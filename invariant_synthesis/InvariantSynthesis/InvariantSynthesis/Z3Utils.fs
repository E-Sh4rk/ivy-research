module Z3Utils

    open MinimalAST
    open WPR
    open Microsoft.Z3

    let sort_of_type (ctx:Context) sorts t : Sort =
        match t with
        | AST.Void -> failwith "Void type has no sort!"
        | AST.Bool -> ctx.BoolSort :> Sort
        | AST.Uninterpreted str -> Map.find str sorts :> Sort
        | AST.Enumerated str -> Map.find str sorts :> Sort

    /// <summary>
    /// A Z3 global context. Defines global elements in a module and allow us to find them easily.
    /// </summary>
    [<NoComparison>]
    type ModuleContext =
        {
            Context: Context ;
            Sorts: Map<string, Sort> ;
            Funs: Map<string, FuncDecl>
        }

    /// <summary>
    /// Builds a global context corresponding to the given module.
    /// </summary>
    /// <param name="m">The module</param>
    let build_context<'a,'b> (m:AST.ModuleDecl<'a,'b>) =
        let ctx = new Context()
        let sorts = ref Map.empty 
        let funs = ref Map.empty

        for d in m.Types do
            match d.Infos with
            | AST.UninterpretedTypeDecl -> sorts := Map.add d.Name (ctx.MkUninterpretedSort(d.Name) :> Sort) (!sorts)
            | AST.EnumeratedTypeDecl strs -> sorts := Map.add d.Name (ctx.MkEnumSort(d.Name, List.toArray strs) :> Sort) (!sorts)
        for d in m.Funs do
            let domain = List.map (sort_of_type ctx (!sorts)) d.Input
            let range = sort_of_type ctx (!sorts) d.Output
            if List.length domain = 0
            then funs := Map.add d.Name (ctx.MkConstDecl(d.Name, range)) (!funs)
            else funs := Map.add d.Name (ctx.MkFuncDecl(d.Name,Array.ofList domain,range)) (!funs)

        { Context = ctx ; Sorts = !sorts ; Funs = !funs }

    let name_of_constint (t,i) =
        sprintf "%s%c%i" t AST.name_separator i

    /// <summary>
    /// Aggregates new data about local variables and concrete values in a value.
    /// </summary>
    /// <param name="args">The arguments of the action containing the value (if any)</param>
    /// <param name="ctx">The global context</param>
    /// <param name="lenum">Data about local enumerations</param>
    /// <param name="v">The value to analyze</param>
    /// <param name="lvars">Data about local variables</param>
    /// <param name="cv_assoc">Data about concrete values</param>
    let declare_lvars_ext<'a,'b> args (ctx:ModuleContext) lenum v (lvars,cv_assoc) =
        
        let add_civ (lvars,cv_assoc) (t,i) =
            let name = name_of_constint (t,i)
            let sort = Map.find t ctx.Sorts
            if not (Map.containsKey name lvars)
            then
                let lvars = Map.add name (ctx.Context.MkConstDecl(name,sort)) lvars
                let cv_assoc = (name, (t,i))::cv_assoc
                (lvars,cv_assoc)
            else (lvars,cv_assoc)

        let add_fv acc name =
            if Map.containsKey name acc
            then acc
            else
                let decl = List.find (fun (v:VarDecl) -> v.Name = name) args
                let sort = sort_of_type ctx.Context (Helper.merge_maps ctx.Sorts lenum) decl.Type
                Map.add name (ctx.Context.MkConstDecl(name,sort)) acc
        
        let (lvars,cv_assoc) = Set.fold add_civ (lvars,cv_assoc) (const_int_in_value v)
        let lvars = Set.fold add_fv lvars (free_vars_of_value v)
        (lvars,cv_assoc)

    /// <summary>
    /// Retrieves new data about local variables and concrete values in a value.
    /// </summary>
    /// <param name="args">The arguments of the action containing the value (if any)</param>
    /// <param name="ctx">The global context</param>
    /// <param name="lenum">Data about local enumerations</param>
    /// <param name="v">The value to analyze</param>
    let declare_lvars<'a,'b> args (ctx:ModuleContext) lenum v =
        declare_lvars_ext args ctx lenum v (Map.empty, [])

    /// <summary>
    /// Aggregates data about a new local enumeration.
    /// </summary>
    /// <param name="str">The name of the enumeration</param>
    /// <param name="vs">The possible values</param>
    /// <param name="ctx">The global context</param>
    /// <param name="lenums">Data about other local enumerations</param>
    let declare_new_enumerated_type_ext<'a,'b> (str:string, vs) (ctx:ModuleContext) lenums =
        let sort = ctx.Context.MkEnumSort (str, List.toArray vs) :> Sort
        Map.add str sort lenums

    let expr_of_cv (ctx:ModuleContext) lvars (lenums:Map<string,Sort>) cv =
        match cv with
        | AST.ConstVoid -> failwith "Void value is not a valid expression!"
        | AST.ConstBool true -> ctx.Context.MkTrue() :> Expr
        | AST.ConstBool false -> ctx.Context.MkFalse() :> Expr
        | AST.ConstInt (t, i) ->
            let name = name_of_constint (t,i)
            let fd = Map.find name lvars
            ctx.Context.MkConst(fd)
        | AST.ConstEnumerated (t, str) ->
            let esort =
                if Map.containsKey t lenums
                then
                    Map.find t lenums :?> EnumSort
                else
                    Map.find t ctx.Sorts :?> EnumSort
            ctx.Context.MkConst (Array.find (fun (fd:FuncDecl) -> fd.Name.ToString() = str) esort.ConstDecls)

    /// <summary>
    /// Builds a Z3 Expression from a Z3Value.
    /// </summary>
    /// <param name="ctx">The global context</param>
    /// <param name="lvars">Data about local vars</param>
    /// <param name="lenums">Data about local enumerations</param>
    /// <param name="v">The value</param>
    let build_value<'a,'b> (ctx:ModuleContext) lvars lenums (v:Z3Value) =

        let rec aux qvars v =
            match v with
            | Z3Const cv -> expr_of_cv ctx lvars lenums cv
            | Z3Var str ->
                if Map.containsKey str qvars
                then Map.find str qvars
                else ctx.Context.MkConst (Map.find str lvars)
            | Z3Fun (str, vs) ->
                let exprs = List.map (aux qvars) vs
                let fd = Map.find str ctx.Funs
                ctx.Context.MkApp (fd, exprs)
            | Z3Equal (v1, v2) ->
                let e1 = aux qvars v1
                let e2 = aux qvars v2
                ctx.Context.MkEq (e1, e2) :> Expr
            | Z3Or (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkOr ([e1;e2]) :> Expr
            | Z3And (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkAnd ([e1;e2]) :> Expr
            | Z3Imply (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkImplies (e1,e2) :> Expr
            | Z3Not v ->
                let e = aux qvars v :?> BoolExpr
                ctx.Context.MkNot (e) :> Expr
            | Z3IfElse (vc, vif, velse) ->
                let ec = aux qvars vc :?> BoolExpr
                let eif = aux qvars vif
                let eelse = aux qvars velse
                ctx.Context.MkITE (ec, eif, eelse)
            | Z3Forall (d, v) ->
                let cst = ctx.Context.MkFreshConst (d.Name, sort_of_type ctx.Context ctx.Sorts d.Type)
                let qvars = Map.add d.Name cst qvars
                let e = aux qvars v
                ctx.Context.MkForall ([|cst|], e) :> Expr
            | Z3Exists (d, v) ->
                let cst = ctx.Context.MkFreshConst (d.Name, sort_of_type ctx.Context ctx.Sorts d.Type)
                let qvars = Map.add d.Name cst qvars
                let e = aux qvars v
                ctx.Context.MkExists ([|cst|], e) :> Expr
            | Z3Hole -> failwith "Can't convert a context to a Z3 formula!"
        aux Map.empty v

    [<NoComparison>]
    type SolverResult = UNSAT | UNKNOWN | SAT of Model

    /// <summary>
    /// Checks whether a Z3 expression is satisfiable or not.
    /// </summary>
    /// <param name="ctx">The global context</param>
    /// <param name="e">The expression</param>
    /// <param name="timeout">Timeout</param>
    let check (ctx:ModuleContext) (e:Expr) (timeout:int) =
        let s = ctx.Context.MkSolver()
        s.Set ("timeout", uint32(timeout))
        s.Assert ([|e:?> BoolExpr|])
        match s.Check () with
        | Status.UNKNOWN ->
            printfn "ERROR: Satisfiability can't be decided!"
            UNKNOWN
        | Status.UNSATISFIABLE ->
            UNSAT
        | Status.SATISFIABLE ->
            SAT s.Model
        | _ -> failwith "Solver returned an unknown status..."

    let is_true (e:Expr) =
        e.FuncDecl.Name.ToString() = "true"

    let is_false (e:Expr) =
        e.FuncDecl.Name.ToString() = "false"

    /// <summary>
    /// Checks whether a disjunction of Z3 expressions is satisfiable. If satisfiable, also returns the name of a satisfiable Z3 expression.
    /// </summary>
    /// <param name="ctx">The global context</param>
    /// <param name="e">Some axioms that must be satisfied in every expression</param>
    /// <param name="es">The list of named Z3 expressions</param>
    /// <param name="timeout">Timeout</param>
    let check_disjunction (ctx:ModuleContext) (e:Expr) (es:List<string*Expr>) (timeout:int) =

        let s = ctx.Context.MkSolver()
        s.Set ("timeout", uint32(timeout))
        s.Assert ([|e:?> BoolExpr|])
        s.Push ()

        let rec treat_exprs unknown (es:List<string*Expr>) =
            match es with
            | [] -> if unknown then (UNKNOWN, None) else (UNSAT, None)
            | (str,e)::es ->
                s.Assert ([|e :?> BoolExpr|])
                match s.Check () with
                | Status.UNKNOWN ->
                    printfn "ERROR: Satisfiability can't be decided!"
                    s.Pop (uint32(1))
                    s.Push ()
                    treat_exprs true es
                | Status.UNSATISFIABLE ->
                    s.Pop (uint32(1))
                    s.Push ()
                    treat_exprs false es
                | Status.SATISFIABLE ->
                    (SAT s.Model, Some str)
                | _ -> failwith "Solver returned an unknown status..."

        treat_exprs false es
        // TODO: Eventually, choose the one with the smallest model.
       
    /// <summary>
    /// Checks whether a conjunction of Z3 expressions is satisfiable. If not, also returns a minimal unSAT core.
    /// NOTE: With the version of Z3 currently used, the core returned is not minimal. Please use check_conjunction_fix instead.
    /// </summary>
    /// <param name="ctx">The global context</param>
    /// <param name="e">Some axioms that must be satisfied</param>
    /// <param name="es">The list of named Z3 expressions</param>
    /// <param name="timeout">Timeout</param>
    let check_conjunction (ctx:ModuleContext) (e:Expr) (es:List<string*Expr>) (timeout:int) =
        let normalize_name str =
            AST.generated_name (sprintf "__unsatcore__%s" str)

        let s = ctx.Context.MkSolver()
        s.Set ("timeout", uint32(timeout))
        s.Set ("unsat_core", true)
        s.Set ("core.minimize", true)
        s.Set ("core.validate", true)
        s.Assert ([|e:?> BoolExpr|])
        let assert_and_track (str, e:Expr) =
            let p = ctx.Context.MkBoolConst(normalize_name str);
            s.AssertAndTrack (e :?> BoolExpr, p)
        List.iter assert_and_track es
       
        match s.Check () with
        | Status.UNKNOWN ->
            printfn "ERROR: Satisfiability can't be decided!"
            (UNKNOWN, [])
        | Status.UNSATISFIABLE ->
            let core = List.ofArray s.UnsatCore
            let core = List.map (fun (e:BoolExpr) -> e.FuncDecl.Name.ToString()) core
            let res = List.map (fun (str,_) -> str) es
            let res = List.filter (fun str -> List.contains (normalize_name str) core) res
            (UNSAT, res)
        | Status.SATISFIABLE ->
            (SAT s.Model, [])
        | _ -> failwith "Solver returned an unknown status..."

    // TODO: Remove that function when a future (working) version of Z3 will take into account 'core.minimize'
    /// <summary>
    /// See description of check_conjunction.
    /// </summary>
    let check_conjunction_fix (ctx:ModuleContext) (e:Expr) (es:List<string*Expr>) (timeout:int) =
        
        match check_conjunction ctx e es timeout with
        | (UNSAT, res) ->
            // We minimize by hand...
            let es = List.filter (fun (str,_) -> List.contains str res) es
            let try_remove_e es (str,_) =
                let es' = List.filter (fun (str',_) -> str'<>str) es
                if List.length es' = List.length es
                then es
                else
                    match check_conjunction ctx e es' timeout with
                    | (UNSAT, res) ->
                        List.filter (fun (str,_) -> List.contains str res) es'
                    | _ -> es
            let es = List.fold try_remove_e es es
            (UNSAT, List.map (fun (str,_) -> str) es)
        | x -> x

    let cv_of_expr_str (m:AST.ModuleDecl<'a,'b>) const_cv_map str =
        match str with
        | "true" -> AST.ConstBool true
        | "false" -> AST.ConstBool false
        | str ->
            if Map.containsKey str const_cv_map
            then AST.ConstInt (Map.find str const_cv_map)
            else
                // Note: local enumerated types are not supported for now
                let etypes = AST.all_enumerated_values m.Types |> Set.toList
                let (t,str) = List.find (fun (_,str') -> str'=str) etypes
                AST.ConstEnumerated (t, str)

    let universe_for_sorts (model:Model) (sorts:List<Sort>) =
        let univs = List.map (fun s -> model.SortUniverse s) sorts
        Helper.all_choices_combination univs

    /// <summary>
    /// Converts a Z3 model into a model.
    /// </summary>
    /// <param name="m">The module from which the Z3 model is issued</param>
    /// <param name="ctx">The global context</param>
    /// <param name="args">The arguments of the main action. All (and only) these local variables will be set in the returned model.</param>
    /// <param name="lvars">Data about local variables of the Z3 model.</param>
    /// <param name="cv_assoc">Data about concrete values in the Z3 model.</param>
    /// <param name="model">The Z3 model.</param>
    let z3model_to_ast_model<'a,'b> (m:AST.ModuleDecl<'a,'b>) (ctx:ModuleContext) args lvars
        cv_assoc (model:Model)
        : (Model.TypeInfos * Model.Environment) =

        let all_decls = model.Decls
        let is_declared (fd:FuncDecl) =
            Array.exists (fun (fd':FuncDecl) -> fd.Name = fd'.Name) all_decls
        let is_declared_sort (s:Sort) =
            Array.exists (fun (s':Sort) -> s.Name = s'.Name) model.Sorts

        // Fix concrete const values
        let treat_concrete const_cv_map (name,cv) =
            let (fd:FuncDecl) = Map.find name lvars
            if is_declared fd
            then
                let (e:Expr) = model.ConstInterp (fd)
                let fname = e.FuncDecl.Name.ToString()
                Map.add fname cv const_cv_map
            else const_cv_map
        let const_cv_map = List.fold treat_concrete Map.empty cv_assoc

        let treat_type const_cv_map (t:TypeDecl) =
            let sort = Map.find t.Name ctx.Sorts
            if is_declared_sort sort then
                let univ = model.SortUniverse (sort)
                let treat_expr const_cv_map (e:Expr) =
                    let rec next_available_i i =
                        match Map.tryFindKey (fun _ (str,j) -> str=t.Name && j=i) const_cv_map with
                        | None -> i
                        | Some _ -> next_available_i (i+1)
                    let name = e.FuncDecl.Name.ToString()
                    if not (Map.containsKey name const_cv_map) then
                        Map.add name (t.Name, next_available_i 0) const_cv_map
                    else
                        const_cv_map
                Array.fold treat_expr const_cv_map univ
            else const_cv_map
        let const_cv_map = List.fold treat_type const_cv_map m.Types

        // Type infos
        let type_infos = List.fold (fun acc (t:TypeDecl) -> Map.add t.Name 0 acc) Map.empty m.Types
        let update_type_infos acc (_,(t,i)) =
            let new_i = max i (Map.find t acc)
            Map.add t new_i acc
        let type_infos = List.fold update_type_infos type_infos (Map.toList const_cv_map)

        // Environment
        let cv_of_expr (e:Expr) =
            cv_of_expr_str m const_cv_map (e.FuncDecl.Name.ToString())

        let treat_var acc (decl:VarDecl) =
            if Map.containsKey decl.Name lvars // For action args, the symbol sometimes does not exists (if useless)
            then
                let fd = Map.find decl.Name lvars
                if is_declared fd
                then
                    let expr = model.ConstInterp (fd)
                    let cv = cv_of_expr expr
                    Map.add decl.Name cv acc
                else
                    Map.add decl.Name (AST.type_default_value m.Types decl.Type) acc
            else
                Map.add decl.Name (AST.type_default_value m.Types decl.Type) acc

        let vars_env = List.fold treat_var Map.empty args

        let treat_fun acc (d:FunDecl) =
            // Default vals
            let all_entries = Model.all_values_ext m.Types type_infos d.Input
            let default_val = AST.type_default_value m.Types d.Output
            let acc = Seq.fold (fun acc cvs -> Map.add (d.Name, cvs) default_val acc) acc all_entries
            // Z3 Entries
            let fd = Map.find d.Name ctx.Funs
            if is_declared fd
            then
                if List.length d.Input = 0 then
                    let expr = model.ConstInterp (fd)
                    let cv = cv_of_expr expr
                    Map.add (d.Name, []) cv acc
                else
                    let fi = model.FuncInterp (fd)
                    // Else case
                    let expr = fi.Else
                    let treat_else_case_for acc exprs =
                        let exprs = Array.ofList exprs
                        (*let exprs = Array.sub exprs 0 (Array.length expr.Args)
                        let expr = model.Eval(expr.Substitute(expr.Args, exprs),false)*)
                        // Note: Right way to do???
                        let expr = model.Eval(expr.SubstituteVars(exprs),false)
                        let cv = cv_of_expr expr
                        let cvs = List.ofArray (Array.map cv_of_expr exprs)
                        Map.add (d.Name, cvs) cv acc
                    let acc = Seq.fold treat_else_case_for acc (universe_for_sorts model (List.ofArray fd.Domain))
                    // Entries
                    let entries = fi.Entries
                    let aux acc (entry:FuncInterp.Entry) =
                        let input_expr = entry.Args
                        let input = Array.toList (Array.map cv_of_expr input_expr)
                        let expr = entry.Value
                        let cv = cv_of_expr expr
                        Map.add (d.Name, input) cv acc
                    Array.fold aux acc entries
            else acc

        let fun_env = List.fold treat_fun Map.empty m.Funs

        (type_infos, { Model.Environment.f = fun_env ; Model.Environment.v = vars_env })
