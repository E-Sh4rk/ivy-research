module WPR

    // Thanks to https://github.com/Microsoft/ivy/blob/master/doc/decidability.md

    open MinimalAST

    /// <summary>
    /// Represents a value/formula that can easily be passed to the Z3 solver.
    /// </summary>
    type Z3Value =
        | Z3Const of ConstValue
        | Z3Var of string
        | Z3Fun of string * List<Z3Value>
        | Z3Equal of Z3Value * Z3Value
        | Z3Or of Z3Value * Z3Value
        | Z3And of Z3Value * Z3Value
        | Z3Imply of Z3Value * Z3Value
        | Z3Not of Z3Value
        | Z3IfElse of Z3Value * Z3Value * Z3Value
        | Z3Forall of VarDecl * Z3Value
        | Z3Exists of VarDecl * Z3Value
        | Z3Hole // Used for contexts

    /// <summary>
    /// Represents a tuple (c,v) where 'c' is a context (a Z3Value containing a Z3Hole) and 'v' a value that can be used inside the context 'c'.
    /// </summary>
    type ValueContext = Z3Value * Z3Value

    /// <summary>
    /// Yet another AST for representing a statement, this one is convenient for computing weakest preconditions.
    /// </summary>
    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * ValueContext
        | VarAssignAction of string * string * List<ValueContext>
        | FunAssign of string * List<VarDecl> * ValueContext
        | Parallel of Statement * Statement
        | Assume of ValueContext
        | Abort

    // Utility functions on types

    let replace_holes_with repl v =
        let rec aux v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str -> Z3Var str
            | Z3Fun (str, vs) -> Z3Fun (str, List.map aux vs)
            | Z3Equal (v1, v2) -> Z3Equal (aux v1, aux v2)
            | Z3Or (v1, v2) -> Z3Or (aux v1, aux v2)
            | Z3And (v1, v2) -> Z3And (aux v1, aux v2)
            | Z3Imply (v1, v2) -> Z3Imply (aux v1, aux v2)
            | Z3Not v -> Z3Not (aux v)
            | Z3IfElse (c,i,e) -> Z3IfElse (aux c, aux i, aux e)
            | Z3Forall (d, v) -> Z3Forall (d, aux v)
            | Z3Exists (d, v) -> Z3Exists (d, aux v)
            | Z3Hole -> repl
        aux v
    
    let rec free_vars_of_value v =
        match v with
        | Z3Const _ -> Set.empty
        | Z3Var str -> Set.singleton str
        | Z3Fun (_, vs) -> Set.unionMany (List.map free_vars_of_value vs)
        | Z3Equal (v1, v2) | Z3Or (v1, v2) | Z3And (v1, v2) | Z3Imply (v1, v2)
            -> Set.union (free_vars_of_value v1) (free_vars_of_value v2)
        | Z3Not v -> free_vars_of_value v
        | Z3IfElse (f, v1, v2) ->
            Set.unionMany [free_vars_of_value f ; free_vars_of_value v1 ; free_vars_of_value v2]
        | Z3Forall (d, v) | Z3Exists (d, v) -> 
            let fv = free_vars_of_value v
            Set.remove d.Name fv
        | Z3Hole -> Set.empty

    let rec const_int_in_value v =
        match v with
        | Z3Const (AST.ConstInt (t,i)) -> Set.singleton (t,i)
        | Z3Const _ -> Set.empty
        | Z3Var _ -> Set.empty
        | Z3Fun (_, vs) -> Set.unionMany (List.map const_int_in_value vs)
        | Z3Equal (v1, v2) | Z3Or (v1, v2) | Z3And (v1, v2) | Z3Imply (v1, v2)
            -> Set.union (const_int_in_value v1) (const_int_in_value v2)
        | Z3Not v -> const_int_in_value v
        | Z3IfElse (f, v1, v2) ->
            Set.unionMany [const_int_in_value f ; const_int_in_value v1 ; const_int_in_value v2]
        | Z3Forall (_, v) | Z3Exists (_, v) -> const_int_in_value v
        | Z3Hole -> Set.empty

    let rec funs_in_value v =
        match v with
        | Z3Const _ -> Set.empty
        | Z3Var _ -> Set.empty
        | Z3Fun (str, vs) -> Set.unionMany ((Set.singleton str)::(List.map funs_in_value vs))
        | Z3Equal (v1, v2) | Z3Or (v1, v2) | Z3And (v1, v2) | Z3Imply (v1, v2)
            -> Set.union (funs_in_value v1) (funs_in_value v2)
        | Z3Not v -> funs_in_value v
        | Z3IfElse (f, v1, v2) ->
            Set.unionMany [funs_in_value f ; funs_in_value v1 ; funs_in_value v2]
        | Z3Forall (_, v) | Z3Exists (_, v) -> funs_in_value v
        | Z3Hole -> Set.empty

    // Conversion tools

    let next_var = ref 0

    let reinit_tmp_vars () =
        next_var := 0

    let unique_name name =
        let id = !next_var
        next_var := (!next_var) + 1
        AST.make_name_unique name id

    // Utility functions

    let conjunction_of fs =
        match fs with
        | [] -> Z3Const (AST.ConstBool true)
        | h::tl -> List.fold (fun acc f -> Z3And (acc, f)) h tl

    let disjunction_of fs =
        match fs with
        | [] -> Z3Const (AST.ConstBool false)
        | h::tl -> List.fold (fun acc f -> Z3Or (acc, f)) h tl

    let rename_value renaming v =
        let dico = Map.map (fun _ str -> ValueVar str) renaming
        map_vars_in_value v dico
    let rename_var renaming str =
        if Map.containsKey str renaming
        then Map.find str renaming else str

    let fail_if_ctx_depends_on ctx dependances =
        if Set.isEmpty (Set.intersect (free_vars_of_value ctx) dependances)
        then ()
        else failwith "Can't convert value to a FO Z3 value..."

    let rec map_vars_in_z3value v dico =
        match v with
        | Z3Const c -> Z3Const c
        | Z3Var str ->
            if Map.containsKey str dico
            then Map.find str dico
            else Z3Var str
        | Z3Fun (str, vs) ->
            Z3Fun (str, List.map (fun v -> map_vars_in_z3value v dico) vs)
        | Z3Equal (v1, v2) ->
            Z3Equal (map_vars_in_z3value v1 dico, map_vars_in_z3value v2 dico)
        | Z3Or (v1, v2) ->
            Z3Or (map_vars_in_z3value v1 dico, map_vars_in_z3value v2 dico)
        | Z3And (v1, v2) ->
            Z3And (map_vars_in_z3value v1 dico, map_vars_in_z3value v2 dico)
        | Z3Imply (v1, v2) ->
            Z3Imply (map_vars_in_z3value v1 dico, map_vars_in_z3value v2 dico)
        | Z3Not v ->
            Z3Not (map_vars_in_z3value v dico)
        | Z3IfElse (f, v1, v2) ->
            Z3IfElse (map_vars_in_z3value f dico, map_vars_in_z3value v1 dico, map_vars_in_z3value v2 dico)
        | Z3Forall (d,v) ->
            let dico = Map.remove d.Name dico
            Z3Forall (d, map_vars_in_z3value v dico)
        | Z3Exists (d,v) ->
            let dico = Map.remove d.Name dico
            Z3Exists (d, map_vars_in_z3value v dico)
        | Z3Hole -> Z3Hole
    
    let simplify_z3_value f =
        let rec aux f =
            match f with
            // Possible simplifications
            | Z3Not (Z3Const (AST.ConstBool true)) -> Z3Const (AST.ConstBool false)
            | Z3Not (Z3Const (AST.ConstBool false)) -> Z3Const (AST.ConstBool true)
            | Z3Or (Z3Const (AST.ConstBool true), _) | Z3Or (_, Z3Const (AST.ConstBool true)) -> Z3Const (AST.ConstBool true)
            | Z3Or (Z3Const (AST.ConstBool false), v) | Z3Or (v, Z3Const (AST.ConstBool false)) -> aux v
            | Z3And (Z3Const (AST.ConstBool false), _) | Z3And (_, Z3Const (AST.ConstBool false)) -> Z3Const (AST.ConstBool false)
            | Z3And (Z3Const (AST.ConstBool true), v) | Z3Or (v, Z3Const (AST.ConstBool true)) -> aux v
            | Z3Imply (Z3Const (AST.ConstBool true), v) -> aux v
            | Z3Imply (Z3Const (AST.ConstBool false), _) | Z3Imply (_, Z3Const (AST.ConstBool true)) -> Z3Const (AST.ConstBool true)
            | Z3Imply (v, Z3Const (AST.ConstBool false)) -> aux (Z3Not v)
            | Z3Not (Z3Not v) -> aux v
            | Z3Not (Z3And (v1, v2)) -> aux (Z3Or (Z3Not v1, Z3Not v2))
            | Z3Not (Z3Or (v1, v2)) -> aux (Z3And (Z3Not v1, Z3Not v2))
            | Z3Not (Z3Imply (v1, v2)) -> aux (Z3And (v1, Z3Not v2))
            | Z3Not (Z3Forall (d,f)) -> aux (Z3Exists (d, Z3Not f))
            | Z3Not (Z3Exists (d,f)) -> aux (Z3Forall (d, Z3Not f))
            | Z3Or (Z3Not v1, v2) -> aux (Z3Imply (v1, v2))
            // Normal cases
            | Z3Const c -> Z3Const c
            | Z3Var str -> Z3Var str
            | Z3Fun (str,vs) -> Z3Fun (str, List.map aux vs)
            | Z3Equal (v1,v2) -> Z3Equal (aux v1, aux v2)
            | Z3Or (v1, v2) -> Z3Or (aux v1, aux v2)
            | Z3And (v1, v2) -> Z3And (aux v1, aux v2)
            | Z3Imply (v1, v2) -> Z3Imply (aux v1, aux v2)
            | Z3Not v -> Z3Not (aux v)
            | Z3IfElse (f, v1, v2) -> Z3IfElse (aux f, aux v1, aux v2)
            | Z3Forall (d, v) -> Z3Forall (d, aux v)
            | Z3Exists (d, v) -> Z3Exists (d, aux v)
            | Z3Hole -> Z3Hole
        aux f

    /// <summary>
    /// Converts a MinimalAST value into a Z3Value. Each local variable in the value is also renamed in order to be unique.
    /// </summary>
    /// <param name="m">The module from which the value is issued</param>
    /// <param name="v">The value to convert</param>
    let minimal_val2z3_val (m:ModuleDecl<'a,'b>) v =
        let rec aux v =
            match v with
            | ValueConst c -> (Z3Hole, Z3Const c)
            | ValueStar t ->
                printfn "Warning: Non-deterministic operation detected (ValueStar)."
                let name = unique_name (AST.local_name "NDS")
                let d = AST.default_var_decl name t
                let ctx = Z3Forall (d, Z3Hole)
                (ctx, Z3Var name)
            | ValueVar str -> (Z3Hole, Z3Var str)
            | ValueFun (str, vs) ->
                let (ctxs, vs) = List.unzip (List.map aux vs)
                let ctx = List.fold replace_holes_with Z3Hole (List.rev ctxs)
                (ctx, Z3Fun (str, vs))
            | ValueEqual (v1, v2) ->
                let (ctx1, v1) = aux v1
                let (ctx2, v2) = aux v2
                let ctx = replace_holes_with ctx2 ctx1
                (ctx, Z3Equal (v1, v2))
            | ValueOr (v1, v2) ->
                let (ctx1, v1) = aux v1
                let (ctx2, v2) = aux v2
                let ctx = replace_holes_with ctx2 ctx1
                (ctx, Z3Or (v1, v2))
            | ValueNot v ->
                let (ctx, v) = aux v
                (ctx, Z3Not v)
            | ValueSomeElse (d, v1, v2) ->
                printfn "Warning: Non-deterministic operation detected (ValueSomeElse)."
                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming = Map.add d.Name new_d.Name Map.empty
                let v1 = rename_value renaming v1

                let (ctx1, v1) = aux v1
                fail_if_ctx_depends_on ctx1 (Set.singleton new_d.Name)
                let (ctx2, v2) = aux v2

                let condition = Z3Forall (new_d, Z3Imply (Z3Or (v1, Z3And (Z3Not (Z3Exists (new_d, v1)), Z3Equal(Z3Var new_d.Name, v2))), Z3Hole))
                let ctx = replace_holes_with condition ctx2
                let ctx = replace_holes_with ctx ctx1
                let v = Z3Var new_d.Name
                (ctx, v)
            | ValueIfElse (c,i,e) ->
                let (ctx1, c) = aux c
                let (ctx2, i) = aux i
                let (ctx3, e) = aux e
                let ctx = List.fold replace_holes_with Z3Hole [ctx3;ctx2;ctx1]
                (ctx, Z3IfElse (c,i,e))
            | ValueForall (d, v) ->
                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming = Map.add d.Name new_d.Name Map.empty
                let v = rename_value renaming v

                let (ctx, v) = aux v
                fail_if_ctx_depends_on ctx (Set.singleton new_d.Name)
                let v = Z3Forall (new_d, v)
                (ctx, v)
            | ValueInterpreted (str, _) ->
                aux (ValueStar (MinimalAST.find_interpreted_action m str).Output)
        let (ctx, v) = aux v
        (simplify_z3_value ctx, simplify_z3_value v)

    exception ValueNotAllowed

    /// <summary>
    /// Combines a ValueContext into a formula (the value is directly injected in the context).
    /// </summary>
    /// <param name="ctx">The context</param>
    /// <param name="v">The value (must be a formula, otherwise this operation makes no sense)</param>
    /// <param name="allow_contexts">If false, ctx must be an empty context</param>
    let z3ctx2deterministic_formula (ctx,v) allow_contexts =
        if allow_contexts
        then replace_holes_with v ctx
        else if ctx <> Z3Hole
        then raise ValueNotAllowed
        else v

    /// <summary>
    /// Converts a MinimalAST statement into a WPR statement. Also rename variables according to the given mapping. Each local variable is also renamed in order to be unique.
    /// </summary>
    /// <param name="m">The module from which is issued the statement.</param>
    /// <param name="renaming">A mapping for the variables that we want to rename.</param>
    /// <param name="st">The statement to convert.</param>
    let minimal_stat2wpr_stat<'a,'b> (m:ModuleDecl<'a,'b>) renaming st =
        let minimal_val2z3_val = minimal_val2z3_val m

        let packIfNecessary sts =
            if List.length sts = 1 then List.head sts
            else NewBlock ([],sts)

        let rec aux renaming st =
            match st with
            | MinimalAST.AtomicGroup sts -> List.concat (List.map (aux renaming) sts)
            | MinimalAST.NewBlock (decls, sts) ->
                let new_decls = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) decls
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming decls new_decls
                [NewBlock (new_decls, List.concat (List.map (aux renaming) sts))]
            | MinimalAST.VarAssign (str, v) ->
                let v = rename_value renaming v
                [VarAssign (rename_var renaming str, minimal_val2z3_val v)]
            | MinimalAST.VarAssignAction (str, action, vs) ->
                let vs = List.map (rename_value renaming) vs
                [VarAssignAction (rename_var renaming str, action, List.map minimal_val2z3_val vs)]
            | MinimalAST.FunAssign (str, ds, v) ->
                let new_ds = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) ds
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming ds new_ds
                let v = rename_value renaming v
                [FunAssign (str,new_ds,minimal_val2z3_val v)]
            | MinimalAST.IfElse (vcond, sif, selse) ->
                let vcond = rename_value renaming vcond
                let sif = (Assume (minimal_val2z3_val vcond))::(aux renaming sif)
                let sif = packIfNecessary sif
                let selse = (Assume (minimal_val2z3_val (ValueNot vcond)))::(aux renaming selse)
                let selse = packIfNecessary selse
                [Parallel (sif, selse)]
            | MinimalAST.IfSomeElse (d, vcond, sif, selse) ->
                let qvar = AST.default_var_decl (unique_name (AST.local_name "ISE")) d.Type
                let renaming_qvar = Map.add d.Name qvar.Name renaming
                let vcond_qvar = rename_value renaming_qvar vcond

                let selse = aux renaming selse
                let selse = (Assume (minimal_val2z3_val (ValueForall (qvar, ValueNot vcond_qvar))))::selse
                let selse = packIfNecessary selse

                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming_d = Map.add d.Name new_d.Name renaming
                let vcond_new_d = rename_value renaming_d vcond
                
                let sif = aux renaming_d sif
                let sif_d_assign = minimal_val2z3_val (ValueSomeElse (qvar, vcond_qvar, ValueStar d.Type))
                let sif = [NewBlock ([new_d], (VarAssign (new_d.Name, sif_d_assign))::sif)]
                let sif = (Assume (minimal_val2z3_val vcond_new_d))::sif
                let sif = packIfNecessary sif
                
                [Parallel (sif, selse)]
            | MinimalAST.Assert v ->
                let v = rename_value renaming v
                let sassert = [Assume (minimal_val2z3_val (ValueNot v));Abort]
                let sassert = packIfNecessary sassert
                [Parallel (sassert,NewBlock([],[]))]
            | MinimalAST.Assume v ->
                let v = rename_value renaming v
                [Assume (minimal_val2z3_val v)]
        packIfNecessary (aux renaming st)

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }

    /// <summary>
    /// Converts a MinimalAST ActionDecl into a WPR ActionDecl.
    /// </summary>
    /// <param name="m">The module from which is issued the action</param>
    /// <param name="action">The action to convert</param>
    /// <param name="rename_args">Whether or not the arguments of the action should be renamed in order to be unique</param>
    let minimal_action2wpr_action<'a,'b> (m:ModuleDecl<'a,'b>) action rename_args =
        let action = find_action m action

        let rename_decl renaming (decl:VarDecl) =
            if Map.containsKey decl.Name renaming
            then { decl with Name = Map.find decl.Name renaming } else decl

        let renaming =
            if rename_args
            then List.fold (fun acc (d:VarDecl) -> Map.add d.Name (unique_name d.Name) acc) Map.empty (action.Output::action.Args)
            else Map.empty
        let args = List.map (rename_decl renaming) action.Args
        let output = rename_decl renaming action.Output
        { Name = action.Name ; Args = args ; Output = output ; Content = minimal_stat2wpr_stat m renaming action.Content }

    // WPR

    let replace_vars dico v =
        let rec aux dico v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str ->
                if Map.containsKey str dico
                then Map.find str dico
                else Z3Var str
            | Z3Fun (str, vs) ->
                Z3Fun (str, List.map (aux dico) vs)
            | Z3Equal (v1, v2) ->
                Z3Equal (aux dico v1, aux dico v2)
            | Z3Or (v1, v2) ->
                Z3Or (aux dico v1, aux dico v2)
            | Z3And (v1, v2) ->
                Z3And (aux dico v1, aux dico v2)
            | Z3Imply (v1, v2) ->
                Z3Imply (aux dico v1, aux dico v2)
            | Z3Not v ->
                Z3Not (aux dico v)
            | Z3IfElse (f, v1, v2) ->
                Z3IfElse (aux dico f, aux dico v1, aux dico v2)
            | Z3Forall (d,v) ->
                let dico = Map.remove d.Name dico
                Z3Forall (d, aux dico v)
            | Z3Exists (d,v) ->
                 let dico = Map.remove d.Name dico
                 Z3Exists (d, aux dico v)
            | Z3Hole -> Z3Hole
        aux dico v

    let replace_var str repl v =
        replace_vars (Map.add str repl Map.empty) v

    let replace_fun decls str repl v =
        let rec aux v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str -> Z3Var str
            | Z3Fun (str', vs) ->
                if str' = str
                then
                    let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty decls vs
                    replace_vars dico repl
                else
                    Z3Fun (str', List.map aux vs)
            | Z3Equal (v1, v2) ->
                Z3Equal (aux v1, aux v2)
            | Z3Or (v1, v2) ->
                Z3Or (aux v1, aux v2)
            | Z3And (v1, v2) ->
                Z3And (aux v1, aux v2)
            | Z3Imply (v1, v2) ->
                Z3Imply (aux v1, aux v2)
            | Z3Not v ->
                Z3Not (aux v)
            | Z3IfElse (f, v1, v2) ->
                Z3IfElse (aux f, aux v1, aux v2)
            | Z3Forall (d,v) -> Z3Forall (d, aux v)
            | Z3Exists (d,v) -> Z3Exists (d, aux v)
            | Z3Hole -> Z3Hole
        aux v

    /// <summary>
    /// Converts a list of MinimalAST values into a list of Z3Value.
    /// The values must not need any context in order to be translated to Z3Value: they must be fully deterministic.
    /// </summary>
    /// <param name="m">The module from which the values are issued</param>
    /// <param name="conj">The list of values to convert</param>
    let conjectures_to_z3values<'a,'b> (m:ModuleDecl<'a,'b>) conj =
        List.fold
            (
                fun acc v ->
                    try
                        (z3ctx2deterministic_formula (minimal_val2z3_val m v) false)::acc
                    with :? ValueNotAllowed -> printfn "Illegal axiom/conjecture ignored..." ; acc
            ) [] conj

    /// <summary>
    /// Computes the weakest precondition of a formula before a statement.
    /// </summary>
    /// <param name="m">The module from which are issued the statement</param>
    /// <param name="f">The formula</param>
    /// <param name="st">The statement</param>
    let weakest_precondition<'a,'b> (m:ModuleDecl<'a,'b>) f st =

        let axioms = conjectures_to_z3values m (MinimalAST.axioms_decls_to_formulas m.Axioms)

        let filter_axioms str =
            let is_necessary axiom =
                Set.contains str (funs_in_value axiom)
            List.filter is_necessary axioms

        let add_necessary_axioms str f = // Mutations are assumed to not break axioms (when non-deterministic)
            // That's why we need to assume axioms when non-deterministic values are assigned to global vars/funs
            let axioms = filter_axioms str
            if List.isEmpty axioms
            then f
            else Z3Imply(conjunction_of axioms, f)
        let rec aux f st =
            match st with
            | NewBlock (ds, sts) ->
                let names = Set.ofList (List.map (fun (v:VarDecl) -> v.Name) ds)
                let fv = free_vars_of_value f
                assert Set.isEmpty (Set.intersect fv names) // New local vars should have unique names
                let f = List.fold aux f (List.rev sts)
                let fv = free_vars_of_value f
                assert Set.isEmpty (Set.intersect fv names) // Used local vars should have been assigned!
                f
            | VarAssign (str, (ctx, v)) ->
                // Note: No need to assume axioms here because these vars are local (so no axiom is involving them)
                let f = replace_var str v f
                replace_holes_with f ctx
            | VarAssignAction (str, action, vs) ->
                let action = minimal_action2wpr_action m action true
                // Note: No need to assume axioms here because these vars are local (so no axiom is involving them)
                let f = replace_var str (Z3Var action.Output.Name) f
                let f = aux f action.Content
                assert not (Set.contains action.Output.Name (free_vars_of_value f)) // Return var should have been assigned

                let assign_arg f (d:VarDecl) (ctx, v) =
                    // Note: No need to assume axioms here because these vars are local (so no axiom is involving them)
                    let f = replace_var d.Name v f
                    replace_holes_with f ctx

                List.fold2 assign_arg f (List.rev action.Args) (List.rev vs)
            | FunAssign (str, ds, (ctx,v)) ->
                let f = add_necessary_axioms str f
                let f = replace_fun ds str v f
                replace_holes_with f ctx
            | Parallel (st1, st2) ->
                let f1 = aux f st1
                let f2 = aux f st2
                Z3And (f1, f2)
            | Assume (ctx, v) ->
                let f = Z3Imply (v, f)
                replace_holes_with f ctx
            | Abort -> Z3Const (AST.ConstBool false)
        simplify_z3_value (aux f st)

    /// <summary>
    /// Computes the weakest precondition of a formula before an action.
    /// </summary>
    /// <param name="m">The module from which the action is issued</param>
    /// <param name="f">The formula</param>
    /// <param name="action">The action name</param>
    /// <param name="negate">Indicates whether the result must be negated or not. If set to true, the arguments will not be renamed nor quantified in the formula so their value can be collected.</param>
    let wpr_for_action<'a,'b> (m:ModuleDecl<'a,'b>) f action negate =
        let action = minimal_action2wpr_action m action (not negate)
        let res = weakest_precondition m f action.Content
        if not negate
        then
            List.fold (fun acc (d:VarDecl) -> Z3Forall (d,acc)) res action.Args
        else Z3Not res
