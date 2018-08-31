module Formula

    open AST

    type ValueAssociation =
        | VAConst of ConstValue
        | New of string
        | ExistingVar of string
        | ExistingFun of string * List<ConstValue>

    /// <summary>
    /// Returns the invariant corresponding to the given marks.
    /// For convenience, the resulting invariant is not quantified, and the variables that must be quantified are returned separately.
    /// </summary>
    /// <param name="env">The environment (=state) to which the marks refer</param>
    /// <param name="mapping">A partial mapping from the concrete values to the wanted associated elements in the final formula</param>
    /// <param name="generalize">The set of concrete values to quantify on. Other concrete values will be left as is, are will be treated according to the given mapping.</param>
    /// <param name="m">The marks</param>
    let formula_for_marks (env:Model.Environment) (mapping:int*Map<ConstValue,ValueAssociation>) (generalize:Set<ConstValue>) (m:Marking.Marks) =

        let var_name nb =
            let c = (char)(65 + nb)
            c.ToString()

        let add_mapping_for_cv (m:Marking.Marks) (next_var,cmap) cv =
            if Marking.is_model_dependent_value cv then
                if Map.containsKey cv cmap then failwith "Concrete value is already mapped!"
                let rec aux_f mfs =
                    match mfs with
                    | [] -> (next_var+1, Map.add cv (New (var_name next_var)) cmap)
                    | (str,cvs)::mfs ->
                        if AST.value_equal (Map.find (str,cvs) env.f) cv
                        then (next_var, Map.add cv (ExistingFun (str,cvs)) cmap)
                        else aux_f mfs
                let rec aux_v mvs =
                    match mvs with
                    | [] -> aux_f (m.f |> Set.toList)
                    | str::mvs ->
                        if AST.value_equal (Map.find str env.v) cv
                        then (next_var, Map.add cv (ExistingVar str) cmap)
                        else aux_v mvs
                aux_v (m.v |> Set.toList)
            else
                (next_var, Map.add cv (VAConst cv) cmap)

        let cv2association (_,mapping) cv =
            if Map.containsKey cv mapping
            then Map.find cv mapping
            else VAConst cv

        let rec cv2value (i,mapping) cv =
            let a = cv2association (i,mapping) cv
            match a with
            | VAConst cv -> ValueConst cv
            | New str -> ValueVar str
            | ExistingVar str -> ValueVar str
            | ExistingFun (str, cvs) ->
                let vs = List.map (cv2value (i,mapping)) cvs
                ValueFun (str, vs)

        let all_new_vars (_,mapping) : Set<VarDecl> =
            let content = (Map.toList mapping)
            let content = List.filter (fun (_,assoc) -> match assoc with New _ -> true | _ -> false) content
            let vars =
                List.map
                    (fun (cv,assoc) ->
                        match assoc with
                        | New str -> AST.default_var_decl str (type_of_const_value cv)
                        | _ -> failwith "Invalid association."
                    ) content
            Set.ofList vars

        let replace_new_by_existing (i,mapping) =
            let aux _ a =
                match a with
                | VAConst cv -> VAConst cv
                | New str -> ExistingVar str
                | ExistingVar str -> ExistingVar str
                | ExistingFun (str, cvs) -> ExistingFun (str, cvs)
            let mapping = Map.map aux mapping
            (i, mapping)

        let mapping = Set.fold (fun (i,acc) cv -> (i,Map.remove cv acc)) mapping generalize
        let mapping = Set.fold (add_mapping_for_cv m) mapping generalize

        // We remove trivial equalities
        let v' =
            Set.filter
                (
                    fun str ->
                        let cv = Map.find str env.v
                        cv2association mapping cv <> ExistingVar str
                ) m.v
        let m = {m with v=v'}
        let f' =
            Set.filter
                (
                    fun (str, cvs) ->
                        let cv = Map.find (str, cvs) env.f
                        cv2association mapping cv <> ExistingFun (str, cvs)
                ) m.f
        let m = {m with f=f'}
        let d' = Set.filter (fun (cv1,cv2) -> Marking.is_model_dependent_value cv1 || Marking.is_model_dependent_value cv2) m.d
        let m = {m with d=d'}

        // Build constraints
        let constraints_var =
            Set.map
                (
                    fun str ->
                        let cv = Map.find str env.v
                        ValueEqual (ValueVar str, cv2value mapping cv)
                ) m.v
        let constraints_fun =
            Set.map
                (
                    fun (str,cvs) ->
                        let cv = Map.find (str,cvs) env.f
                        let vs = List.map (cv2value mapping) cvs
                        ValueEqual (ValueFun (str, vs), cv2value mapping cv)
                ) m.f
        let constraints = Set.union constraints_var constraints_fun
        let ineq_constraints =
            Set.map
                (
                    fun (cv1,cv2) ->
                        let (cv1,cv2) = Helper.order_tuple (cv1,cv2)
                        let v1 = cv2value mapping cv1
                        let v2 = cv2value mapping cv2
                        ValueNot (ValueEqual (v1, v2))
                ) m.d
        let constraints = Set.union constraints ineq_constraints

        // Buld formula and list of vars to quantify
        let new_vars = all_new_vars mapping
        let f =
            match constraints |> Set.toList with
            | [] -> ValueConst (ConstBool true)
            | h::constraints -> List.fold (fun acc c -> ValueAnd (acc,c)) h constraints

        // Replace new vars by existing var in the mapping
        let mapping = replace_new_by_existing mapping
        (mapping, new_vars, f)

    let concrete_values_of_marks (env:Model.Environment) (m:Marking.Marks) =
        let add_cvs_var acc str =
            Set.add (Map.find str env.v) acc
        let add_cvs_fun acc (str,cvs) =
            let acc = Set.add (Map.find (str,cvs) env.f) acc
            Set.union acc (Set.ofList cvs)
        let add_cvs_diff acc (cv1, cv2) =
            Set.add cv1 (Set.add cv2 acc)
        let res = Set.fold add_cvs_var Set.empty m.v
        let res = Set.fold add_cvs_fun res m.f
        Set.fold add_cvs_diff res m.d

    let generate_semi_generalized_formula (do_not_generalize:Set<ConstValue>) mapping (env:Model.Environment) (m:Marking.Marks) =
        let all_cvs = concrete_values_of_marks env m
        let generalize = Set.difference all_cvs do_not_generalize
        let (_,new_vars,f) = formula_for_marks env mapping generalize m
        Set.fold (fun acc (d:VarDecl) -> ValueExists (d, acc)) f new_vars

    let generate_semi_generalized_formulas (do_not_generalize:Set<ConstValue>) mapping alt_execs =
        let fs = List.map (fun (m,env) -> generate_semi_generalized_formula do_not_generalize mapping env m) alt_execs
        match fs with
        | [] -> ValueConst (ConstBool false)
        | h::fs -> List.fold (fun acc f -> ValueOr (acc,f)) h fs

    let generate_invariant (env:Model.Environment) (common_cvs:Set<ConstValue>) (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) =
        let generalize = Set.union (concrete_values_of_marks env m) common_cvs
        let (mapping, new_vars, f) = formula_for_marks env (0, Map.empty) generalize m
        let f' = generate_semi_generalized_formulas common_cvs mapping alt_exec

        let f = ValueImply (f,f')
        Set.fold (fun acc (d:VarDecl) -> ValueForall (d, acc)) f new_vars

    /// <summary>
    /// Simplify a value/formula. The resulting value/formula is equivalent.
    /// </summary>
    let rec simplify_value f =
        match f with
        // Implication
        | ValueImply (f1, ValueConst (ConstBool false)) -> simplify_value (ValueNot f1)
        // Negation
        | ValueNot (ValueEqual (v, ValueConst (ConstBool b)))
        | ValueNot (ValueEqual (ValueConst (ConstBool b), v))
            -> simplify_value (ValueEqual (v, ValueConst (ConstBool (not b))))
        | ValueNot (ValueConst (ConstBool b)) -> simplify_value (ValueConst (ConstBool (not b)))
        | ValueNot (ValueNot f) -> simplify_value f
        //| ValueNot (ValueOr (f1, f2)) -> simplify_value (ValueAnd (ValueNot f1, ValueNot f2))
        //| ValueNot (ValueAnd (f1, f2)) -> simplify_value (ValueOr (ValueNot f1, ValueNot f2))
        | ValueNot (ValueForall (d,f)) -> simplify_value (ValueExists (d, ValueNot f))
        | ValueNot (ValueExists (d,f)) -> simplify_value (ValueForall (d, ValueNot f))
        //| ValueNot (ValueImply (f1, f2)) -> simplify_value (ValueAnd (f1, ValueNot f2))
        // Identity cases
        | ValueConst b -> ValueConst b
        | ValueStar t -> ValueStar t
        | ValueEqual (v1, v2) -> ValueEqual (simplify_value v1, simplify_value v2)
        | ValueOr (f1, f2) -> ValueOr (simplify_value f1, simplify_value f2)
        | ValueAnd (f1, f2) -> ValueAnd (simplify_value f1, simplify_value f2)
        | ValueNot f -> ValueNot (simplify_value f)
        | ValueForall (v, f) -> ValueForall (v, simplify_value f)
        | ValueExists (v, f) -> ValueExists (v, simplify_value f)
        | ValueImply (f1, f2) -> ValueImply (simplify_value f1, simplify_value f2)
        | ValueVar v -> ValueVar v
        | ValueFun (str, vs) -> ValueFun (str, List.map simplify_value vs)
        | ValueMacro (str, vs) -> ValueMacro (str, List.map simplify_value vs)
        | ValueSomeElse (d, v1, v2) -> ValueSomeElse (d, simplify_value v1, simplify_value v2)
        | ValueIfElse (f, v1, v2) -> ValueIfElse (simplify_value f, simplify_value v1, simplify_value v2)
        | ValueInterpreted (str, vs) -> ValueInterpreted (str, List.map simplify_value vs)
