module Interpreter

    open MinimalAST

    type ModuleDecl = ModuleDecl<Model.TypeInfos,Model.Environment>

    exception TypeError
    exception EnvironmentError of string

    let value_or v1 v2 =
        match v1, v2 with
        | AST.ConstBool b1, AST.ConstBool b2 -> AST.ConstBool (b1 || b2)
        | _ -> raise TypeError

    let value_not v =
        match v with
        | AST.ConstBool b -> AST.ConstBool (not b)
        | _ -> raise TypeError

    let rec if_some_value (m:ModuleDecl) infos (env:Model.Environment) (decl:VarDecl) v : option<ConstValue> =
        let possible_values = Model.all_values m.Types infos (decl.Type) |> Seq.toList
        try
            Some (List.find (fun cv -> eval_value_with m infos env v [decl.Name] [cv] = AST.ConstBool true) possible_values)
        with :? System.Collections.Generic.KeyNotFoundException -> None

    and evaluate_value (m:ModuleDecl) infos (env:Model.Environment) v =
        match v with
        | ValueConst cv -> cv
        | ValueStar t -> AST.type_default_value m.Types t
        | ValueVar str -> Map.find str env.v
        | ValueFun (str, lst) ->
            let lst = List.map (evaluate_value m infos env) lst
            Map.find (str, lst) env.f
        | ValueEqual (v1, v2) ->
            let cv1 = evaluate_value m infos env v1
            let cv2 = evaluate_value m infos env v2
            AST.ConstBool (AST.value_equal cv1 cv2)
        | ValueOr (v1, v2) -> 
            let cv1 = evaluate_value m infos env v1
            let cv2 = evaluate_value m infos env v2
            value_or cv1 cv2
        | ValueNot v -> 
            let cv = evaluate_value m infos env v
            value_not cv
        | ValueSomeElse (d,f,v) ->
            match if_some_value m infos env d f with
            | Some v -> v
            | None -> evaluate_value m infos env v
        | ValueIfElse (f,v1,v2) ->
            if evaluate_value m infos env f = AST.ConstBool true
            then evaluate_value m infos env v1
            else evaluate_value m infos env v2
        | ValueForall (d,v) ->
            let possible_values = Model.all_values m.Types infos d.Type |> Seq.toList
            AST.ConstBool (List.forall (fun cv -> eval_value_with m infos env v [d.Name] [cv] = AST.ConstBool true) possible_values)
        | ValueInterpreted (str, vs) ->
            let lst = List.map (evaluate_value m infos env) vs
            (find_interpreted_action m str).Effect infos env lst

    and eval_value_with (m:ModuleDecl) infos (env:Model.Environment) v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        evaluate_value m infos { env with v=v' } v

    let evaluate_values (m:ModuleDecl) infos (env:Model.Environment) vs =
        List.map (evaluate_value m infos env) vs

    exception AssertionFailed of Model.Environment * Value
    exception AssumptionFailed of Model.Environment * Value

    /// <summary>
    /// Returns a new environment after entering a new block.
    /// </summary>
    /// <param name="m">Current module</param>
    /// <param name="env">Current environment</param>
    /// <param name="lvars">New local var names</param>
    /// <param name="lvalues">New local var values</param>
    let enter_new_block (m:ModuleDecl) (env:Model.Environment) lvars lvalues : Model.Environment =
        let add_decl acc (decl:VarDecl) v =
            match v with
            | None -> Map.add decl.Name (AST.type_default_value m.Types decl.Type) acc
            | Some v -> Map.add decl.Name v acc
        {env with v=List.fold2 add_decl env.v lvars lvalues }

    /// <summary>
    /// Returns a new environment after leaving the current block.
    /// </summary>
    /// <param name="env">Current environment</param>
    /// <param name="lvars">Local var names of the current block</param>
    /// <param name="old_env">Former environment, before entering the current block</param>
    let leave_block (env:Model.Environment) lvars (old_env:Model.Environment) : Model.Environment =
        let rollback acc (decl:VarDecl) =
            match Map.tryFind decl.Name old_env.v with
            | None -> Map.remove decl.Name acc
            | Some e -> Map.add decl.Name e acc
        { env with v=List.fold rollback env.v lvars }

    let rec execute_statement (m:ModuleDecl) infos (env:Model.Environment) s : Model.Environment =
        match s with
        | AtomicGroup sts ->
            execute_statements m infos env sts
        | NewBlock (decls, ss) ->
            let env' = enter_new_block m env decls (List.map (fun _ -> None) decls)
            let env' = execute_statements m infos env' ss
            leave_block env' decls env
        | VarAssign (str, v) -> // For now, we don't check the types
            let v' = Map.add str (evaluate_value m infos env v) env.v
            { env with v=v' }
        | VarAssignAction (var, action, vs) ->
            let cvs = List.map (evaluate_value m infos env) vs
            let (env,cv) = execute_action m infos env action cvs
            execute_statement m infos env (VarAssign (var, ValueConst cv))
        | FunAssign (str, ds, v) -> // For now, we don't check the types
            let compute_value_for acc inst =
                let value = eval_value_with m infos env v (List.map (fun (v:VarDecl) -> v.Name) ds) inst
                Map.add (str,inst) value acc
            let possibilities = List.map (fun (d:VarDecl) -> d.Type) ds
            let possibilities = Model.all_values_ext m.Types infos possibilities |> Seq.toList
            let res = List.fold compute_value_for Map.empty possibilities
            let f' = Map.fold (fun acc k v -> Map.add k v acc) env.f res
            { env with f=f' }
        | IfElse (v, sif, selse) ->
            let cv = evaluate_value m infos env v
            match cv with
            | AST.ConstBool true -> execute_statement m infos env sif
            | AST.ConstBool false -> execute_statement m infos env selse
            | _ -> raise TypeError
        | IfSomeElse (decl, v, sif, selse) ->
            match if_some_value m infos env decl v with
            | Some value ->
                let env' = enter_new_block m env [decl] [Some value]
                let env' = execute_statement m infos env' sif
                leave_block env' [decl] env
            | None ->
                execute_statement m infos env selse
        | Assert v ->
            if evaluate_value m infos env v = AST.ConstBool true
            then env else raise (AssertionFailed (env, v))
        | Assume v ->
            if evaluate_value m infos env v = AST.ConstBool true
            then env else raise (AssumptionFailed (env, v))

    and execute_statements (m:ModuleDecl) infos (env:Model.Environment) ss =
        List.fold (execute_statement m infos) env ss
    
    and execute_inline_action (m:ModuleDecl) (env:Model.Environment) input output (effect:Model.Environment->Model.Environment) args =
        let env' = enter_new_block m env (output::input) (None::(List.map (fun a -> Some a) args))
        let env' = effect env'
        let res =
            match Map.tryFind output.Name env'.v with
            | None -> AST.type_default_value m.Types output.Type
            | Some cv -> cv
        (leave_block env' (output::input) env, res)

    and execute_action (m:ModuleDecl) infos (env:Model.Environment) action args = // For now, we don't check the types
        let action_decl = find_action m action
        let effect env = execute_statement m infos env action_decl.Content
        execute_inline_action m env action_decl.Args action_decl.Output effect args
