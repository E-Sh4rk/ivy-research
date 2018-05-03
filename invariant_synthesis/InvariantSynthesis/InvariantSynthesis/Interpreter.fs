﻿module Interpreter

    open AST
    open System.Collections.Generic

    let all_values infos data_type =
        match data_type with
        | Void -> Seq.singleton ConstVoid
        | Bool -> [ConstBool false; ConstBool true] |> Seq.ofList
        | Uninterpreted s ->
            let max = Map.find s infos
            seq { for x in 0..max -> ConstInt (s, x) }

    let pick_value infos data_type =
        Seq.head (all_values infos data_type)

    let rec evaluate_value (env:Model.Environment) v =
        match v with
        | ValueConst cv -> cv
        | ValueVar str -> Map.find str env.v
        | ValueFun (str, lst) ->
            let lst = List.map (evaluate_value env) lst
            Map.find (str, lst) env.f
    
    let value_equal infos v1 v2 = v1=v2

    let rec evaluate_formula infos (env:Model.Environment) f =
        match f with
        | Const b -> b
        | Equal (v1,v2) ->
            let v1 = evaluate_value env v1
            let v2 = evaluate_value env v2
            value_equal env v1 v2
        | Or (f1,f2) ->
            let f1 = evaluate_formula infos env f1
            let f2 = evaluate_formula infos env f2
            f1 || f2
        | And (f1,f2) ->
            let f1 = evaluate_formula infos env f1
            let f2 = evaluate_formula infos env f2
            f1 && f2
        | Not f -> not (evaluate_formula infos env f)
        | Forall (d,f) ->
            let eval_with value =
                let v' = Map.add d.Name value env.v
                evaluate_formula infos { env with v=v' } f
            let possible_values = all_values infos d.Type
            Seq.forall eval_with possible_values
        | Exists (d,f) ->
            let eval_with value =
                let v' = Map.add d.Name value env.v
                evaluate_formula infos { env with v=v' } f
            let possible_values = all_values infos d.Type
            Seq.exists eval_with possible_values
    
    let value_or v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 || b2)
        | _ -> ConstVoid

    let value_and v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 && b2)
        | _ -> ConstVoid

    let value_not v =
        match v with
        | ConstBool b -> ConstBool (not b)
        | _ -> ConstVoid

    exception AssertionFailed

    let rec evaluate_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        match e with
        | ExprConst cv -> (env, cv)
        | ExprVar v -> (env, evaluate_value env (ValueVar v))
        | ExprFun (str, lst) ->
            let (env, lst) = evaluate_expressions m infos env lst
            let lst = List.map (fun cv -> ValueConst cv) lst
            (env, evaluate_value env (ValueFun (str, lst)))
        | ExprAction (str, lst) ->
            let (env, lst) = evaluate_expressions m infos env lst
            execute_action m infos env str lst
        | ExprEqual (e1, e2) ->
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, ConstBool (value_equal env v1 v2))
        | ExprOr (e1, e2) -> 
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, value_or v1 v2)
        | ExprAnd (e1, e2) -> 
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, value_and v1 v2)
        | ExprNot e -> 
            let (env, v) = evaluate_expression m infos env e
            (env, value_not v)

    and evaluate_expressions (m:ModuleDecl) infos (env:Model.Environment) es =
        let aux (env, res) e =
            let (env, v) = evaluate_expression m infos env e
            (env, v::res)
        let (env, res) = List.fold aux (env, []) es
        (env, List.rev res)

    and execute_statement (m:ModuleDecl) infos (env:Model.Environment) s : Model.Environment =
        match s with
        | NewBlock (decls, ss) ->
            let add_decl acc (decl:VarDecl) =
                Map.add decl.Name (pick_value infos decl.Type) acc
            let env' = {env with v=List.fold add_decl env.v decls }
            let env' = execute_statements m infos env' ss
            // Undo changes of new env for local variables
            let rollback acc (decl:VarDecl) =
                match Map.tryFind decl.Name env.v with
                | None -> Map.remove decl.Name acc
                | Some e -> Map.add decl.Name e acc
            { env' with v=List.fold rollback env'.v decls }
        | Expression e ->
            let (env, _) = evaluate_expression m infos env e
            env
        | VarAssign (str, e) -> // For now, we don't check the types
            let (env, res) = evaluate_expression m infos env e
            let v' = Map.add str res env.v
            { env with v=v' }
        | FunAssign (str, lst, e) -> // For now, we don't check the types
            let (env, lst) = evaluate_expressions m infos env lst
            let (env, res) = evaluate_expression m infos env e
            let f' = Map.add (str, lst) res env.f
            { env with f=f' }
        | IfSomeElse (decl, f, sif, selse) ->
            let eval_with (env:Model.Environment) value =
                let v' = Map.add decl.Name value env.v
                evaluate_formula infos { env with v=v' } f
            let possible_values = all_values infos (decl.Type)
            try
                let value = Seq.find (eval_with env) possible_values
                let v' = Map.add decl.Name value env.v
                execute_statement m infos { env with v=v' } sif
            with :? KeyNotFoundException ->
                execute_statement m infos env selse
        | Assert f ->
            if evaluate_formula infos env f then env
            else raise AssertionFailed

    and execute_statements (m:ModuleDecl) infos (env:Model.Environment) ss =
        let aux env s =
            execute_statement m infos env s
        List.fold aux env ss

    and execute_action (m:ModuleDecl) infos (env:Model.Environment) action args = // For now, we don't check the types
        let action_decl = List.find (fun (adecl:ActionDecl) -> adecl.Name = action) m.Actions
        let add_decl acc (decl:VarDecl) v = Map.add decl.Name v acc
        let env' = { env with v=List.fold2 add_decl env.v action_decl.Args args }
        let env' = { env' with v=Map.add action_decl.Output.Name (pick_value infos action_decl.Output.Type) env'.v }
        let env' = execute_statement m infos env' action_decl.Content
        let res =
            match Map.tryFind action_decl.Output.Name env'.v with
            | None -> ConstVoid
            | Some cv -> cv
        // Undo changes of new env for local variables
        let rollback acc (decl:VarDecl) =
            match Map.tryFind decl.Name env.v with
            | None -> Map.remove decl.Name acc
            | Some e -> Map.add decl.Name e acc
        ({ env' with v=List.fold rollback env'.v (action_decl.Output::action_decl.Args) }, res)
        // TODO: Handle abstract actions
