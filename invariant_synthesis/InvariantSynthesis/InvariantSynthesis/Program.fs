﻿open System.Text
open System
open AST

type ModuleDecl = ModuleDecl<Model.TypeInfos,Model.Environment>

let read_until_line_jump () =
    let str = new StringBuilder()
    let line = ref "_"
    while !line <> "" do
        line := Console.ReadLine()
        ignore (str.Append(!line + Environment.NewLine))
    str.ToString()

let parser_cmd = "lin"
let parser_args = "parser.native all %IN% %OUT% %ERR%"
let parser_output_path = "parser.out"
let parser_error_path = "parser.err"

// ----- MANUAL MODE -----

let manual_counterexample (md:ModuleDecl) decls action verbose =
    printfn "Please enter constraints:"
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs = ConstraintsParser.parse_from_str md str
    printfn "Building environment from constraints..."
    let (infos, env) = Model.constraints_to_env md cs
    if verbose
    then
        printfn "%A" infos
        printfn "%A" env

    let args_decl = (find_action md action "").Args
    let env =
        List.fold
            (
                fun (acc:Model.Environment) vd ->
                    printfn "Please enter next arg:"
                    let cv =
                        match vd.Type with
                        | Void -> ConstVoid
                        | Bool -> ConstBool (Convert.ToBoolean (Console.ReadLine()))
                        | Uninterpreted str -> ConstInt (str, Convert.ToInt32 (Console.ReadLine()))
                    { acc with v = Map.add vd.Name cv acc.v }
            )
            env args_decl
    
    let mmd = MinimalAST.module2minimal md action

    printfn "Executing..."
    let tr = TInterpreter.trace_action mmd infos env action (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor
    let env' = Trace.final_env tr
    if verbose
    then
        printfn "%A" env'

    if Trace.is_fully_executed tr
    then
        printfn "Please enter the index of the invariant to analyze:"
        let (main_module,_) = AST.decompose_name action
        let invs = AST.find_invariants md main_module
        List.iteri
            (
                fun i (d:AST.InvariantDecl) ->
                    let mv = MinimalAST.value2minimal md d.Formula
                    match Interpreter.evaluate_value mmd infos env' mv with
                    | ConstBool true -> Console.ForegroundColor <- ConsoleColor.Green
                    | ConstBool false -> Console.ForegroundColor <- ConsoleColor.Red
                    | _ -> Console.ResetColor()
                    printfn "%i. [%s] %s" i d.Module (Printer.value_to_string decls d.Formula 0)
            ) invs
        Console.ResetColor()

        let nb = Convert.ToInt32 (Console.ReadLine())
        let formula = List.item nb (AST.invariants_to_formulas invs)
        let formula = MinimalAST.value2minimal md formula
        Some (mmd, action, infos, env, cs, formula, tr)
    else
        Some (mmd, action, infos, env, cs, MinimalAST.ValueConst (ConstBool true), tr)
    
let manual_allowed_path (md:ModuleDecl) decls env cs m um' =
    printfn "Please modify some constraints on the environment to change the final formula value."
    printfn ""
    printfn "Constraints you can't change:"
    printfn "%s" (Printer.marks_to_string decls env m)
    printfn ""
    printfn "Constraints you should change (at least one):"
    printfn "%s" (Printer.marks_to_string decls env um')

    printfn ""
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs' = ConstraintsParser.parse_from_str md str
    printfn "Building new environment..."
    let (infos_allowed, env_allowed) = Model.constraints_to_env md (cs@cs')
    printfn "Computing..."
    Some (infos_allowed, { env_allowed with v=env.v }) // We keep the same args as before

// ----- AUTO MODE -----

let auto_counterexample (md:ModuleDecl) decls action verbose =

    let mmd = MinimalAST.module2minimal md action
    let mmd = Determinization.determinize_action mmd action
    let action_args = (MinimalAST.find_action mmd action).Args

    let counterexample = ref None
    let first_loop = ref true
    let finished = ref false

    let (main_module,_) = AST.decompose_name action
    let invs = AST.find_invariants md main_module

    while not (!finished) do

        let formulas =
            if !first_loop
            then
                first_loop := false
                printfn "Searching assertions fail..."
                Some [(-1,MinimalAST.ValueConst (ConstBool true))]
            else
                printfn "Select the conjecture(s) to test (separate by space, '*' for all):"
                List.iteri (fun i (d:AST.InvariantDecl) -> printfn "%i. [%s] %s" i d.Module (Printer.value_to_string decls d.Formula 0)) invs
                let line = Console.ReadLine()
                let nbs =
                    if line = "*"
                    then List.mapi (fun i _ -> sprintf "%i" i) invs
                    else line.Split ([|' '|], StringSplitOptions.RemoveEmptyEntries) |> List.ofArray
                if List.isEmpty nbs
                then None
                else
                    let nbs = List.map (fun (str:string) -> Convert.ToInt32 str) nbs
                    let formulas = List.map (fun nb -> (nb,List.item nb (AST.invariants_to_formulas invs))) nbs
                    let formulas = List.map (fun (nb,formula) -> (nb,MinimalAST.value2minimal md formula)) formulas
                    Some formulas

        match formulas with
        | None -> finished := true
        | Some formulas ->
            match Simplification.find_counterexample mmd action formulas with
            | None -> counterexample := None
            | Some c -> finished := true ; counterexample := Some c

    match !counterexample with
    | None -> None
    | Some (i, formula, infos, env) ->
        printfn "Invariant n°%i." i
        let tr = TInterpreter.trace_action mmd infos env action (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) action_args) AST.impossible_var_factor
        Some (mmd, action, infos, env, [], formula, tr)

let auto_allowed_path (md:ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
    action (m:Synthesis.Marks) prev_allowed only_terminating_run =

    let f = Simplification.generate_allowed_path_formula md mmd env formula action m prev_allowed only_terminating_run
    Simplification.check_z3_formula mmd (Some action) f 3000

// ----- MAIN -----

let analyse_example_ending mmd infos tr formula =
    let env' = Trace.final_env tr
    if Trace.is_fully_executed tr
    then
        let (b,cfgs) = Synthesis.marks_for_value mmd infos env' Set.empty formula
        let cfg = Synthesis.best_cfg cfgs
        if b <> ConstBool true && b <> ConstBool false
        then failwith "Invalid execution!"
        (b = ConstBool true, true, cfg)
    else
        (Trace.assume_failed tr, false, Synthesis.empty_config)

[<EntryPoint>]
let main argv =

    let verbose = Array.contains "-v" argv
    let manual = Array.contains "-m" argv

    let filename = 
        match Array.tryLast argv with
        | None -> ""
        | Some str ->
            if str.EndsWith(".ivy")
            then str else ""

    let (md:ModuleDecl) =
        if filename = ""
        then
            printfn "Loading hardcoded test module 'queue'..."
            TestModule.Queue.queue_module
        else
            printfn "Parsing module..."
            let args = parser_args.Replace("%IN%", "\"" + filename + "\"").Replace("%OUT%", "\"" + parser_output_path + "\"").Replace("%ERR%", "\"" + parser_error_path + "\"")
            System.IO.File.Delete(parser_output_path)
            System.IO.File.Delete(parser_error_path)
            System.Diagnostics.Process.Start(parser_cmd, args).WaitForExit()
            let err =
                try System.IO.File.ReadAllText(parser_error_path)
                with :? System.IO.FileNotFoundException -> ""
            if err <> ""
            then
                printfn "Parser error: %s" err
                ignore (Console.ReadLine())
                failwith "Parser error!"
            else
                let content = System.IO.File.ReadAllText(parser_output_path)
                let parsed_elts = ParserAST.deserialize content
                printfn "Converting parsed AST..."
                ParserAST.ivy_elements_to_ast_module filename parsed_elts

    // Remove unwanted implementations from the module decl
    printfn "Please enter the names of the concrete modules to ban:"
    let str = read_until_line_jump ()
    let banned_modules = str.Split([|Environment.NewLine|], StringSplitOptions.RemoveEmptyEntries)
    let md = AST.exclude_from_module md (Seq.toList banned_modules)
    let decls = Model.declarations_of_module md

    while true do
        // Choose the action to analyze

        let possible_actions = List.map (fun (d:ActionDecl) -> d.Name) md.Actions
        let possible_actions = List.filter (fun str -> let (_,v) = AST.decompose_action_name str in v = "") possible_actions
        printfn "Which action do you want to analyze?"
        List.iteri (fun i str -> printfn "%i. %s" i str) possible_actions
        let nb = Convert.ToInt32 (Console.ReadLine())
        let name = List.item nb possible_actions

        // Let's go!

        let counterexample =
            if manual
            then manual_counterexample md decls name verbose
            else auto_counterexample md decls name verbose

        match counterexample with
        | None -> ()
        | Some (mmd, name, infos, env, cs, formula, tr) ->
            let (b,finished_exec,(m,um,ad)) =
                analyse_example_ending mmd infos tr formula
            if b then failwith "Invalid counterexample!"

            printfn "Going back through the action..."
            let (m,um,ad) = Synthesis.marks_before_statement mmd infos true false tr (m,um,ad)
            if verbose
            then
                printfn "%A" m
                printfn "%A" um
                printfn "%A" ad

            let m = Simplification.simplify_marks md mmd env m (Synthesis.empty_marks)//Formula.simplify_marks infos md.Implications decls env m
            let um = Simplification.simplify_marks md mmd env um (Synthesis.empty_marks) //Formula.simplify_marks infos md.Implications decls env um
            let f = Formula.formula_from_marks env m [] false
            let f = Formula.simplify_value f
            printfn "%s" (Printer.value_to_string decls f 0)
            printfn ""

            let allowed_paths = ref []
            if ad.md
            then
                printfn "This invariant may be too strong!"
                printfn "(Some model-dependent marks have been ignored)"
                printfn "Would you like to add an allowed path to the invariant? (y/n)"
                let answer = ref (Console.ReadLine())
                let only_terminating_exec = ref true
                while !answer = "y" do

                    let allowed_path_opt =
                        if manual
                        then manual_allowed_path md decls env cs m um
                        else auto_allowed_path md mmd env formula name m (!allowed_paths) (!only_terminating_exec)

                    match allowed_path_opt with
                    | Some (infos_allowed, env_allowed) ->
                        let args_decl = (MinimalAST.find_action mmd name).Args
                        let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor

                        let (b_al,_,(m_al,um_al,ad_al)) =
                            analyse_example_ending mmd infos_allowed tr_allowed formula

                        if b_al
                        then
                            let (m_al,_,ad_al) =
                                Synthesis.marks_before_statement mmd infos_allowed finished_exec true tr_allowed (m_al,um_al,ad_al)
                            if ad_al.md
                            then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."
                            let m_al = Simplification.simplify_marks md mmd env m_al m
                            allowed_paths := (m_al,env_allowed)::(!allowed_paths)
                        else printfn "ERROR: Illegal execution!"
                    | None ->
                        printfn "No more allowed path found!"
                        if !only_terminating_exec = true
                        then
                            printfn "Extending the search domain to non-terminating runs..."
                            only_terminating_exec := false
            
                    printfn "Would you like to add an allowed path to the invariant? (y/n)"
                    answer := Console.ReadLine()
            else
                printfn "These conditions are sufficient to break the invariant!"

            printfn "Proceed to hard simplification? (y/n)"
            let m' =
                if Console.ReadLine () = "y"
                then Simplification.simplify_marks_hard md mmd env name formula m (!allowed_paths)
                else m

            let f = Formula.formula_from_marks env m' (!allowed_paths) false
            let f = Formula.simplify_value f

            printfn ""
            printfn "Invariant to add:"
            printfn "%s" (Printer.value_to_string decls f 0)
            ignore (Console.ReadLine())
    
    0
