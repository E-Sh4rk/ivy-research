open System.Text
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

// ----- MANUAL MODE -----

let manual_counterexample (md:ModuleDecl) decls possible_actions mmds verbose =
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

    printfn "Which action do you want to analyze?"
    List.iteri (fun i str -> printfn "%i. %s" i str) possible_actions
    let nb = Convert.ToInt32 (Console.ReadLine())
    let action = List.item nb possible_actions

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
                        | Enumerated str -> ConstEnumerated (str, Console.ReadLine())
                    { acc with v = Map.add vd.Name cv acc.v }
            )
            env args_decl
    
    let mmd = Map.find action mmds

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
        Some (action, infos, env, cs, formula, tr)
    else
        Some (action, infos, env, cs, MinimalAST.ValueConst (ConstBool true), tr)
    
let manual_allowed_path (md:ModuleDecl) decls env cs m um =
    printfn "Please modify some constraints on the environment to change the final formula value."
    printfn ""
    printfn "Constraints you can't change:"
    printfn "%s" (Printer.marks_to_string decls env m)
    printfn ""
    printfn "Constraints you should change (at least one):"
    printfn "%s" (Printer.marks_to_string decls env um)

    printfn ""
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs' = ConstraintsParser.parse_from_str md str
    printfn "Building new environment..."
    let (infos_allowed, env_allowed) = Model.constraints_to_env md (cs@cs')
    printfn "Computing..."
    Some (infos_allowed, { env_allowed with v=env.v }) // We keep the same args as before

// ----- AUTO MODE -----

let auto_counterexample (md:ModuleDecl) decls main_module mmds =

    let counterexample = ref None
    let first_loop = ref true
    let finished = ref false

    let invs = AST.find_invariants md main_module

    while not (!finished) do

        let formulas =
            if !first_loop
            then
                first_loop := false
                printfn "Searching assertions fail..."
                Some [(-1,MinimalAST.ValueConst (ConstBool true))]
            else
                printfn "Select the conjecture(s) to test (separated by space, '*' for all):"
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
            match Solver.find_counterexample md mmds formulas with
            | None -> counterexample := None
            | Some c -> finished := true ; counterexample := Some c

    match !counterexample with
    | None -> None
    | Some (i, action, formula, infos, env) ->
        let mmd = Map.find action mmds
        let action_args = (MinimalAST.find_action mmd action).Args
        printfn "Invariant n°%i: %s" i action
        let tr = TInterpreter.trace_action mmd infos env action (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) action_args) AST.impossible_var_factor
        Some (action, infos, env, [], formula, tr)

let auto_allowed_path (md:ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
    action (m:Marking.Marks) all_actions prev_allowed only_terminating_run =
    Solver.find_allowed_execution md mmd env formula action m all_actions prev_allowed only_terminating_run


// ----- MAIN -----

/// <summary>
/// Analyzes a trace. Returns a tuple (is formula satisfied after execution, is action fully executed (=no assumption/assertion fail), marks for the ending state).
/// </summary>
let analyse_example_ending mmd infos tr formula =
    let env' = Trace.final_env tr
    if Trace.is_fully_executed tr
    then
        let (b,cfgs) = Marking.marks_for_value mmd infos env' Set.empty formula
        let cfg = Marking.best_cfg cfgs
        if b <> ConstBool true && b <> ConstBool false
        then failwith "Invalid execution!"
        (b = ConstBool true, true, cfg)
    else
        (Trace.assume_failed tr, false, Marking.empty_config)

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

    // Loading a module
    let (md:ModuleDecl) =
        if filename = ""
        then
            // Hardcoded module
            printfn "Loading hardcoded test module 'queue'..."
            TestModule.Queue.queue_module
        else
            // External .ivy file
            printfn "Parsing module..."
            let args = Config.parser_args.Replace("%IN%", "\"" + filename + "\"").Replace("%OUT%", "\"" + Config.parser_output_path + "\"").Replace("%ERR%", "\"" + Config.parser_error_path + "\"")
            System.IO.File.Delete(Config.parser_output_path)
            System.IO.File.Delete(Config.parser_error_path)
            System.Diagnostics.Process.Start(Config.parser_cmd, args).WaitForExit()
            let err =
                try System.IO.File.ReadAllText(Config.parser_error_path)
                with :? System.IO.FileNotFoundException -> ""
            if err <> ""
            then
                printfn "Parser error: %s" err
                ignore (Console.ReadLine())
                failwith "Parser error!"
            else
                let content = System.IO.File.ReadAllText(Config.parser_output_path)
                let parsed_elts = ParserAST.deserialize content
                printfn "Converting parsed AST..."
                ParserAST.ivy_elements_to_ast_module filename parsed_elts

    // Remove unwanted implementations from the module declaration
    // If a module should be treated as an abstract module, its implementation must be removed
    printfn "Please enter the names of the concrete modules to ignore:"
    let str = read_until_line_jump ()
    let banned_modules = str.Split([|Environment.NewLine|], StringSplitOptions.RemoveEmptyEntries)
    let md = AST.exclude_from_module md (Seq.toList banned_modules)
    let decls = Model.declarations_of_module md

    // Retrieve `init` actions in the right order
    let all_actions =
        List.fold (fun acc (a:AST.ActionDecl) -> let (name,_) = AST.decompose_variant_action_name a.Name in Set.add name acc) Set.empty md.Actions
    let init_actions = Set.filter (fun str -> let (_,name) = AST.decompose_name str in name = "init") all_actions
    let action_is_child str1 str2 =
        let (mod1,_) = AST.decompose_name str1
        let (mod2,_) = AST.decompose_name str2
        AST.has_base_name mod1 mod2
    let init_actions_cmp str1 str2 =
        if str1=str2 then 0
        else if action_is_child str1 str2 then -1
        else if action_is_child str2 str1 then 1
        else 0
    let init_actions = List.sortWith init_actions_cmp (Set.toList init_actions)

    // Build corresponding minimal modules
    let build_mmd action =
        Determinization.determinize_action (MinimalAST.module2minimal md action) action
    let init_actions = List.map (fun str -> (str,build_mmd str)) init_actions

    while true do
        // Retrieve the actions to analyze
        printfn "Please enter the name of the module containing the actions to analyze:"
        let main_module = Console.ReadLine ()
        let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
        let possible_actions = List.map (fun (_,str) -> str) possible_actions

        if not (List.isEmpty possible_actions)
        then
            // Build minimal modules for each action
            let mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

            // Let's go!
            // Find a counterexample
            let counterexample =
                if manual
                then manual_counterexample md decls possible_actions mmds verbose
                else auto_counterexample md decls main_module mmds

            match counterexample with
            | None -> ()
            | Some (name, infos, env, cs, formula, tr) ->
                let mmd = Map.find name mmds
                let (b,finished_exec,(m,um,ad)) =
                    analyse_example_ending mmd infos tr formula
                if b then failwith "Invalid counterexample!"

                // Backpropagate marks
                printfn "Going back through the action..."
                let (m,um,ad) = Marking.marks_before_statement mmd infos true false tr (m,um,ad)
                let (m,um) = (Marking.remove_all_var_marks m, Marking.remove_all_var_marks um)
                if verbose
                then
                    printfn "%A" m
                    printfn "%A" um
                    printfn "%A" ad
                let common_cvs = Formula.concrete_values_of_marks env m

                // Print intermediate result
                let f = Formula.generate_invariant env common_cvs (Solver.simplify_marks md mmd env m (Marking.empty_marks)) []
                let f = Formula.simplify_value f
                printfn "%s" (Printer.value_to_string decls f 0)
                printfn ""

                // Second step: weakening (for non-monotonic counterexamples)
                let allowed_paths = ref []
                if ad.md
                then
                    printfn "Non-monotonic counterexample: This invariant may be too strong!"
                    printfn "(Some model-dependent marks have been ignored)"
                    printfn "Would you like to weaken the invariant with an allowed execution? (y/n)"
                    let answer = ref (Console.ReadLine())
                    let only_terminating_exec = ref true
                    while !answer = "y" do

                        // Find a potentially valid execution
                        let allowed_path_opt =
                            if manual
                            then manual_allowed_path md decls env cs m um
                            else auto_allowed_path md mmd env formula name m (Map.toList mmds) common_cvs (!allowed_paths) (!only_terminating_exec)

                        match allowed_path_opt with
                        | Some (infos_allowed, env_allowed) ->
                            let args_decl = (MinimalAST.find_action mmd name).Args
                            let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor

                            let (b_al,_,(m_al,um_al,ad_al)) =
                                analyse_example_ending mmd infos_allowed tr_allowed formula

                            if b_al
                            then
                                // Backpropagate marks
                                let (m_al,_,ad_al) = Marking.marks_before_statement mmd infos_allowed finished_exec true tr_allowed (m_al,um_al,ad_al)
                                let m_al = Marking.remove_all_var_marks m_al
                                if ad_al.md
                                then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."

                                // Printing
                                let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                                let f_al = Formula.simplify_value f_al
                                printfn "%s" (Printer.value_to_string decls f_al 0)

                                // Minimization (existential part) (optional)
                                printfn "Try to minimize this existential part now (can weaken the final invariant)? (n:no/y:yes)"
                                let m_al =
                                    let line = Console.ReadLine ()
                                    if line = "y"
                                    then
                                        let m_al = Solver.wpr_based_minimization_existential_part md mmd infos env (Map.toList mmds) formula m common_cvs env_allowed m_al
                                        let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                                        let f_al = Formula.simplify_value f_al
                                        printfn "%s" (Printer.value_to_string decls f_al 0)
                                        m_al
                                    else m_al

                                allowed_paths := (m_al,env_allowed)::(!allowed_paths)
                            else printfn "ERROR: Illegal execution!"
                        | None ->
                            printfn "No more allowed execution found!"
                            if !only_terminating_exec = true
                            then
                                printfn "Extending the search domain to non-terminating runs..."
                                only_terminating_exec := false
            
                        printfn "Would you like to weaken the invariant with an allowed execution? (y/n)"
                        answer := Console.ReadLine()
                else
                    printfn "Monotonic counterexample: This invariant should already be correct!"

                // If the counterexample was not monotonic but no allowed execution was found... it may be because of decidability issues
                let (m,common_cvs) =
                    if ad.md && List.isEmpty (!allowed_paths)
                    then
                        printfn "No allowed execution found... maybe for decidability reasons. In this case, would you like to consider the following model-dependent marks? (y/n)"
                        printfn "%s" (Printer.marks_to_string decls env um)
                        if (Console.ReadLine ()) = "y"
                        then
                            let m = Marking.marks_union m um
                            (m, Formula.concrete_values_of_marks env m)
                        else (m, common_cvs)
                    else (m, common_cvs)

                // Minimization (universal part) (optional)
                printfn "Minimize universal part? (n:no/s:safe/h:hard/[0-9]:sbv)"
                let m =
                    let line = Console.ReadLine ()
                    if line = "h"
                    then Solver.wpr_based_minimization md mmd infos env name (Map.toList mmds) formula m common_cvs (!allowed_paths) true
                    else if line = "s"
                    then Solver.wpr_based_minimization md mmd infos env name (Map.toList mmds) formula m common_cvs (!allowed_paths) false
                    else if line = "n"
                    then m
                    else
                        let boundary = int(Convert.ToUInt32 (line))
                        Solver.sbv_based_minimization md mmd infos env (Map.toList mmds) init_actions m common_cvs (!allowed_paths) boundary
                let m = Solver.simplify_marks md mmd env m (Marking.empty_marks)

                // Minimization (existential parts again, if not already done before) (optional)
                if List.length (!allowed_paths) > 0
                then
                    printfn "Minimize existential parts? (n:no/y:yes)"
                    if Console.ReadLine () = "y"
                    then
                        let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.wpr_based_minimization_existential_part md mmd infos env (Map.toList mmds) formula m common_cvs env_al m_al,env_al)) (!allowed_paths)
                        allowed_paths := allowed_paths'
                    let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.simplify_marks md mmd env_al m_al m,env_al)) (!allowed_paths)
                    allowed_paths := allowed_paths'

                // Print final result
                let f = Formula.generate_invariant env common_cvs m (!allowed_paths)
                let f = Formula.simplify_value f
                printfn "\nInvariant to add:"
                printfn "%s" (Printer.value_to_string decls f 0)
                ignore (Console.ReadLine())

    0
