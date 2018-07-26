﻿module Solver

    let decompose_marks (m:Marking.Marks) =
        let var_mark_singleton str =
            {Marking.empty_marks with v=Set.singleton str}
        let fun_mark_singleton (str, cvs) =
            {Marking.empty_marks with f=Set.singleton (str, cvs)}
        let diff_mark_singleton (cv1,cv2) =
            {Marking.empty_marks with d=Set.singleton (cv1, cv2)}
        let vms = List.map var_mark_singleton (m.v |> Set.toList)
        let fms = List.map fun_mark_singleton (m.f |> Set.toList)
        let dms = List.map diff_mark_singleton (m.d |> Set.toList)
        vms@fms@dms

    let z3_formulas_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        let var_constraint str = // Constraints on the arguments
            let cv = Map.find str env.v
            AST.ValueEqual (AST.ValueVar str, AST.ValueConst cv)
        let vcs = List.map var_constraint (m.v |> Set.toList)
        let fun_constraint (str, cvs) =
            let cv = Map.find (str, cvs) env.f
            let vs = List.map (fun cv -> AST.ValueConst cv) cvs
            AST.ValueEqual (AST.ValueFun (str, vs), AST.ValueConst cv)
        let fcs = List.map fun_constraint (m.f |> Set.toList)
        let diff_constraint (cv1, cv2) =
            AST.ValueNot (AST.ValueEqual (AST.ValueConst cv1, AST.ValueConst cv2))
        let dcs = List.map diff_constraint (m.d |> Set.toList)
        let cs = vcs@fcs@dcs
        let cs = List.map (MinimalAST.value2minimal md) cs
        List.map (fun c -> WPR.z3ctx2deterministic_formula (WPR.minimal_val2z3_val mmd c) false) cs

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        WPR.conjunction_of (z3_formulas_for_constraints md mmd env m)

    let z3_fomula_for_axioms (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        WPR.conjunction_of (WPR.conjectures_to_z3values mmd (MinimalAST.axioms_decls_to_formulas mmd.Axioms))

    let z3_formula_for_axioms_and_conjectures (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        let all_invariants = MinimalAST.invariants_decls_to_formulas mmd.Invariants
        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd all_invariants)
        let axioms = z3_fomula_for_axioms mmd
        WPR.Z3And (axioms, conjectures)

    let z3_formula_for_wpr (mmd:MinimalAST.ModuleDecl<'a,'b>) action formula negate =
        let z3formula = WPR.z3ctx2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
        WPR.wpr_for_action mmd z3formula action negate

    [<NoComparison>]
    type SolverResult = UNSAT | UNKNOWN | SAT of Model.TypeInfos * Model.Environment

    let args_decl_for_action mmd action =
        (MinimalAST.find_action mmd action).Args

    let check_z3_formula (md:AST.ModuleDecl<'a,'b>) args_decl f timeout =
        let z3ctx = Z3Utils.build_context md
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx Map.empty f
        let z3e = Z3Utils.build_value z3ctx z3lvars Map.empty f
        match Z3Utils.check z3ctx z3e timeout with
        | Z3Utils.UNSAT -> UNSAT
        | Z3Utils.UNKNOWN -> UNKNOWN
        | Z3Utils.SAT m -> SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m)

    let check_z3_disjunction (md:AST.ModuleDecl<'a,'b>) f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars [] z3ctx Map.empty f
        let z3e = Z3Utils.build_value z3ctx z3lvars Map.empty f

        let declare_lvars (mmd, action, f) =
            let args_decl = (MinimalAST.find_action mmd action).Args
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx Map.empty f (z3lvars, z3concrete_map)
            (mmd, action, Z3Utils.build_value z3ctx z3lvars Map.empty f, (z3lvars, z3concrete_map))
        let fs = List.map declare_lvars fs

        let es = List.map (fun (_,action,es,_) -> (action, es)) fs
        match Z3Utils.check_disjunction z3ctx z3e es timeout with
        | (Z3Utils.UNSAT, _) -> (UNSAT, None)
        | (Z3Utils.UNKNOWN, _) -> (UNKNOWN, None)
        | (Z3Utils.SAT _, None) -> failwith "Can't retrieve action of counterexample..."
        | (Z3Utils.SAT m, Some action) ->
            let (mmd, _, _, (z3lvars, z3concrete_map)) = List.find (fun (_,action',_,_) -> action' = action) fs
            let args_decl = (MinimalAST.find_action mmd action).Args
            (SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m), Some action)

    let z3_unsat_core (md:AST.ModuleDecl<'a,'b>) args_decl local_enums f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let lenums = List.fold (fun acc e -> Z3Utils.declare_new_enumerated_type_ext e z3ctx acc) Map.empty local_enums
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx lenums f
        let z3e = Z3Utils.build_value z3ctx z3lvars lenums f

        let add_constraint ((z3lvars, z3concrete_map),acc) (str,f) =
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx lenums f (z3lvars, z3concrete_map)
            let z3e = Z3Utils.build_value z3ctx z3lvars lenums f
            ((z3lvars, z3concrete_map),(str,z3e)::acc)
        let (_,z3_es) = List.fold add_constraint ((z3lvars, z3concrete_map),[]) fs
        
        Z3Utils.check_conjunction_fix z3ctx z3e z3_es timeout
    
    let find_counterexample_action md mmd action formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let f = WPR.Z3And (axioms_conjectures, z3_formula_for_wpr mmd action formula true)
            let res = check_z3_formula md (args_decl_for_action mmd action) f 3000
        
            counterexample :=
                match res with
                | UNSAT | UNKNOWN -> !counterexample
                | SAT (infos, env) ->
                    let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,infos,_) -> Model.cardinal infos
                    if Model.cardinal infos < former_cardinal
                    then Some (i, formula, infos, env)
                    else !counterexample

        List.iter treat_formula formulas
        !counterexample

    let find_counterexample md mmds formulas =
        let (_,tmp_mmd) = (List.head (Map.toList mmds)) // We arbitrary take axioms and conjectures of the first mmd (they should be exactly the same for every mmd)
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures tmp_mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let fs = List.map (fun (action,mmd) -> (mmd, action, z3_formula_for_wpr mmd action formula true)) (Map.toList mmds)
            let res = check_z3_disjunction md axioms_conjectures fs 3000
            
            counterexample :=
                match res with
                | (UNSAT, _) | (UNKNOWN, _) -> !counterexample
                | (SAT (infos, env), Some action) ->
                    let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,_,infos,_) -> Model.cardinal infos
                    if Model.cardinal infos < former_cardinal
                    then Some (i, action, formula, infos, env)
                    else !counterexample
                | (SAT _, None) -> failwith "Can't retrieve the main action of the counterexample."

        List.iter treat_formula formulas
        !counterexample

    let not_already_allowed_state_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) allowed_execs =
        let f = Formula.formula_from_marks env m allowed_execs true
        let f = AST.ValueNot f
        let f = MinimalAST.value2minimal md f
        WPR.z3ctx2deterministic_formula (WPR.minimal_val2z3_val mmd f) false

    let wpr_based_valid_state_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action other_actions formula =
        let wpr = z3_formula_for_wpr mmd action formula false
        let add_wpr acc (action',mmd') =
            if action' <> action
            then
                let wpr = z3_formula_for_wpr mmd' action' formula false
                WPR.Z3And (acc, wpr)
            else acc
        let wpr = List.fold add_wpr wpr other_actions
        WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

    let terminating_or_failing_run_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action =
        WPR.wpr_for_action mmd (WPR.Z3Const (AST.ConstBool false)) action true

    let find_allowed_execution (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
        action (m:Marking.Marks) other_actions prev_allowed only_terminating_run =

        // 1. Marked constraints
        let cs = z3_formula_for_constraints md mmd env m
        // 2. NOT previous allowed state
        let f = not_already_allowed_state_formula md mmd env m prev_allowed
        // 3. Possibly valid state
        let valid_run = wpr_based_valid_state_formula mmd action other_actions formula
        // 4. If we only want a terminating run...
        let trc =
            if only_terminating_run
            then
                terminating_or_failing_run_formula mmd action
            else
                WPR.Z3Const (AST.ConstBool true)
        // All together
        let f = WPR.Z3And (WPR.Z3And(cs, trc), WPR.Z3And(f,valid_run))
        // Solve!
        match check_z3_formula md (args_decl_for_action mmd action) f 3000 with
        | UNSAT | UNKNOWN -> None
        | SAT (i,e) -> Some (i,e)

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) (additional_marks:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }

        let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let constraints = z3_formula_for_constraints md mmd env (Marking.marks_union m additional_marks)
            let tested_constraint = z3_formula_for_constraints md mmd env m'
            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not tested_constraint)
            match check_z3_formula md [] f 1000 with
            | UNSAT -> false
            | _ -> true
        let keep_mark_if_necessary (m:Marking.Marks) m' =
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        List.fold keep_mark_if_necessary m (decompose_marks m)

    let expand_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) (m:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
        // We add every valid fun/diff constraint!
        let cs = z3_formula_for_constraints md mmd env m
        let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
        let f = WPR.Z3And (cs, axioms_conjs)
        let is_formula_valid f' =
            let f = WPR.Z3And (f, WPR.Z3Not f')
            match check_z3_formula md [] f 1000 with
            | UNSAT ->
                // We don't add mark if t can be deduced directly from the axioms
                let f = WPR.Z3And (axioms_conjs, WPR.Z3Not f')
                match check_z3_formula md [] f 1000 with
                | SAT _ -> true
                | _ -> false
            | _ -> false
        let is_mark_valid m =
            let f = z3_formula_for_constraints md mmd env m
            is_formula_valid f

        let fm = List.map (fun (k,_) -> k) (Map.toList env.f) |> Set.ofList
        let diffs = Set.unionMany (List.map (fun t -> Formula.all_diffs_for_type md.Types infos t) (AST.all_uninterpreted_types md.Types))
        let m = { Marking.empty_marks with Marking.d = diffs ; Marking.f = fm }
        let ms = decompose_marks m
        let ms = List.filter is_mark_valid ms
        Marking.marks_union_many ms

    type MinimizationMode = Safe | Hard | MinimizeAltExec
    let wpr_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) action other_actions formula (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) (mode:MinimizationMode) =
        
        let m = { m with v = Set.empty } // We remove local vars
        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks!
        
        // Unsat core!
        let f =
            match mode with
            | Safe | Hard ->
                let f = not_already_allowed_state_formula md mmd env m alt_exec
                let f = WPR.Z3And (f, wpr_based_valid_state_formula mmd action other_actions formula)
                if mode = Hard
                then WPR.Z3And (f, terminating_or_failing_run_formula mmd action)
                else f
            | MinimizeAltExec ->
                let not_valid_run = WPR.Z3Not (wpr_based_valid_state_formula mmd action other_actions formula)
                let f = z3_formula_for_constraints md mmd env m
                WPR.Z3And (f, not_valid_run)

        let (save_m, m, env) =
            if mode = MinimizeAltExec then
                assert (List.length alt_exec = 1)
                let (m', env) = List.head alt_exec
                let m' = { m' with v = Set.empty } // We remove local vars
                let save_m = m'
                let m' = expand_marks md mmd infos env (Marking.marks_union m m') // We expand marks!
                (save_m,Marking.marks_diff m' m, env)
            else (save_m, m, env)

        let ms = decompose_marks m
        let labeled_ms = List.mapi (fun i m -> (sprintf "%i" i, m)) ms
        let labeled_cs = List.map (fun (i,m) -> (i, z3_formula_for_constraints md mmd env m)) labeled_ms

        match z3_unsat_core md (args_decl_for_action mmd action) [] f labeled_cs 5000 with
        | (Z3Utils.SolverResult.UNSAT, lst) ->
            let labeled_ms = List.filter (fun (str,_) -> List.contains str lst) labeled_ms
            let ms = List.map (fun (_,m) -> m) labeled_ms
            Marking.marks_union_many ms
        | (Z3Utils.SolverResult.UNKNOWN _, _) ->
            printfn "Can't resolve unSAT core!"
            save_m
        | (Z3Utils.SolverResult.SAT _, _) ->
            printfn "Core is SAT."
            save_m
        // TODO: run unsat core only for constraints on functions, and then run unsat core for disequalities on the result?
        // Alternatively, constraints should be sorted by order of "strength"

    let has_k_exec_counterexample_formula formula actions init_actions boundary =

        let rec compute_next_iterations fs n =
            match n with
            | n when n <= 0 -> (*printfn "All paths have been computed!" ;*) fs
            | n ->
                //printfn "Computing level %i..." n
                let prev = List.head fs
                let wprs = List.map (fun (action,mmd) -> WPR.wpr_for_action mmd prev action false) actions
                let wpr = WPR.conjunction_of wprs
                compute_next_iterations (wpr::fs) (n-1)

        let paths = compute_next_iterations [formula] boundary
        let f = WPR.conjunction_of paths
        // Add initializations
        let f = List.fold (fun f (action,mmd) -> WPR.wpr_for_action mmd f action false) f init_actions
        WPR.Z3Not f
        
    let sbv_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) actions init_actions (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) boundary =

        // TMP Tests
        // TODO: Fix axioms that seem to be ignored
        let axioms = z3_fomula_for_axioms mmd 
        printfn "%A" (check_z3_formula md [](WPR.Z3And (axioms,has_k_exec_counterexample_formula (WPR.Z3Const (AST.ConstBool true)) actions init_actions boundary)) 5000)
        // ----------

        let m = { m with v = Set.empty } // We remove local vars
        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks!

        let axioms = z3_fomula_for_axioms mmd
        let give_k_invariant m =
            let f = WPR.z3ctx2deterministic_formula (WPR.minimal_val2z3_val mmd (MinimalAST.value2minimal md (Formula.formula_from_marks env m alt_exec false))) false
            let f = WPR.Z3And (axioms, has_k_exec_counterexample_formula f actions init_actions boundary)
            match check_z3_formula md [] f 5000 with
            | SolverResult.UNKNOWN ->
                printfn "Can't decide of satisfiability!"
                false
            | SolverResult.UNSAT -> true
            | SolverResult.SAT _ -> false

        if give_k_invariant m
        then
            let keep_mark_if_necessary (m:Marking.Marks) m' =
                let m' = Marking.marks_diff m m'
                if give_k_invariant m'
                then m' else m
            List.fold keep_mark_if_necessary m (decompose_marks m)
        else
            printfn "ERROR: The whole formula is not a k-invariant!"
            save_m

        