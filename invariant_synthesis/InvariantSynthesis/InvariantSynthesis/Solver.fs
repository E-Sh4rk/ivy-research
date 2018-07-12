﻿module Solver

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        let add_var_constraint cs str = // Constraints on the arguments
            let cv = Map.find str env.v
            AST.ValueAnd (cs, AST.ValueEqual (AST.ValueVar str, AST.ValueConst cv))
        let cs = Set.fold add_var_constraint (AST.ValueConst (AST.ConstBool true)) m.v
        let add_fun_constraint cs (str, cvs) =
            let cv = Map.find (str, cvs) env.f
            let vs = List.map (fun cv -> AST.ValueConst cv) cvs
            AST.ValueAnd (cs, AST.ValueEqual (AST.ValueFun (str, vs), AST.ValueConst cv))
        let cs = Set.fold add_fun_constraint cs m.f
        let add_diff_constraint cs (cv1, cv2) =
            AST.ValueAnd (cs, AST.ValueNot (AST.ValueEqual (AST.ValueConst cv1, AST.ValueConst cv2)))
        let cs = Set.fold add_diff_constraint cs m.d
        let cs = MinimalAST.value2minimal md cs
        WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd cs) false

    let z3_formula_for_axioms_and_conjectures (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        let all_invariants = MinimalAST.invariants_to_formulas mmd.Invariants
        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd all_invariants)
        let axioms = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Axioms)
        WPR.Z3And (axioms, conjectures)

    let z3_formula_for_wpr (mmd:MinimalAST.ModuleDecl<'a,'b>) action formula uq_args =
        let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
        WPR.wpr_for_action mmd z3formula action uq_args

    [<NoComparison>]
    type SolverResult = UNSAT | UNKNOWN | SAT of Model.TypeInfos * Model.Environment

    let check_z3_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) action f timeout =
        let z3ctx = Z3Utils.build_context md
        let args_decl =
            match action with
            | None -> []
            | Some action -> (MinimalAST.find_action mmd action).Args
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx f
        let z3e = Z3Utils.build_value z3ctx z3lvars f
        match Z3Utils.check z3ctx z3e timeout with
        | Z3Utils.UNSAT -> UNSAT
        | Z3Utils.UNKNOWN -> UNKNOWN
        | Z3Utils.SAT m -> SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m)

    let check_z3_disjunction (md:AST.ModuleDecl<'a,'b>) f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars [] z3ctx f
        let z3e = Z3Utils.build_value z3ctx z3lvars f

        let declare_lvars (mmd, action, f) =
            let args_decl = (MinimalAST.find_action mmd action).Args
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx f (z3lvars, z3concrete_map)
            (mmd, action, Z3Utils.build_value z3ctx z3lvars f, (z3lvars, z3concrete_map))
        let fs = List.map declare_lvars fs

        let es = List.map (fun (_,action,es,_) -> (action, es)) fs
        match Z3Utils.check_disjunction z3ctx z3e es timeout with
        | (Z3Utils.UNSAT, _) -> (UNSAT, None)
        | (Z3Utils.UNKNOWN, _) -> (UNKNOWN, None)
        | (Z3Utils.SAT m, lst) ->
            if List.length lst > 1 then printfn "Multiple actions match this counterexample. Taking the first one."
            let action = List.head lst
            let (mmd, _, _, (z3lvars, z3concrete_map)) = List.find (fun (_,action',_,_) -> action' = action) fs
            let args_decl = (MinimalAST.find_action mmd action).Args
            (SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m), Some action)
    
    let find_counterexample_action md mmd action formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let wpr = z3_formula_for_wpr mmd action formula false
            let f = WPR.Z3And (axioms_conjectures, WPR.Z3Not wpr)
            let res = check_z3_formula md mmd (Some action) f 3000
        
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
            let fs = List.map (fun (action,mmd) -> (mmd, action, WPR.Z3Not (z3_formula_for_wpr mmd action formula false))) (Map.toList mmds)
            let res = check_z3_disjunction md axioms_conjectures fs 3000
            
            counterexample :=
                match res with
                | (UNSAT, _) | (UNKNOWN, _) -> !counterexample
                | (SAT (infos, env), Some action) ->
                    let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,_,infos,_) -> Model.cardinal infos
                    if Model.cardinal infos < former_cardinal
                    then Some (i, action, formula, infos, env)
                    else !counterexample
                | (SAT _, None) -> failwith "Can't retrieve the main action og the counterexample."

        List.iter treat_formula formulas
        !counterexample

    let generate_allowed_path_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
        action (m:Marking.Marks) other_actions prev_allowed only_terminating_run =

        // 1. Marked constraints
        let cs = z3_formula_for_constraints md mmd env m

        // 2. NOT Previous semi-generalized allowed examples
        let f = Formula.formula_from_marks env m prev_allowed true
        let f = AST.ValueNot f
        let f = MinimalAST.value2minimal md f
        let f = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd f) false

        // 3. Possibly valid run: WPRs & conjectures & axioms
        let wpr = z3_formula_for_wpr mmd action formula true
        let add_wpr acc (action,mmd) =
            let wpr = z3_formula_for_wpr mmd action formula true
            WPR.Z3And (acc, wpr)
        let wpr = List.fold add_wpr wpr other_actions
        let valid_run = WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

        // 4. If we only want a terminating run...
        let trc =
            if only_terminating_run
            then
                // We know that the run will be valid for every argument value,
                // so we can just search arguments such that the run does not satisfy the weakest precondition of 'false'
                WPR.Z3Not (WPR.wpr_for_action mmd (WPR.Z3Const (AST.ConstBool false)) action false)
            else
                WPR.Z3Const (AST.ConstBool true)

        // All together
        WPR.Z3And (WPR.Z3And(cs, trc), WPR.Z3And(f,valid_run))

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) (additional_marks:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
            let constraints = z3_formula_for_constraints md mmd env (Marking.marks_union m additional_marks)
            let funmark_constraint = z3_formula_for_constraints md mmd env m'

            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not funmark_constraint)
            match check_z3_formula md mmd None f 1000 with
            | UNSAT -> false
            | _ -> true
        let keep_funmark_if_necessary (m:Marking.Marks) (str, cvs) =
            let m' = { Marking.empty_marks with f=Set.singleton (str, cvs) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        let m = Set.fold keep_funmark_if_necessary m m.f
        // We simplify disequalities
        let keep_diff_if_necessary (m:Marking.Marks) (cv1, cv2) =
            let m' = { Marking.empty_marks with d=Set.singleton (cv1, cv2) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        Set.fold keep_diff_if_necessary m m.d

    let simplify_marks_hard (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) action formula (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) safe =
        // TODO
        // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let f = generate_allowed_path_formula md mmd env formula action m [] alt_exec (not safe)
            match check_z3_formula md mmd (Some action) f 1000 with
            | UNSAT -> false
            | _ -> true
        let keep_funmark_if_necessary (m:Marking.Marks) (str, cvs) =
            let m' = { Marking.empty_marks with f=Set.singleton (str, cvs) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        let m = Set.fold keep_funmark_if_necessary m m.f
        // We simplify disequalities
        let keep_diff_if_necessary (m:Marking.Marks) (cv1, cv2) =
            let m' = { Marking.empty_marks with d=Set.singleton (cv1, cv2) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        Set.fold keep_diff_if_necessary m m.d