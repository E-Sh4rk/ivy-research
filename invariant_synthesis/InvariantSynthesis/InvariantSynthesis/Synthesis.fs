﻿module Synthesis

    open AST
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffMarks = Set<ConstValue * ConstValue>

    type Marks = { f : FunMarks; v : VarMarks; d : DiffMarks }

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }

    let marks_count m =
        (Set.count m.f) + (Set.count m.v) + (Set.count m.d)

    let marks_map op1 op2 op3 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        let ds = Seq.map (fun m -> m.d) ms
        { f = op1 fs ; v = op2 vs ; d = op3 ds }
    
    let marks_union_many = marks_map Set.unionMany Set.unionMany Set.unionMany    
    let marks_inter_many = marks_map Set.intersectMany Set.intersectMany Set.intersectMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_inter m1 m2 = marks_inter_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f = Set.difference m1.f m2.f ; v = Set.difference m1.v m2.v ; d = Set.difference m1.d m2.d }

    let rec marks_for_value infos env v : ConstValue * Marks =
        match v with
        | ValueConst c -> (c, empty_marks)
        | ValueVar str -> (evaluate_value env (ValueVar str), { empty_marks with v=Set.singleton str })
        | ValueFun (str, values) ->
            let res = List.map (marks_for_value infos env) values
            let (cvs, ms) = List.unzip res
            let m = marks_union_many ms
            let vs = List.map (fun cv -> ValueConst cv) cvs
            (evaluate_value env (ValueFun (str, vs)), { m with f = Set.add (str, cvs) m.f })

    // Return type : (formula value, important elements, universally quantified important elements)
    let rec marks_for_formula infos env f : bool * Marks * Marks =
        match f with
        | Const  b -> (b, empty_marks, empty_marks)
        | Equal (v1, v2) ->
            let (cv1, m1) = marks_for_value infos env v1
            let (cv2, m2) = marks_for_value infos env v2
            let m = marks_union m1 m2
            if value_equal infos cv1 cv2 then (true, m, empty_marks)
            else
                let d' =
                    if Set.contains (cv1, cv2) m.d || Set.contains (cv2, cv1) m.d
                    then m.d else Set.add (cv1, cv2) m.d
                (false, { m with d = d' }, empty_marks)
        | Or (f1, f2) ->
            let (b1, m1, um1) = marks_for_formula infos env f1
            let (b2, m2, um2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false -> (false, marks_union m1 m2, marks_union um1 um2)
            | true, false -> (true, m1, um1)
            | false, true -> (true, m2, um2)
            | true, true when marks_count um1 > marks_count um2 -> (true, m2, um2)
            | true, true -> (true, m1, um1)
        | And (f1, f2) ->
            (*let (b1, m1, um1) = marks_for_formula infos env f1
            let (b2, m2, um2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false when marks_count um1 > marks_count um2 -> (false, m2, um2)
            | false, false -> (false, m1, um1)
            | true, false -> (false, m2, um2)
            | false, true -> (false, m1, um1)
            | true, true -> (true, marks_union m1 m2, marks_union um1 um2)*)
            marks_for_formula infos env (Not (Or (Not f1, Not f2)))
        | Not f ->
            let (b,m,um) = marks_for_formula infos env f
            (not b, m, um)
        | Forall (decl, f) ->
            let marks_with value =
                let v' = Map.add decl.Name value env.v
                let (b, m, um) = marks_for_formula infos { env with v=v' } f
                let m = { m with v = Set.remove decl.Name m.v }
                let um = { um with v = Set.remove decl.Name um.v }
                (b, m, um)
            let values = all_values infos decl.Type
            let all_possibilities = Seq.map marks_with values
            if Seq.forall (fun (b,_,_) -> b) all_possibilities
            then
                // Important constraints are universally quantified...
                // Common properties stay in m, other properties move to um
                let ms = Seq.map (fun (_,m,_) -> m) all_possibilities
                let ums = Seq.map (fun (_,_,um) -> um) all_possibilities
                let m = marks_inter_many ms
                let um1 = marks_union_many ums
                let um2 = marks_diff (marks_union_many ms) m
                (true, m, marks_union um1 um2)
            else
                // We pick one constraint that breaks the forall
                let min_count (mb, mm, mum) (b, m, um) = if marks_count um < marks_count mm then (b, m, um) else (mb, mm, mum)
                let interesting_possibilities = Seq.filter (fun (b, _, _) -> not b) all_possibilities
                let (_, m, um) = Seq.fold min_count (Seq.head interesting_possibilities) interesting_possibilities
                (false, m, um)
        | Exists (decl, f) ->
            marks_for_formula infos env (Not (Forall (decl, Not f)))
