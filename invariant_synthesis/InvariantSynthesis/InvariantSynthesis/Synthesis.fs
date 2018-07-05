﻿module Synthesis

    open MinimalAST
    open Trace
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffConstraint = Set<ConstValue * ConstValue> // We don't impose disequality if is not necessary

    type Marks = { f : FunMarks; v : VarMarks; d: DiffConstraint }

    // Indicate for each umark which arguments are potentially model-dependent
    type UniversalFunMarksInfo = Map<string * List<ConstValue>,Set<int>>
    type AdditionalData = { md : bool ; ufmi : UniversalFunMarksInfo } // md means model-dependent

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }
    let empty_ad = { md = false ; ufmi = Map.empty }
    let empty_config = (empty_marks, empty_marks, empty_ad)
    // A config (m,um,ad) is composed of alist of marks m, a list of model-dependent marks um, additional data ad

    let is_model_dependent_type t =
        match t with
        | AST.Void -> false
        | AST.Bool -> false
        | AST.Uninterpreted _ -> true

    let is_model_dependent_value cv =
        match cv with
        | AST.ConstVoid -> false
        | AST.ConstBool _ -> false
        | AST.ConstInt _ -> true

    let marks_count m =
        (Set.count m.f) + (Set.count m.v) + (Set.count m.d)

    let marks_reduce op1 op2 op3 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        let ds = Seq.map (fun m -> m.d) ms
        { f = op1 fs ; v = op2 vs ; d = op3 ds }

    let ad_reduce op1 op2 ads : AdditionalData =
        let mds = Seq.map (fun ad -> ad.md) ads
        let ufmis = Seq.map (fun ad -> ad.ufmi) ads
        { md = op1 mds ; ufmi = op2 ufmis }
    
    let marks_union_many = marks_reduce Set.unionMany Set.unionMany Set.unionMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f=Set.difference m1.f m2.f ; v=Set.difference m1.v m2.v; d=Set.difference m1.d m2.d }

    let ad_union_many =
        let union_ufmis ufmis =
            let aux acc ufmi =
                let merge_key acc k v =
                    let s =
                        match Map.tryFind k acc with
                        | None -> v
                        | Some s -> Set.union s v
                    Map.add k s acc
                Map.fold merge_key acc ufmi
            Seq.fold aux Map.empty ufmis
        ad_reduce (Seq.exists Helper.identity) union_ufmis
    let ad_union ad1 ad2 = ad_union_many ([ad1;ad2] |> List.toSeq)

    let config_union (m1,um1,ad1) (m2,um2,ad2) =
        (marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)

    let config_union_many configs =
        Seq.fold (fun cfg1 cfg2 -> config_union cfg1 cfg2) empty_config configs

    let is_better_config (m1, um1, ad1) (m2, um2, ad2) =
        if not ad1.md && ad2.md
        then true
        else if ad1.md && not ad2.md
        then false
        else if marks_count um1 < marks_count um2
        then true
        else if marks_count um1 > marks_count um2
        then false
        else if marks_count m1 < marks_count m2
        then true
        else false

    let add_diff_constraint m cv1 cv2 =
        let d' = Set.add (cv1, cv2) m.d
        let d' = Set.add (cv2, cv1) d'
        { m with d=d' }

    let get_ufmi_entry (ad:AdditionalData) str cvs =
         match Map.tryFind (str, cvs) ad.ufmi with
         | None -> Set.empty
         | Some s -> s

    let add_ufmi_entry (ad:AdditionalData) str cvs arg =
        let s = get_ufmi_entry ad str cvs
        let s = Set.add arg s
        { ad with ufmi = Map.add (str, cvs) s ad.ufmi }

    let remove_ufmi_entry (ad:AdditionalData) str cvs =
        { ad with ufmi = Map.remove (str, cvs) ad.ufmi }

    let is_var_marked (m, um, _) var =
        (Set.contains var m.v) || (Set.contains var um.v)
    
    let remove_var_marks (m, um, ad) var : Marks * Marks * AdditionalData =
        ({m with v = Set.remove var m.v}, {um with v = Set.remove var um.v}, ad)

    let config_is_included (m1,um1,ad1) (m2,um2,ad2) =
        let ad_is_included (ad1:AdditionalData) (ad2:AdditionalData) =
            if ad1.md && not ad2.md
            then false
            else
                let is_included (str, cvs) is =
                    match Map.tryFind (str, cvs) ad2.ufmi with
                    | None -> Set.isEmpty is
                    | Some is' -> Set.isSubset is is' 
                Map.forall is_included ad1.ufmi
        let marks_are_included m1 m2 =
            Set.isSubset m1.f m2.f && Set.isSubset m1.v m2.v
        ad_is_included ad1 ad2 && marks_are_included m1 m2 && marks_are_included um1 um2

    let remove_worst_configs cfgs =
        let is_strictly_included cfg1 cfg2 =
            cfg1 <> cfg2 && config_is_included cfg1 cfg2
        let remove_worse acc cfg =
            Set.filter (fun cfg' -> not (is_strictly_included cfg cfg')) acc
        Set.fold remove_worse cfgs cfgs

    exception InvalidOperation
    let bool_of_cv cv =
        match cv with
        | AST.ConstBool b -> b
        | _ -> raise TypeError

    // uvar: variables that can browse an arbitrary large range (depending on the model)
    let rec marks_for_value mdecl infos env uvar v : ConstValue * Set<Marks * Marks * AdditionalData> =
        let (v, cfgs) =
            match v with
            | ValueConst c -> (c, Set.singleton empty_config)
            | ValueStar t -> (AST.type_default_value t, Set.singleton empty_config)
            | ValueVar str ->
                let eval = evaluate_value mdecl infos env (ValueVar str)
                if Set.contains str uvar
                then (eval, Set.singleton (empty_marks, { empty_marks with v=Set.singleton str }, { empty_ad with md=true }))
                else (eval, Set.singleton ({ empty_marks with v=Set.singleton str }, empty_marks, empty_ad))
            | ValueFun (str, values) ->
                let res = List.map (marks_for_value mdecl infos env uvar) values
                let (cvs, cfgs) = List.unzip res
                let vs = List.map (fun cv -> ValueConst cv) cvs
                let eval = evaluate_value mdecl infos env (ValueFun (str, vs))
                let cfgs = Helper.all_choices_combination cfgs |> Seq.toList
                let treat_cfgs cfgs =
                    let (m,um,ad) = config_union_many cfgs
                    if ad.md
                    then
                        let add_entry_if_needed (i, acc) (_,_,ad:AdditionalData) =
                            if ad.md
                            then (i+1, add_ufmi_entry acc str cvs i)
                            else (i+1, acc)
                        let (_,ad) = List.fold add_entry_if_needed (0, ad) cfgs
                        (m, { um with f = Set.add (str, cvs) um.f }, ad)
                    else
                        ({ m with f = Set.add (str, cvs) m.f }, um, ad)
                (eval, List.map treat_cfgs cfgs |> Set.ofList)
            | ValueEqual (v1, v2) ->
                let (cv1, cfgs1) = marks_for_value mdecl infos env uvar v1
                let (cv2, cfgs2) = marks_for_value mdecl infos env uvar v2
                let cfgs = Helper.all_choices_combination [cfgs1;cfgs2]  |> Seq.toList
                let eval = AST.value_equal cv1 cv2
                let treat_cfg cfg =
                    let (cfg1, cfg2) = Helper.lst_to_couple cfg
                    let (m,um,ad) = config_union cfg1 cfg2
                    if eval then (m, um, ad)
                    else if ad.md
                    then (m, add_diff_constraint um cv1 cv2, ad)
                    else (add_diff_constraint m cv1 cv2, um, ad)
                (AST.ConstBool eval, List.map treat_cfg cfgs |> Set.ofList)
            | ValueOr (v1, v2) ->
                let (cv1, cfgs1) = marks_for_value mdecl infos env uvar v1
                let (cv2, cfgs2) = marks_for_value mdecl infos env uvar v2
                let cfgs = Helper.all_choices_combination [cfgs1;cfgs2] |> Seq.toList
                let eval = (bool_of_cv cv1) || (bool_of_cv cv2)
                let treat_cfg cfg =
                    let (cfg1, cfg2) = Helper.lst_to_couple cfg
                    match cv1, cv2 with
                    | AST.ConstBool false, AST.ConstBool false -> [config_union cfg1 cfg2]
                    | AST.ConstBool true, AST.ConstBool false -> [cfg1]
                    | AST.ConstBool false, AST.ConstBool true -> [cfg2]
                    | AST.ConstBool true, AST.ConstBool true -> [cfg1 ; cfg2]
                    | _, _ -> raise TypeError
                (AST.ConstBool eval, List.concat (List.map treat_cfg cfgs) |> Set.ofList)
            | ValueNot v ->
                let (cv,cfgs) = marks_for_value mdecl infos env uvar v
                (value_not cv, cfgs)
            | ValueSomeElse (d,f,v) ->
                match if_some_value mdecl infos env d f with
                | Some cv ->
                    (* NOTE: See note for IfSomeElse statement. *)
                    let is_uvar = is_model_dependent_type d.Type && not (Set.isEmpty uvar) 
                    let uvar = if is_uvar then Set.add d.Name uvar else uvar
                    let (_,cfgs) = marks_for_value_with mdecl infos env uvar f [d.Name] [cv]
                    (cv,cfgs)
                | None -> 
                    let (_,cfgs1) = marks_for_value mdecl infos env uvar (ValueForall (d, ValueNot f))
                    let (cv,cfgs2) = marks_for_value mdecl infos env uvar v
                    let cfgs = Helper.all_choices_combination [cfgs1;cfgs2] |> Seq.toList
                    (cv, List.map config_union_many cfgs |> Set.ofList)
            | ValueIfElse (f, v1, v2) ->
                let (b, cfgs) = marks_for_value mdecl infos env uvar f
                let (res, cfgs') =
                    match b with
                    | AST.ConstBool true -> marks_for_value mdecl infos env uvar v1
                    | AST.ConstBool false -> marks_for_value mdecl infos env uvar v2
                    | _ -> raise TypeError
                let cfgs = Helper.all_choices_combination [cfgs;cfgs'] |> Seq.toList
                (res, List.map config_union_many cfgs |> Set.ofList)
            | ValueForall (decl, v) ->
                let is_uvar = 
                    is_model_dependent_type decl.Type && 
                    (not (Set.isEmpty uvar) || evaluate_value mdecl infos env (ValueForall (decl, v)) = AST.ConstBool true)
                let uvar = if is_uvar then Set.add decl.Name uvar else uvar
                let values = List.ofSeq (Model.all_values infos decl.Type)
                let all_possibilities = List.map (fun cv -> marks_for_value_with mdecl infos env uvar v [decl.Name] [cv]) values
                if Seq.forall (fun (b,_) -> b = AST.ConstBool true) all_possibilities
                then
                    // We mix all contraints (some will probably be model-dependent)
                    let cfgs = Helper.all_choices_combination (List.map (fun (_,cfgs) -> cfgs) all_possibilities) |> Seq.toList
                    (AST.ConstBool true, List.map config_union_many cfgs |> Set.ofList)
                else
                    // We pick one constraint that breaks the forall
                    let possibilities = List.filter (fun (b, _) -> b = AST.ConstBool false) all_possibilities
                    let possibilities = Set.unionMany (List.map (fun (_,cfgs) -> cfgs) possibilities)
                    (AST.ConstBool false, possibilities)
            | ValueInterpreted (str, vs) ->
                let res = List.map (marks_for_value mdecl infos env uvar) vs
                let (cvs, cfgs) = List.unzip res
                let cfgs = Helper.all_choices_combination cfgs |> Seq.toList
                let eval = (find_interpreted_action mdecl str).Effect infos env cvs
                (eval, List.map config_union_many cfgs |> Set.ofList)
        (v, remove_worst_configs cfgs)

    and marks_for_value_with mdecl infos (env:Model.Environment) uvar v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        let (v, cfgs) = marks_for_value mdecl infos {env with v=v'} uvar v
        (v, Set.map (fun cfg -> List.fold remove_var_marks cfg names) cfgs)

    let union_of_cfg_possibilities cfgs =
        let cfgs = Helper.all_choices_combination cfgs |> Seq.toList
        let cfgs = List.map config_union_many cfgs |> Set.ofList
        remove_worst_configs cfgs

    let best_cfg cfgs =
        Helper.seq_min is_better_config cfgs

    ////////////////////////////////////////////////////////////////////////////

    // Some utility functions
    let config_leave_block (m,um,ad) lvars (old_m,old_um,_) =
        let marks_leave_block m old_m : Marks =
            let rollback acc (decl:VarDecl) =
                if Set.contains decl.Name old_m.v
                then Set.add decl.Name acc
                else Set.remove decl.Name acc
            { m with v=List.fold rollback m.v lvars }
        (marks_leave_block m old_m, marks_leave_block um old_um, ad)

    let config_enter_block (m,um,ad) lvars =
        let marks_enter_block m : Marks =
            let rm acc (decl:VarDecl) = Set.remove decl.Name acc
            { m with v=List.fold rm m.v lvars }
        (marks_enter_block m, marks_enter_block um, ad)
    
    let remove_fun_marks (m, um, ad) str cvs : Marks * Marks * AdditionalData =
        ({m with f = Set.remove (str,cvs) m.f},
            {um with f = Set.remove (str,cvs) um.f},
            remove_ufmi_entry ad str cvs)

    let fun_marks (m,um,_) str =
        let fun_marks_for (m:Marks) =
            Set.filter (fun (str',_) -> str = str') m.f
        (fun_marks_for m, fun_marks_for um)

    ////////////////////////////////////////////////////////////////////////////

    let rec marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg =
        let rec aux group_trs cfg =
            if List.isEmpty group_trs then cfg
            else
                let tr = List.head group_trs
                let group_trs = List.tail group_trs
                match tr with
                | TrAtomicGroup (_, trs) ->
                    let cfg = aux (List.rev trs) cfg
                    aux group_trs cfg
                | TrNewBlock (_, decls, trs) ->
                    let cfg' = config_enter_block cfg decls
                    let cfg' = marks_before_statements mdecl infos ignore_asserts ignore_assumes trs cfg'
                    aux group_trs (config_leave_block cfg' decls cfg)
                | TrVarAssign ((env,_,_), str, v) ->
                    let marked = is_var_marked cfg str
                    let cfg = remove_var_marks cfg str
                    let cfgs =
                        if marked
                        then
                            let (_,cfgs) = marks_for_value mdecl infos env Set.empty v
                            union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        else Set.singleton cfg
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
                | TrVarAssignAction ((env,_,b), str, input, output, args, tr) ->
                    let (marked, cfg) =
                        if b then
                            (is_var_marked cfg str, remove_var_marks cfg str)
                        else (false, cfg)

                    let cfg' = config_enter_block cfg (output::input)
                    let cfg' =
                        let (m, um, ad) = cfg'
                        if marked then
                            ({ m with v = Set.add output.Name m.v }, um, ad)
                        else (m, um, ad)

                    let cfg' = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg'
                    let args_marks = List.map (is_var_marked cfg') (List.map (fun (decl:VarDecl) -> decl.Name) input)
                    let cfg = config_leave_block cfg' (output::input) cfg
            
                    let args = List.zip args args_marks
                    let (args, _) = List.unzip (List.filter (fun (_,marked) -> marked) args)
                    let (_, args_cfgs) = List.unzip (List.map (marks_for_value mdecl infos env Set.empty) args)
                    let cfgs = union_of_cfg_possibilities ((Set.singleton cfg)::args_cfgs)
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
                | TrFunAssign ((env,_,_), str, hvs, v) ->
                    // Get rid of expressions in arguments
                    let (vs, ds) = separate_hvals hvs
                    let added_names = List.init (List.length vs) (fun _ -> new_tmp_var ())
                    let existing_names = List.map (fun (d:VarDecl) -> d.Name) ds
                    let names = reconstruct_hvals hvs added_names existing_names
                    let decls = List.map2 (fun str t -> AST.default_var_decl str t) names (find_function mdecl str).Input

                    // Retrieve the involved marks and remove them
                    let (_,_,ad) = cfg
                    let (m_marks,um_marks) = fun_marks cfg str
                    let cfg = Set.fold (fun cfg (str,vs) -> remove_fun_marks cfg str vs) cfg (Set.union m_marks um_marks)
                    let m_marks = Set.map (fun (_,cvs) -> cvs) m_marks
                    let um_marks = Set.map (fun (_,cvs) -> cvs) um_marks

                    let proceed_with_permutation p =
                        // Building v
                        let p = Helper.permutation_to_fun p
                        let add_condition acc name vcond =
                            let vcond = ValueEqual (vcond, ValueVar name)
                            ValueIfElse (vcond, acc, ValueFun (str, List.map (fun str -> ValueVar str) names))
                        let v = List.fold2 add_condition v (List.permute p added_names) (List.permute p vs)
                        
                        // Adding marks for the marked instances of v
                        let compute_marks_for model_dependent uvs =
                            let uvars =
                                if model_dependent
                                then
                                    let md_qvars = List.mapi (fun i uv -> (i,uv)) decls
                                    let ufmi = get_ufmi_entry ad str uvs
                                    let md_qvars = List.filter (fun (i,d:VarDecl) -> is_model_dependent_type d.Type && Set.contains i ufmi) md_qvars
                                    List.map (fun (_,d:VarDecl) -> d.Name) md_qvars |> Set.ofList
                                else Set.empty
                            marks_for_value_with mdecl infos env uvars v (List.map (fun (d:VarDecl) -> d.Name) decls) uvs
                        let add_marks_for_all model_dependent uvs cfgs =
                            let aux acc uvs =
                                let (_,cfgs) = compute_marks_for model_dependent uvs
                                union_of_cfg_possibilities [acc; cfgs]
                            Set.fold aux cfgs uvs

                        let cfgs = add_marks_for_all false m_marks (Set.singleton cfg)
                        let cfgs = add_marks_for_all true um_marks cfgs
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs

                    let permutations = Helper.all_permutations (List.length vs) |> Seq.toList
                    let cfgs = List.map proceed_with_permutation permutations
                    best_cfg cfgs
                | TrIfElse ((env,_,_), v, tr) ->
                    let cfg = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
                    let (_,cfgs) = marks_for_value mdecl infos env Set.empty v
                    let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
                | TrIfSomeElse ((env,_,_), cv, decl, v, tr) ->
                    match cv with
                    | Some _ ->
                        let cfg' = config_enter_block cfg [decl]
                        let cfg' = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg'
                        let (_, cfgs) =
                            if is_var_marked cfg' decl.Name
                            then marks_for_value mdecl infos (initial_env tr) Set.empty v
                            (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                               However, it is a different problem than garanteeing the invariant value,
                               since we are bound to an execution (maybe there is no uniqueness in this execution).
                               Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                               An assertion can also be added by the user to ensure this uniqueness. *)
                            else marks_for_value mdecl infos env Set.empty (ValueNot (ValueForall (decl, ValueNot v)))
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg';cfgs]
                        let cfgs = Set.map (fun cfg' -> aux group_trs (config_leave_block cfg' [decl] cfg)) cfgs
                        best_cfg cfgs
                    | None ->
                        let cfg = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
                        let (_,cfgs) = marks_for_value mdecl infos env Set.empty (ValueForall (decl, ValueNot v))
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
                | TrAssert ((env,_,b),v) ->
                    // If ignore_asserts is true, we ignore satisfied assertions
                    if ignore_asserts && b then
                        aux group_trs cfg
                    else
                        let (_, cfgs) = marks_for_value mdecl infos env Set.empty v
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
                | TrAssume ((env,_,b),v) ->
                    // If ignore_assumes is true, we ignore satisfied assumptions
                    if ignore_assumes && b then
                        aux group_trs cfg
                    else
                        let (_, cfgs) = marks_for_value mdecl infos env Set.empty v
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
        aux [tr] cfg

    // Statements are analysed in reverse order
    and marks_before_statements mdecl infos ignore_asserts ignore_assumes trs cfg =
        let aux cfg tr =
            marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
        List.fold aux cfg (List.rev trs)

