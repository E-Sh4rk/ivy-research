module Marking

    open MinimalAST
    open Trace
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffConstraint = Set<ConstValue * ConstValue>

    /// <summary>
    /// Some marks:
    /// - f contains marks that point to some constraints of the form fun(arg)=concrete_val
    /// - v contains marks that point to some constraints of the form var=concrete_val
    /// - d contains marks that point to some constraints of the form concrete_val<>concrete_val
    /// </summary>
    type Marks = { f : FunMarks; v : VarMarks; d: DiffConstraint }

    /// <summary>
    /// Type used to associate to each model-dependant FunMark ('um.f' below) the subset of their arguments that are marked in an universally quantified way.
    /// Every model-dependant FunMark should have at least one such argument (otherwise it would not be model-dependant).
    /// </summary>
    type UniversalFunMarksInfo = Map<string * List<ConstValue>,Set<int>>
    /// <summary>
    /// Additional data about the markings:
    /// 'md' means 'model-dependant' and 'ufmi' contains additional data about the model dependant FunMarks.
    /// </summary>
    type AdditionalData = { md : bool ; ufmi : UniversalFunMarksInfo }

    /// <summary>
    /// A config is a tuple (m,um,ad) where:
    /// - 'm' contains the list of non-model-dependant marks
    /// - 'um' contains the list of model-dependant marks
    /// - 'ad' contains additional data
    /// </summary>
    type Config = Marks * Marks * AdditionalData

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }
    let empty_ad = { md = false ; ufmi = Map.empty }
    let empty_config:Config = (empty_marks, empty_marks, empty_ad)

    let is_model_dependent_type t =
        match t with
        | AST.Void -> false
        | AST.Bool -> false
        | AST.Uninterpreted _ -> true
        | AST.Enumerated _ -> false

    let is_model_dependent_value cv =
        match cv with
        | AST.ConstVoid -> false
        | AST.ConstBool _ -> false
        | AST.ConstInt _ -> true
        | AST.ConstEnumerated _ -> false

    /// <summary>
    /// Returns all potential disequalities among the elements of a type.
    /// </summary>
    let all_potential_diffs_for_type types infos t =
        let couples = Model.all_values_ext types infos [t;t]
        let couples = Seq.map Helper.lst_to_couple couples
        let couples = Seq.filter (fun (a,b) -> not (AST.value_equal a b)) couples
        Set.ofSeq couples 

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

    let remove_all_var_marks m = { m with v = Set.empty }
    
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

    let config_is_included cfg1 cfg2 =
        config_union cfg1 cfg2 = cfg2

    let remove_worst_configs cfgs =
        let is_strictly_included cfg1 cfg2 =
            cfg1 <> cfg2 && config_is_included cfg1 cfg2
        let remove_worse acc cfg =
            Set.filter (fun cfg' -> not (is_strictly_included cfg cfg')) acc
        Set.fold remove_worse cfgs cfgs

    let bool_of_cv cv =
        match cv with
        | AST.ConstBool b -> b
        | _ -> raise TypeError

    let rec union_of_cfg_possibilities cfgs =
        match cfgs with
        | [] -> Set.singleton empty_config
        | cfgs::cfgss ->
            let res = union_of_cfg_possibilities cfgss
            let res = Set.map (fun cfg -> Set.map (fun cfg' -> config_union cfg cfg') cfgs) res
            remove_worst_configs (Set.unionMany res)

    /// <summary>
    /// Compute many different configs for a value. Each config is sufficient to ensure that the evaluation of the value v is always the same.
    /// </summary>
    /// <param name="mdecl">The module from which is issued the value v</param>
    /// <param name="infos">Information about the types</param>
    /// <param name="env">The current environment (=state)</param>
    /// <param name="uvar">The list of variables that are currently universally quantified, or more generally, that can take a value in an arbitrary large range</param>
    /// <param name="v">The value on which we compute the marks</param>
    let rec marks_for_value mdecl infos env uvar v : ConstValue * Set<Marks * Marks * AdditionalData> =
        let (v, cfgs) =
            match v with
            | ValueConst c -> (c, Set.singleton empty_config)
            | ValueStar t -> (AST.type_default_value mdecl.Types t, Set.singleton empty_config)
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
                let eval = AST.value_equal cv1 cv2
                let cfgs = union_of_cfg_possibilities [cfgs1;cfgs2]                
                let treat_cfg cfg =
                    let (m,um,ad) = cfg
                    if eval then cfg
                    else if ad.md
                    then (m, add_diff_constraint um cv1 cv2, ad)
                    else (add_diff_constraint m cv1 cv2, um, ad)
                (AST.ConstBool eval, Set.map treat_cfg cfgs)
            | ValueOr (v1, v2) ->
                let (cv1, cfgs1) = marks_for_value mdecl infos env uvar v1
                let (cv2, cfgs2) = marks_for_value mdecl infos env uvar v2
                let eval = (bool_of_cv cv1) || (bool_of_cv cv2)
                let cfgs =
                    match cv1, cv2 with
                    | AST.ConstBool false, AST.ConstBool false -> union_of_cfg_possibilities [cfgs1;cfgs2]
                    | AST.ConstBool true, AST.ConstBool false -> cfgs1
                    | AST.ConstBool false, AST.ConstBool true -> cfgs2
                    | AST.ConstBool true, AST.ConstBool true -> Set.union cfgs1 cfgs2
                    | _, _ -> raise TypeError
                (AST.ConstBool eval, cfgs)
            | ValueNot v ->
                let (cv,cfgs) = marks_for_value mdecl infos env uvar v
                (value_not cv, cfgs)
            | ValueSomeElse (d,f,v) ->
                match if_some_value mdecl infos env d f with
                | Some cv ->
                    (* NOTE: In this case, we may also ensure that all other value don't satisfy the predicate.
                    However, it would make the resulting invariant way more complex.
                    If the user want to ensure that there is only one possible value, he can add an assertion for that.
                    More generally, non-deterministic operations should be accompagnied with assertions and/or assumptions if necessary. *)
                    let is_uvar = is_model_dependent_type d.Type && not (Set.isEmpty uvar) 
                    let uvar = if is_uvar then Set.add d.Name uvar else uvar
                    let (_,cfgs) = marks_for_value_with mdecl infos env uvar f [d.Name] [cv]
                    (cv,cfgs)
                | None -> 
                    let (_,cfgs1) = marks_for_value mdecl infos env uvar (ValueForall (d, ValueNot f))
                    let (cv,cfgs2) = marks_for_value mdecl infos env uvar v
                    (cv, union_of_cfg_possibilities [cfgs1;cfgs2])
            | ValueIfElse (f, v1, v2) ->
                let (b, cfgs) = marks_for_value mdecl infos env uvar f
                let (res, cfgs') =
                    match b with
                    | AST.ConstBool true -> marks_for_value mdecl infos env uvar v1
                    | AST.ConstBool false -> marks_for_value mdecl infos env uvar v2
                    | _ -> raise TypeError
                (res, union_of_cfg_possibilities [cfgs;cfgs'])
            | ValueForall (decl, v) ->
                let is_uvar = 
                    is_model_dependent_type decl.Type && 
                    (not (Set.isEmpty uvar) || evaluate_value mdecl infos env (ValueForall (decl, v)) = AST.ConstBool true)
                let uvar = if is_uvar then Set.add decl.Name uvar else uvar
                let values = List.ofSeq (Model.all_values mdecl.Types infos decl.Type)
                let all_possibilities = List.map (fun cv -> marks_for_value_with mdecl infos env uvar v [decl.Name] [cv]) values
                if Seq.forall (fun (b,_) -> b = AST.ConstBool true) all_possibilities
                then
                    // We mix all contraints (some will probably be model-dependent)
                    let all_possibilities = List.map (fun (_,cfgs) -> cfgs) all_possibilities
                    (AST.ConstBool true, union_of_cfg_possibilities all_possibilities)
                else
                    // We pick one constraint that breaks the forall
                    let possibilities = List.filter (fun (b, _) -> b = AST.ConstBool false) all_possibilities
                    let possibilities = Set.unionMany (List.map (fun (_,cfgs) -> cfgs) possibilities)
                    (AST.ConstBool false, possibilities)
            | ValueInterpreted (str, vs) ->
                let res = List.map (marks_for_value mdecl infos env uvar) vs
                let (cvs, cfgs) = List.unzip res
                let eval = (find_interpreted_action mdecl str).Effect infos env cvs
                (eval, union_of_cfg_possibilities cfgs)
        (v, remove_worst_configs cfgs)

    and marks_for_value_with mdecl infos (env:Model.Environment) uvar v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        let (v, cfgs) = marks_for_value mdecl infos {env with v=v'} uvar v
        (v, Set.map (fun cfg -> List.fold remove_var_marks cfg names) cfgs)

    let best_cfg cfgs =
        Helper.seq_min is_better_config cfgs

    ////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// Same as Interpreter.leave_block, but for configs.
    /// </summary>
    let config_leave_block (m,um,ad) lvars (old_m,old_um,_) =
        let marks_leave_block m old_m : Marks =
            let rollback acc (decl:VarDecl) =
                if Set.contains decl.Name old_m.v
                then Set.add decl.Name acc
                else Set.remove decl.Name acc
            { m with v=List.fold rollback m.v lvars }
        (marks_leave_block m old_m, marks_leave_block um old_um, ad)

    /// <summary>
    /// Same as Interpreter.enter_new_block, but for configs.
    /// </summary>
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

    /// <summary>
    /// Backpropagate a config through a trace, so we have the corresponding config BEFORE the execution of the statements in the trace.
    /// </summary>
    /// <param name="mdecl">The module from which the trace is issued</param>
    /// <param name="infos">Information about the types</param>
    /// <param name="ignore_asserts">True if assertions must be ignored</param>
    /// <param name="ignore_assumes">True if assumptions must be ignored</param>
    /// <param name="tr">The trace containing the statements to go through</param>
    /// <param name="cfg">The config to backpropagate</param>
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
                | TrFunAssign ((env,_,_), str, ds, v) ->
                    // Retrieve the involved marks and remove them
                    let (_,_,ad) = cfg
                    let (m_marks,um_marks) = fun_marks cfg str
                    let cfg = Set.fold (fun cfg (str,vs) -> remove_fun_marks cfg str vs) cfg (Set.union m_marks um_marks)
                    let m_marks = Set.map (fun (_,cvs) -> cvs) m_marks
                    let um_marks = Set.map (fun (_,cvs) -> cvs) um_marks
                        
                    // Adding marks for the marked instances of v
                    let compute_marks_for model_dependent uvs =
                        let uvars =
                            if model_dependent
                            then
                                let md_qvars = List.mapi (fun i uv -> (i,uv)) ds
                                let ufmi = get_ufmi_entry ad str uvs
                                let md_qvars = List.filter (fun (i,d:VarDecl) -> is_model_dependent_type d.Type && Set.contains i ufmi) md_qvars
                                List.map (fun (_,d:VarDecl) -> d.Name) md_qvars |> Set.ofList
                            else Set.empty
                        marks_for_value_with mdecl infos env uvars v (List.map (fun (d:VarDecl) -> d.Name) ds) uvs
                    let add_marks_for_all model_dependent uvs cfgs =
                        let aux acc uvs =
                            let (_,cfgs) = compute_marks_for model_dependent uvs
                            union_of_cfg_possibilities [acc; cfgs]
                        Set.fold aux cfgs uvs

                    let cfgs = add_marks_for_all false m_marks (Set.singleton cfg)
                    let cfgs = add_marks_for_all true um_marks cfgs
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
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
                            (* NOTE: See note for ValueSomeElse. *)
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

