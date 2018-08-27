module Determinization

    open MinimalAST

    /// <summary>
    /// Determinize a value in the format MinimalAST (the new value will still be in the format MinimalAST, but without any non-deterministic operation).
    /// Returns a tuple of the form (new fresh arguments needed in the current action, new assumptions needed on these arguments, new deterministic value).
    /// </summary>
    let rec deter_value (md:ModuleDecl<'a,'b>) v : List<VarDecl> * List<Value> * Value =
        let fail_if_assumptions_depend_on ass name =
            if List.exists (fun a -> Set.contains name (free_vars_of_value a)) ass
            then failwith "Can't determinize action (new fresh function must be introduced)!"
        let rec aux v =
            match v with
            | ValueConst c -> ([], [], ValueConst c)
            | ValueStar t ->
                let d = AST.default_var_decl (new_tmp_var ()) t
                ([d], [], ValueVar d.Name)
            | ValueVar str -> ([], [], ValueVar str)
            | ValueFun (str, vs) ->
                let (ds, ass, vs) = deter_vs md vs
                (ds, ass, ValueFun (str, vs))
            | ValueEqual (v1, v2) ->
                let (ds1, ass1, v1) = aux v1
                let (ds2, ass2, v2) = aux v2
                (ds1@ds2, ass1@ass2, ValueEqual (v1,v2))
            | ValueOr (v1, v2) ->
                let (ds1, ass1, v1) = aux v1
                let (ds2, ass2, v2) = aux v2
                (ds1@ds2, ass1@ass2, ValueOr (v1,v2))
            | ValueNot v ->
                let (ds,ass,v) = aux v
                (ds, ass, ValueNot v)
            | ValueSomeElse (d,vcond,velse) ->
                let new_d = AST.default_var_decl (new_tmp_var ()) d.Type
                let new_cond = map_vars_in_value vcond (Map.add d.Name (ValueVar new_d.Name) Map.empty)
                let (dscond, asscond, vcond) = aux new_cond
                fail_if_assumptions_depend_on asscond new_d.Name
                let (dselse, asselse, velse) = aux velse
                let assumption = ValueOr (vcond, ValueNot (ValueOr (ValueNot (ValueForall (new_d, ValueNot (vcond))), ValueNot (ValueEqual (ValueVar new_d.Name, velse)))))
                let v = ValueVar new_d.Name
                (dscond@[new_d]@dselse, asscond@[assumption]@asselse, v)
            | ValueIfElse (cond, vif, velse) ->
                let (ds1, ass1, cond) = aux cond
                let (ds2, ass2, vif) = aux vif
                let (ds3, ass3, velse) = aux velse
                (ds1@ds2@ds3, ass1@ass2@ass3, ValueIfElse (cond,vif,velse))
            | ValueForall (d, v) ->
                let (ds,ass,v) = aux v
                fail_if_assumptions_depend_on ass d.Name
                (ds,ass,ValueForall(d,v))
            | ValueInterpreted (str, _) ->
                aux (ValueStar (find_interpreted_action md str).Output)
        aux v

    and deter_vs (md:ModuleDecl<'a,'b>) vs =
        let aux (ds, ass, vs) v =
            let (ds', ass', v') = deter_value md v
            (ds@ds', ass@ass', v'::vs)
        let (ds,ass,vs) = List.fold aux ([],[],[]) vs
        (ds, ass, List.rev vs)

    let blockIfNecessary sts =
        match sts with
        | [st] -> st
        | sts -> NewBlock([],sts)

    /// <summary>
    /// Determinizes a statement in the format MinimalAST (the new statement will still be in the format MinimalAST, but without any non-deterministic operation).
    /// </summary>
    /// <param name="md">The module from which is issued the statement</param>
    /// <param name="das">Some modified (=already determinized) actions. Actions in das will be considered instead of actions in the module md.</param>
    /// <param name="st">The statement to convert.</param>
    let rec deter_st (md:ModuleDecl<'a,'b>) (das:List<ActionDecl>) st : List<VarDecl> * List<Statement> * List<ActionDecl> =
        match st with
        | AtomicGroup sts ->
            let (ds,sts,das) = deter_sts md das sts
            (ds, [AtomicGroup sts],das)

        | NewBlock (ds, sts) ->
            let (ds',sts,das) = deter_sts md das sts
            (ds', [NewBlock(ds,sts)],das)

        | VarAssign (str, v) ->
            let (ds, ass, v) = deter_value md v
            let ass = List.map (fun a -> Assume a) ass
            (ds, ass@[VarAssign (str,v)],das)

        | VarAssignAction (str, action, vs) ->
            let (ds, ass, vs) = deter_vs md vs
            let ass = List.map (fun a -> Assume a) ass
            let action = find_action md action
            let das =
                if List.exists (fun (a:ActionDecl) -> a.Name=action.Name) das
                then das
                else
                    let (ds, sts, das) = deter_st md das action.Content
                    let st = blockIfNecessary sts
                    let det_action = {action with Args=action.Args@ds ; Content=st}
                    det_action::das

            let det_action = List.find (fun (a:ActionDecl) -> a.Name=action.Name) das
            let (_,new_args) = List.splitAt (List.length action.Args) det_action.Args
            let ds' = List.map (fun (d:VarDecl) -> AST.default_var_decl (new_tmp_var ()) d.Type) new_args
            let vs' = List.map (fun (d:VarDecl) -> ValueVar d.Name) ds'
            (ds@ds', ass@[VarAssignAction(str,action.Name,vs@vs')], das)

        | FunAssign (str, decls, v) ->
            let (ds, ass, v) = deter_value md v
            let ass = List.map (fun a -> Assume a) ass
            (ds, ass@[FunAssign (str, decls, v)], das)

        | IfElse (v, sif, selse) ->
            let (ds, ass, v) = deter_value md v
            let ass = List.map (fun a -> Assume a) ass
            let (dsi, sif, das) = deter_st md das sif
            let (dse, selse, das) = deter_st md das selse
            (ds@dsi@dse, ass@[IfElse (v, blockIfNecessary sif, blockIfNecessary selse)], das)

        | IfSomeElse (d, cond, sif, selse) ->
            let sif = NewBlock([d], (VarAssign (d.Name, ValueSomeElse (d, cond, ValueStar d.Type)))::[sif])
            let (dsi, sif, das) = deter_st md das sif
            let (dse, selse, das) = deter_st md das selse

            let cond = ValueNot (ValueForall (d, ValueNot (cond)))
            let (ds, ass, cond) = deter_value md cond
            let ass = List.map (fun a -> Assume a) ass
            (ds@dsi@dse, ass@[IfElse(cond, blockIfNecessary sif, blockIfNecessary selse)], das)

        | Assert v ->
            let (ds, ass, v) = deter_value md v
            let ass = List.map (fun a -> Assume a) ass
            (ds, ass@[Assert v], das)
        
        | Assume v ->
            let (ds, ass, v) = deter_value md v
            let ass = List.map (fun a -> Assume a) ass
            (ds, ass@[Assume v], das)
                
    and deter_sts (md:ModuleDecl<'a,'b>) (das:List<ActionDecl>) sts =
        let aux (ds, sts, das) st =
            let (ds', sts', das) = deter_st md das st
            (ds@ds', sts@sts', das)
        List.fold aux ([],[],das) sts

    /// <summary>
    /// Determinizes an action.
    /// </summary>
    /// <param name="md">The module from which is issued the action.</param>
    /// <param name="name">The full name of the action.</param>
    let determinize_action (md:ModuleDecl<'a,'b>) name =
        let action = find_action md name
        let (ds, sts, das) = deter_st md [] action.Content
        let st = blockIfNecessary sts
        let det_action = {action with Args=action.Args@ds ; Content=st}
        let actions = det_action::das
        { md with Actions=actions }

