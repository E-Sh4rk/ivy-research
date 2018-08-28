module InterpretedExpr

    open AST

    let order_type_elts infos (env:Model.Environment) t =
        let elts = Model.all_values [] infos (Uninterpreted t) |> Seq.toList
        let rel_name = sprintf "%s%c<" t name_separator
        let cmp cv1 cv2 =
            if value_equal cv1 cv2 then 0
            else if Map.find (rel_name, [cv1;cv2]) env.f = ConstBool true
            then -1 else 1
        List.sortWith cmp elts

    /// <summary>
    /// Deprecated. It was used to perform an addition (now additions are considered as non-determinitstic operations).
    /// </summary>
    let int_addition infos (env:Model.Environment) cvs =
        match Helper.lst_to_couple cvs with
        | (ConstInt (t,i), ConstInt(t',n)) when t=t' ->
            // Note: Int addition should be done non-deterministically (same semantic as for the wpr)
            // This function only support additions of the form (x+n) with 'n' a constant in the code
            let sorted_elts = order_type_elts infos env t
            let index = List.findIndex (fun cv -> value_equal cv (ConstInt (t,i))) sorted_elts
            List.item (index+n) sorted_elts
        | _ -> failwith "Integer addition not defined on these types!"
