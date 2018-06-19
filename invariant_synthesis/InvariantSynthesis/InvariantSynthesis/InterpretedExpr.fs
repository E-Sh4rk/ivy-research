﻿module InterpretedExpr

    open AST

    let int_addition infos _ cvs =
        match Helper.lst_to_couple cvs with
        | (ConstInt (t,i), ConstInt(t',i')) when t=t' ->
            let res = i+i'
            if Map.find t infos < res
            then failwith "Integer addition result is out of bounds!"
            else ConstInt (t, res)
        | _ -> failwith "Integer addition not defined on these types!"