﻿module Model

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)
    open AST

    type BoundConstraint = string * int // For custom types, the number of elements - 1
    type FunConstraint = string * List<ConstValue> * ConstValue
    type VarConstraint = string * ConstValue

    type Constraint =
        | Bound of BoundConstraint
        | Function of FunConstraint
        | Variable of VarConstraint

    type Model = { b : List<BoundConstraint> ; f : List<FunConstraint>; v : List<VarConstraint> }
    type Model' = List<Constraint>


    type TypeInfos = Map<string, int> // For now: only contains bounds for each type

    type FunEnv = Map<string * List<ConstValue>, ConstValue>
    type VarEnv = Map<string, ConstValue>

    type Environment = { f : FunEnv; v : VarEnv }

    type ModuleDecl = ModuleDecl<TypeInfos,Environment>
    type InterpretedActionDecl = InterpretedActionDecl<TypeInfos,Environment>

    type VarDecls = Map<string, VarDecl>
    type FunDecls = Map<string, FunDecl>
    type MacroDecls = Map<string, MacroDecl>
    type InterpretedDecls = Map<string, InterpretedActionDecl>
    
    [<NoEquality;NoComparison>]
    type Declarations = { f : FunDecls; v : VarDecls; m : MacroDecls; i : InterpretedDecls; }

    let declarations_of_module (md:ModuleDecl) =
        let aux acc (d:FunDecl) =
            Map.add d.Name d acc
        let funs = List.fold aux Map.empty md.Funs
        let aux acc (d:MacroDecl) =
            Map.add d.Name d acc
        let macros = List.fold aux Map.empty md.Macros
        let aux acc (d:InterpretedActionDecl) =
            Map.add d.Name d acc
        let interp = List.fold aux Map.empty md.InterpretedActions
        { f = funs; v = Map.empty; m = macros ; i = interp }

    let add_var_declaration (d:VarDecl) (ds:Declarations) =
        { ds with v=Map.add d.Name d ds.v }

    let all_values types infos data_type =
        match data_type with
        | Void -> Seq.singleton ConstVoid
        | Bool -> [ConstBool false; ConstBool true] |> Seq.ofList
        | Uninterpreted s ->
            let max = Map.find s infos
            seq { for x in 0..max -> ConstInt (s, x) }
        | Enumerated s ->
            match (find_type types s).Infos with
            | EnumeratedTypeDecl lst -> List.toSeq (List.map (fun str -> ConstEnumerated (s,str)) lst)
            | _ -> failwith "Not an enumerated type!"

    let all_values_ext types infos lst =
        let lst = List.map (all_values types infos) lst
        Helper.all_choices_combination lst

    let cardinal infos =
        Map.fold (fun acc _ nb -> acc + nb) 0 infos 

    // Note: If some constraints are contradictory, the last one has the last word
    let constraints_to_env (m:ModuleDecl) cs : (TypeInfos * Environment) =
        // Type infos
        // Init
        let type_infos = List.fold (fun acc (tdecl:TypeDecl) -> Map.add tdecl.Name 0 acc) Map.empty m.Types
        // Apply constraints
        let type_infos =
            List.fold
                (fun acc c ->
                    match c with
                    | Function _ | Variable _ -> acc
                    | Bound (str, i) ->
                        let old_i = Map.find str type_infos
                        Map.add str (max i old_i) acc
                ) type_infos cs

        // Environment
        // Init
        let fun_env =
            List.fold
                (fun acc (fdecl:FunDecl) ->
                    Seq.fold (fun acc input ->
                        Map.add (fdecl.Name, input) (AST.type_default_value m.Types fdecl.Output) acc)
                        acc (all_values_ext m.Types type_infos fdecl.Input)
                ) Map.empty m.Funs
        // Apply constraints
        let fun_env =
            List.fold
                (fun f c ->
                    match c with
                    | Function (str, input, output) -> Map.add (str, input) output f
                    | Variable (str, output) -> Map.add (str, []) output f
                    | Bound _ -> f
                ) fun_env cs

        (type_infos, { f = fun_env ; v = Map.empty })
