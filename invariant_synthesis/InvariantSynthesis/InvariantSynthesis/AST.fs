module AST

    (* A VERY BASIC AST FOR IVY *)

    // TODO: Test on new examples (verdi_lock, leader election...)
    // TODO: Optimize computation of WPR: use mutable AST for formulas so substitutions can be done in constant time

    // TODO: Refactor: Make a new AST 'DeterministicAST' and get rid of all non-determinitstic cases in WPR, Interpreter & Marking

    // TODO: "while" loops
    // TODO: "if some" with multiple var decls
    // TODO: Allow multiple return values for actions.
    // If used in an expression, returns ConstVoid.
    // If used in a "call" statement, assign each value.
    // TODO: Handle functions with an object as return value (case of instance a(X):b(Y))
    // For that, we can consider those functions an instance of the corresponding module,
    // with an additionals first parameters for every var/fun/action/etc (that corresponds the parameters of the initial function)
    // TODO: isolate, inductive, extract, interpret...
    // TODO: Infer types for macro args (currently, type annotations is required)

    type Type =
        | Void
        | Bool
        | Uninterpreted of string
        | Enumerated of string

    type RepresentationFlags = Infix
    type RepresentationInfos = { DisplayName: string option; Flags: Set<RepresentationFlags> }

    type TypeDeclInfo = UninterpretedTypeDecl | EnumeratedTypeDecl of List<string>
    type TypeDecl = { Name: string; Infos: TypeDeclInfo }
    type FunDecl = { Name: string; Input: List<Type>; Output: Type; Representation: RepresentationInfos }
    type VarDecl = { Name: string; Type: Type; Representation: RepresentationInfos }

    let default_representation : RepresentationInfos = { DisplayName = None; Flags = Set.empty }

    type ConstValue =
        | ConstVoid // Only used for actions that return nothing
        | ConstBool of bool
        | ConstInt of string * int // Type name, value
        | ConstEnumerated of string * string // Type name, value

    /// <summary>
    /// Describes an expression without any side effect.
    /// </summary>
    type Value =
        | ValueConst of ConstValue
        | ValueStar of Type
        | ValueVar of string
        | ValueFun of string * List<Value>
        | ValueMacro of string * List<Value>
        | ValueEqual of Value * Value
        | ValueOr of Value * Value
        | ValueAnd of Value * Value
        | ValueNot of Value
        | ValueSomeElse of VarDecl * Value * Value
        | ValueIfElse of Value * Value * Value
        | ValueForall of VarDecl * Value
        | ValueExists of VarDecl * Value
        | ValueImply of Value * Value
        | ValueInterpreted of string * List<Value>

    /// <summary>
    /// Describes an expression with possible side effects.
    /// </summary>
    type Expression =
        | ExprConst of ConstValue
        | ExprStar of Type
        | ExprVar of string
        | ExprFun of string * List<Expression>
        | ExprMacro of string * List<Value>
        | ExprAction of string * List<Expression>
        | ExprEqual of Expression * Expression
        | ExprOr of Expression * Expression
        | ExprAnd of Expression * Expression
        | ExprNot of Expression
        | ExprSomeElse of VarDecl * Value * Value
        | ExprIfElse of Expression * Value * Value
        | ExprForall of VarDecl * Value
        | ExprExists of VarDecl * Value
        | ExprImply of Expression * Expression
        | ExprInterpreted of string * List<Expression>

    type HoleExpression =
        | Hole of VarDecl
        | Expr of Expression

    /// <summary>
    /// Describes a statement. This AST is the closest to the actual IVy code, but not the more conveninent for analysis.
    /// </summary>
    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | Expression of Expression
        | VarAssign of string * Expression
        | FunAssign of string * List<Expression> * Expression
        | ForallFunAssign of string * List<HoleExpression> * Value
        | IfElse of Expression * Statement * Statement
        | IfSomeElse of VarDecl * Value * Statement * Statement
        | Assert of Value
        | Assume of Value
        | Require of Value
        | Ensure of Value

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement; Module: string }

    type MacroDecl = { Name: string; Args: List<VarDecl>; Output: Type; Value: Value ; Representation: RepresentationInfos }

    type InvariantDecl = { Module: string; Formula: Value }
    type AxiomDecl = InvariantDecl

    /// <summary>
    /// Not used anymore since interpreted actions are considered as star expressions (non-determinitic choices).
    /// </summary>
    [<NoEquality;NoComparison>]
    type InterpretedActionDecl<'a,'b> = { Name: string; Args: List<Type>; Output: Type; Effect: 'a -> 'b -> List<ConstValue> -> ConstValue ; Representation: RepresentationInfos }

    /// <summary>
    /// Represents a 'module', but not in the IVy sense of the word. Here a module is just a collection of types, functions, actions, invariants...
    /// </summary>
    [<NoEquality;NoComparison>]
    type ModuleDecl<'a,'b> =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; InterpretedActions: List<InterpretedActionDecl<'a,'b>>; Exports: List<string*string>;
            Actions: List<ActionDecl>; Macros: List<MacroDecl>; Invariants: List<InvariantDecl>; Axioms: List<AxiomDecl> }

    let empty_module name =
        {
            Name=name;
            Types=[];
            Funs=[];
            Actions=[];
            Macros=[];
            Invariants=[];
            InterpretedActions=[];
            Axioms=[];
            Exports=[]
        }

    let default_var_decl name t =
        { VarDecl.Name = name ; VarDecl.Type = t ; VarDecl.Representation = default_representation }

    // Var names functions

    let name_separator = '.'
    let action_variant_char = ':'

    /// <summary>
    /// An action is designated with a string composed of two components: its name (itself composed of a basename and an individual name) and its variant.
    /// If the variant is empty, it refers to the current implementation of the action. Otherwise, it refers to an additional implementation, like "after" or "before".
    /// </summary>
    let variant_action_name name variant =
        if variant = ""
        then name
        else sprintf "%s%c%s" name action_variant_char variant

    /// <summary>
    /// Returns a tuple of the form (name,variant).
    /// </summary>
    let decompose_variant_action_name (name:string) =
        let i = name.LastIndexOf(action_variant_char)
        if i >= 0
        then (name.Substring(0,i), name.Substring(i+1))
        else (name, "")

    let local_var_prefix = "$"
    let impossible_var_factor = "$$"

    let void_return_decl = default_var_decl impossible_var_factor Void

    let generated_name name =
        sprintf "%s%s" impossible_var_factor name

    let make_name_unique name id =
        sprintf "%s%s%i" name impossible_var_factor id

    let make_name_unique_bis name id_str =
        sprintf "%s%s%s%s" name impossible_var_factor impossible_var_factor id_str

    let local_name name =
        sprintf "%s%s" local_var_prefix name

    /// <summary>
    /// Every element is designated with a string composed of two components: its basename (the name of its ancestors) and its individual name.
    /// </summary>
    let compose_name base_name name =
        if name = ""
        then base_name
        else if base_name = ""
        then name
        else sprintf "%s%c%s" base_name name_separator name

    /// <summary>
    /// Returns a tuple of the form (parent name, last name).
    /// </summary>
    let decompose_name (name:string) =
        let i = name.LastIndexOf(name_separator)
        if i >= 0
        then (name.Substring(0,i), name.Substring(i+1))
        else ("", name)

    let has_base_name (name:string) (base_name:string) =
        base_name = "" || name = base_name || name.StartsWith(sprintf "%s%c" base_name name_separator)

    let has_reference_name (name:string) reference_name =
        name = reference_name || name.EndsWith(sprintf "%c%s" name_separator reference_name)

    // Utility functions

    let find_type types str =
        List.find (fun (decl:TypeDecl) -> decl.Name = str) types

    let all_uninterpreted_types types =
        let et = List.filter (fun (t:TypeDecl) -> match t.Infos with UninterpretedTypeDecl -> true | _ -> false) types
        List.map (fun (t:TypeDecl) -> Uninterpreted t.Name) et

    let all_enumerated_types types =
        let et = List.filter (fun (t:TypeDecl) -> match t.Infos with EnumeratedTypeDecl _ -> true | _ -> false) types
        List.map (fun (t:TypeDecl) -> Enumerated t.Name) et

    let all_enumerated_values types =
        let add_values acc (t:TypeDecl) =
            match t.Infos with
            | UninterpretedTypeDecl -> acc
            | EnumeratedTypeDecl strs ->
                let strs = List.map (fun str -> (t.Name,str)) strs
                Set.union (Set.ofList strs) acc
        List.fold add_values Set.empty types

    let find_function (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs

    let find_action (m:ModuleDecl<'a,'b>) str variant =
        let str = variant_action_name str variant
        List.find (fun (decl:ActionDecl) -> decl.Name = str) m.Actions

    let find_action_any_variant (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:ActionDecl) -> let (str',_) = decompose_variant_action_name decl.Name in str'=str) m.Actions

    let find_interpreted_action (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:InterpretedActionDecl<'a,'b>) -> decl.Name = str) m.InterpretedActions

    let find_macro (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:MacroDecl) -> decl.Name = str) m.Macros

    let find_invariants (m:ModuleDecl<'a,'b>) module_name =
        List.filter (fun (d:InvariantDecl) -> has_base_name d.Module module_name) m.Invariants

    let invariants_to_formulas invs =
        List.map (fun (d:InvariantDecl) -> d.Formula) invs

    let rec map_vars_in_value v dico =
        match v with
        | ValueConst c -> ValueConst c
        | ValueStar t -> ValueStar t
        | ValueVar str ->
            if Map.containsKey str dico
            then Map.find str dico
            else ValueVar str
        | ValueFun (str, vs) ->
            ValueFun (str, List.map (fun v -> map_vars_in_value v dico) vs)
        | ValueMacro (str, vs) ->
            ValueMacro (str, List.map (fun v -> map_vars_in_value v dico) vs)
        | ValueEqual (v1, v2) ->
            ValueEqual (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueOr (v1, v2) ->
            ValueOr (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueAnd (v1, v2) ->
            ValueAnd (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueNot v ->
            ValueNot (map_vars_in_value v dico)
        | ValueSomeElse (d, v1, v2) ->
            let dico' = Map.remove d.Name dico
            ValueSomeElse (d, map_vars_in_value v1 dico', map_vars_in_value v2 dico)
        | ValueIfElse (f, v1, v2) ->
            ValueIfElse (map_vars_in_value f dico, map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueForall (d,v) ->
            let dico = Map.remove d.Name dico
            ValueForall (d, map_vars_in_value v dico)
        | ValueExists (d,v) ->
            let dico = Map.remove d.Name dico
            ValueExists (d, map_vars_in_value v dico)
        | ValueImply (v1, v2) ->
            ValueImply (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueInterpreted (str, vs) ->
            ValueInterpreted (str, List.map (fun v -> map_vars_in_value v dico) vs)

    let rec expr_to_value expr =
        match expr with
        | ExprConst c -> ValueConst c
        | ExprStar t -> ValueStar t
        | ExprVar v -> ValueVar v
        | ExprFun (str,args) -> ValueFun (str, List.map expr_to_value args)
        | ExprMacro (str, args) -> ValueMacro (str, args)
        | ExprAction _ -> failwith "Value expected, action found!"
        | ExprEqual (e1, e2) -> ValueEqual (expr_to_value e1, expr_to_value e2)
        | ExprOr (e1, e2) -> ValueOr (expr_to_value e1, expr_to_value e2)
        | ExprAnd (e1, e2) -> ValueAnd (expr_to_value e1, expr_to_value e2)
        | ExprNot e -> ValueNot (expr_to_value e)
        | ExprSomeElse (d, v1, v2) -> ValueSomeElse (d, v1, v2)
        | ExprIfElse (f, v1, v2) -> ValueIfElse (expr_to_value f, v1, v2)
        | ExprForall (d,v) -> ValueForall (d,v)
        | ExprExists (d,v) -> ValueExists (d,v)
        | ExprImply (e1, e2) -> ValueImply (expr_to_value e1, expr_to_value e2)
        | ExprInterpreted (str, args) -> ValueInterpreted (str, List.map expr_to_value args)
        
    let expand_macro (macro:MacroDecl) args =
        let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty macro.Args args
        map_vars_in_value (macro.Value) dico

    let exclude_from_module (m:ModuleDecl<'a,'b>) exclusions =
        let is_provenance_excluded name =
            List.exists (fun str -> has_base_name name str) exclusions
        let filter_types (t:TypeDecl) =
            let (bn,_) = decompose_name t.Name
            not (is_provenance_excluded bn)
        let filter_funs (f:FunDecl) =
            let (bn,_) = decompose_name f.Name
            not (is_provenance_excluded bn)
        let filter_actions (a:ActionDecl) =
            not (is_provenance_excluded a.Module)
        let filter_macros (m:MacroDecl) =
            let (bn,_) = decompose_name m.Name
            not (is_provenance_excluded bn)
        let filter_axioms (a:AxiomDecl) =
            not (is_provenance_excluded a.Module)
        let filter_exports (prov,_) =
            not (is_provenance_excluded prov)
        let filter_invariants (i:InvariantDecl) =
            not (is_provenance_excluded i.Module)

        let t = List.filter filter_types m.Types
        let f = List.filter filter_funs m.Funs
        let a = List.filter filter_actions m.Actions
        let ma = List.filter filter_macros m.Macros
        let i = List.filter filter_invariants m.Invariants
        let e = List.filter filter_exports m.Exports
        let ax = List.filter filter_axioms m.Axioms
        { ModuleDecl.Name=m.Name ; Types=t; Funs=f; Actions=a; Macros=ma; Invariants=i; Exports=e;
            InterpretedActions=m.InterpretedActions; Axioms=ax }

    // Functions on types

    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s
        | ConstEnumerated (s,_) -> Enumerated s

    // Note: should not be changed: operations like Set.contains or Set.remove doesn't take this function into account.
    let value_equal v1 v2 = v1=v2

    let type_equal t1 t2 = t1=t2

    let type_default_value types t =
        match t with
        | Void -> ConstVoid
        | Bool -> ConstBool false
        | Uninterpreted str -> ConstInt (str, 0)
        | Enumerated str ->
            match (find_type types str).Infos with
            | EnumeratedTypeDecl (h::_) -> ConstEnumerated (str,h)
            | _ -> failwith "No default value for this type!"
            
    let rec type_of_value<'a,'b> (m:ModuleDecl<'a,'b>) value dico =
        match value with
        | ValueConst cv -> type_of_const_value cv
        | ValueStar t -> t
        | ValueVar v -> Map.find v dico
        | ValueFun (f,_) -> (find_function m f).Output
        | ValueMacro (str,_) -> (find_macro m str).Output
        | ValueEqual _ | ValueOr _ | ValueAnd _ | ValueNot _ | ValueImply _
        | ValueForall _ | ValueExists _ -> Bool
        | ValueSomeElse (_,_,v) -> type_of_value m v dico
        | ValueIfElse (_,_,v) -> type_of_value m v dico
        | ValueInterpreted (str, _) -> (find_interpreted_action m str).Output

    let type_of_expr<'a,'b> (m:ModuleDecl<'a,'b>) expr dico =
        match expr with
        | ExprConst cv -> type_of_const_value cv
        | ExprStar t -> t
        | ExprVar v -> Map.find v dico
        | ExprFun (f,_) -> (find_function m f).Output
        | ExprMacro (str,_) -> (find_macro m str).Output
        | ExprAction (str, _) -> (find_action m str "").Output.Type
        | ExprEqual _ | ExprOr _ | ExprAnd _ | ExprNot _ | ExprImply _
        | ExprForall _ | ExprExists _ -> Bool
        | ExprSomeElse (_,_,v) -> type_of_value m v dico
        | ExprIfElse (_,_,v) -> type_of_value m v dico
        | ExprInterpreted (str, _) -> (find_interpreted_action m str).Output

    let type_of_hole_expr<'a,'b> (m:ModuleDecl<'a,'b>) hexpr dico =
        match hexpr with
        | Expr e -> type_of_expr m e dico
        | Hole d -> d.Type
