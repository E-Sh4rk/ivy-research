module Trace

    open MinimalAST
    open Model

    /// <summary>
    /// Represents runtime data about the execution of a statement:
    /// the environment before the execution, the environment after the execution, a boolean indicating whether the statement was successfully executed or not
    /// </summary>
    type RuntimeData = Environment * Environment * bool

    /// <summary>
    /// Represents a log (a "trace") of the execution of a statement.
    /// Contains info about the statement and runtime data.
    /// </summary>
    type TrStatement =
        | TrAtomicGroup of RuntimeData * List<TrStatement>
        | TrNewBlock of RuntimeData * List<VarDecl> * List<TrStatement>
        | TrVarAssign of RuntimeData * string * Value
        | TrVarAssignAction of RuntimeData * string * List<VarDecl> * VarDecl * List<Value> * TrStatement
        | TrFunAssign of RuntimeData * string * List<VarDecl> * Value
        | TrIfElse of RuntimeData * Value * TrStatement
        | TrIfSomeElse of RuntimeData * Option<ConstValue> * VarDecl * Value * TrStatement
        | TrAssert of RuntimeData * Value
        | TrAssume of RuntimeData * Value

    let runtime_data s =
        match s with
        | TrAtomicGroup (rd,_)
        | TrNewBlock (rd,_,_)
        | TrVarAssign (rd,_,_)
        | TrVarAssignAction (rd,_,_,_,_,_)
        | TrFunAssign (rd,_,_,_)
        | TrIfElse (rd,_,_)
        | TrIfSomeElse (rd,_,_,_,_)
        | TrAssert (rd,_)
        | TrAssume (rd,_) -> rd

    let is_fully_executed st =
        let (_,_,b) = runtime_data st
        b

    let are_fully_executed sts =
        List.forall is_fully_executed sts

    let rec assume_failed st =
        match st with
        | TrAtomicGroup (_,sts)
        | TrNewBlock (_,_,sts) -> List.exists (fun st -> assume_failed st) sts
        | TrVarAssign _ | TrFunAssign _ -> false
        | TrIfSomeElse (_,_,_,_,st) | TrIfElse (_,_,st) | TrVarAssignAction (_,_,_,_,_,st) ->
            assume_failed st
        | TrAssume ((_,_,false),_) -> true
        | TrAssert _ | TrAssume _ -> false

    let final_env st =
        let (_,env,_) = runtime_data st
        env

    let final_env_of_trs sts initial_env =
        let aux _ s =
            final_env s
        List.fold aux initial_env sts

    let initial_env st =
        let (env,_,_) = runtime_data st
        env
    