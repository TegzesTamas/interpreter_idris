module cfa

export
data Variable : Type -> Type
  where
    IntVar : (name : String) -> Variable Integer
    BoolVar : (name : String) -> Variable Bool

export
data Const : (ty : Type) -> Type
  where
    IntConst : (x : Integer) -> Const Integer
    BoolConst : (b : Bool) -> Const Bool

export
data Expr : Type -> Type
  where
    ConstExpr : Const type -> Expr type
    RefExpr : Variable type -> Expr type
    AddExpr : Expr Integer -> Expr Integer -> Expr Integer
    SubExpr : Expr Integer -> Expr Integer -> Expr Integer
    EqExpr : Expr Integer -> Expr Integer -> Expr Bool
    LessExpr : Expr Integer -> Expr Integer -> Expr Bool
    GrtExpr : Expr Integer -> Expr Integer -> Expr Bool
    LeqExpr : Expr Integer -> Expr Integer -> Expr Bool
    GeqExpr : Expr Integer -> Expr Integer -> Expr Bool
    NegExpr : Expr Bool -> Expr Bool
    AndExpr : Expr Bool -> Expr Bool -> Expr Bool
    OrExpr : Expr Bool -> Expr Bool -> Expr Bool
    ImplExpr : Expr Bool -> Expr Bool -> Expr Bool
    IffExpr : Expr Bool -> Expr Bool -> Expr Bool

export
data Action = Assign (Variable type) (Expr type)
  | Assume (Expr Bool)
  | Noop

export
data Node = SimpleNode String (List (Action, Node))
            | ErrorNode


export
data CFA = SimpleCfa Node

export
traverse : Node -> IO ()
traverse (SimpleNode x []) = putStrLn (x ++ " completed")
traverse (SimpleNode x ((a,n) :: xs)) =
                                  do traverse n
                                     traverse (SimpleNode x xs)
traverse ErrorNode = putStrLn "Reachable"



export
traverseCfa : CFA -> IO ()
traverseCfa (SimpleCfa start) = traverse start

-- example
errorNode : Node
errorNode = ErrorNode

node1 : Node
node1 = SimpleNode "1" [(Noop, errorNode)]

node2 : Node
node2 = SimpleNode "2" [(Noop, errorNode)]

node3 : Node
node3 = SimpleNode "3" []

node4 : Node
node4 = SimpleNode "4" [(Noop, node3), (Noop, node2)]

startNode : Node
startNode = SimpleNode "Start" [(Noop, node2), (Noop, node4)]
