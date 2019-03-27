module cfa

public export
data Variable : Type -> Type
  where
    IntVar : (name : String) -> Variable Integer
    BoolVar : (name : String) -> Variable Bool

public export
data Const : (ty : Type) -> Type
  where
    IntConst : (x : Integer) -> Const Integer
    BoolConst : (b : Bool) -> Const Bool

public export
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

public export
data Action = Assign (Variable type) (Expr type)
  | Assume (Expr Bool)
  | Noop

public export
data Node = SimpleNode String (List (Action, Node))
            | ErrorNode


public export
data CFA = SimpleCfa Node

public export
traverse : Node -> IO ()
traverse (SimpleNode x []) = putStrLn (x ++ " completed")
traverse (SimpleNode x ((a,n) :: xs)) =
                                  do traverse n
                                     traverse (SimpleNode x xs)
traverse ErrorNode = putStrLn "Reachable"



public export
traverseCfa : CFA -> IO ()
traverseCfa (SimpleCfa start) = traverse start
