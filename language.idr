module language

public export
data IntExpr = IntLiteral Integer
  | IntVar String
  | Plus IntExpr IntExpr

public export
data BoolExpr = LessThan IntExpr IntExpr

public export
data Instruction =
  Assign String IntExpr
  | Seq Instruction Instruction
  | While BoolExpr Instruction
