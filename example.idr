module example
import cfa
import language


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


program : Instruction
program = Seq
  (Assign "x" (IntLiteral 12))
  (While
    (LessThan (IntVar "x") (IntLiteral 20))
    (Assign "x" (Plus
      (IntVar "x")
      (IntLiteral 1)
    ))
  )
