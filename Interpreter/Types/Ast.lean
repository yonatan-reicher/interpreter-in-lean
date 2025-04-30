import Interpreter.Types.Identifier


inductive Ast : Type where
  --- 123
  | val : Int → Ast
  --- x
  | var : Ident → Ast
  --- x + y
  | add : Ast → Ast → Ast
  --- let x := 123 in x + y
  | letIn : Ident → Ast → Ast → Ast
  deriving Repr, BEq, Inhabited
