import Interpreter.Types.Identifier


-- TODO:
/-
1. Rename Ast to Expr
2. Add a namespace for the module
3. Add a types for a declaration, and for a script/program/lib
-/


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
