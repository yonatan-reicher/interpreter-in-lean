import Interpreter.Types.Identifier


namespace Interpreter.Types


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
  --- x := 123; f x
  | letIn : Ident → Ast → Ast → Ast
  deriving Repr, BEq, Inhabited
