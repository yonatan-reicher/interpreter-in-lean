import Interpreter.Types.Identifier


inductive Ast : Type where
  | val : Int → Ast
  | var : Ident → Ast
  | add : Ast → Ast → Ast
  | let_ : Ident → Ast → Ast → Ast
  deriving Repr, BEq, Inhabited
