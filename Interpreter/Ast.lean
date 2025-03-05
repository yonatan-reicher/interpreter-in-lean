inductive Ast : Type where
  | val : Int → Ast
  | var : String → Ast
  | add : Ast → Ast → Ast
  | let_ : String → Ast → Ast → Ast
  deriving Repr, BEq
