import Interpreter.Types.Ty
import Interpreter.Types.Vars


namespace Interpreter.Types


inductive Expr : Ty -> VarTypes -> Type where
  | val {ty vt} : Val ty -> Expr ty vt
  | var {vt} : (var : Key vt) -> Expr vt[var.val] vt
  | letIn {ty var_ty vt}
  : (var : Name) -> Expr var_ty vt -> Expr ty (vt.insert var var_ty) -> Expr ty vt
  deriving Repr
  -- deriving Repr, BEq
  -- deriving Repr, DecidableEq


instance {ty vt} : Inhabited (Expr ty vt) where default := .val default
/-
instance {ty vt} : BEq (Expr ty vt) where
  beq
    | .val a, .val b => a == b
    | .var a, .var b => a == b
    | .letIn a b c, .letIn d e f => a == d && b == e && c == f
    | _, _ => false
-/
