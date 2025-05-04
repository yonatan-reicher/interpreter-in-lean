import Interpreter.Types


namespace Interpreter.Eval


open Interpreter.Types (
  VarValues
  VarTypes
  Expr
  Val
)


partial def eval {ty vars} (values : VarValues vars) (expr : Expr ty vars)
: Val ty :=
  match expr with
  | Expr.val v => v
  | Expr.var v =>
    -- values[v.val].snd
    have : values[v.val].fst = vars[v.val] := VarValues.fst_getElem
    this ▸ values[v.val].snd
  -- | Expr.add lhs rhs => eval values lhs + eval values rhs
  | Expr.letIn var rhs ret =>
    let varValue := eval values rhs
    let values' := values.insert var varValue
    eval values' ret


