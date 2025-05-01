import Interpreter.Basic


namespace Interpreter.Eval


partial def eval {ty vars} (values : VarValues vars) (expr : Expr ty vars) : Val ty :=
  match expr with
  | Expr.val v => v
  | Expr.var v => values.get v
  | Expr.add lhs rhs => eval values lhs + eval values rhs
  | Expr.let_ var rhs ret =>
    let varValue := eval values rhs
    let values' := values.insert var varValue
    eval values' ret


