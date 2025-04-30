import Interpreter.Types.Ast
import Interpreter.Basic -- Expr

inductive Error
| NameIsNotDefined (name : String) (vars : VarTypes) : Error
| Many : List Error -> Error
| TypesCannotBeAdded : SomeExpr -> SomeExpr -> Error
deriving Inhabited, Repr

open Except (ok error)

def Except.elim2 {α β e ε}
(okOk : α -> α -> β)
(err : e -> ε)
(errErr : e -> e -> ε)
: Except e α -> Except e α -> Except ε β
  | ok x, ok y => ok (okOk x y)
  | error x, error y => error (errErr x y)
  | ok _, error x | error x, ok _ => error (err x)

def checkWithEnv env : Ast -> Except Error ((ty : Ty) × Expr ty env)
  | Ast.val int => ok ⟨Ty.int, Expr.val int⟩
  | Ast.var (.name name) => 
    if h : name.toString ∈ env
    then ok ⟨env[name.toString], Expr.var name.toString⟩
    else error (Error.NameIsNotDefined name.toString env)
  | Ast.add e1 e2 =>
    Except.elim2
      (fun
        | ⟨Ty.int, e1⟩, ⟨Ty.int, e2⟩ => ok ⟨Ty.int, Expr.add e1 e2⟩
        | ⟨_, e1⟩, ⟨_, e2⟩ =>
          error (Error.TypesCannotBeAdded ⟨_, _, e1⟩ ⟨_, _, e2⟩))
      id
      (fun e1 e2 => Error.Many [e1, e2])
      (checkWithEnv env e1)
      (checkWithEnv env e2)
    |>.bind id
  | Ast.let_ (.name name) var_expr ret_expr => do
    let var := name.toString
    let ⟨var_type, var_expr'⟩ <- checkWithEnv env var_expr
    let env' := env.insert var var_type
    let ⟨ty, ret_expr'⟩ <- checkWithEnv env' ret_expr
    pure ⟨ty, Expr.let_ var var_expr' ret_expr'⟩

def check : Ast -> Except Error ((ty : Ty) × Expr ty ∅) := checkWithEnv ∅
