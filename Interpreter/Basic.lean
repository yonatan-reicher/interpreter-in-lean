import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

open Std

inductive Ty : Type where
  | int : Ty
  | bool : Ty
deriving Inhabited, BEq, Repr

abbrev Val : Ty → Type
  | Ty.int => Int
  | Ty.bool => Bool

instance {ty : Ty} : Repr (Val ty) where
  reprPrec v _ :=
    match ty with
    | Ty.int => repr (v : Int)
    | Ty.bool => repr (v : Bool)

abbrev VarTypes : Type := HashMap String Ty

abbrev VarValues (types: VarTypes) :=
  /-
  TODO: Try alternative definitions
  1. DHashMap String (fun name => PSigma (fun h => Val (types[name]'h)))
  2. DHashMap (Sigma String (fun name => name ∈ types)) (fun ⟨_,h⟩ => Val types[name]'h)
  3. An inductive type
  4. A structure!~
  structure VarValues types where
    keys_in_types : ∀ name, name ∈ values → name ∈ types
    values : HashMap DString (Val types[name]'subset)
  5. A keys-of type! this must exist!
     DHashMap (KeysOf types) (fun name => Val types[name])
  -/
  (name : String) →
  {h : name ∈ types} →
  Val types[name]

def VarValues.empty : VarValues ∅ :=
  fun name name_in_empty =>
    let name_not_in_empty := HashMap.not_mem_empty (a:=name)
    absurd name_in_empty name_not_in_empty

def VarValues.get {types} (values : VarValues types) (name : String) {h : name ∈ types} : Val types[name] :=
  values name

def VarValues.insert
    {types ty}
    (values : VarValues types)
    (var : String)
    (value : Val ty)
  : VarValues (types.insert var ty) :=
  let types' := types.insert var ty
  fun name {h : name ∈ types'} => -- : Val types'[name]
    have h : (var == name) = true ∨ name ∈ types := HashMap.mem_insert.mp h
    if h_name_var : var == name then
      have _ : var ∈ types' := by simp_all
      have h_eq : ty = types'[var] := HashMap.getElem_insert_self.symm
      have h_eq : ty = types'[name] := by simp_all
      (congrArg Val h_eq).mp value
    else
      have h : name ∈ types := by simp_all
      let ret := values.get name (h:=h)
      have _ : types'[name] = if var == name then ty else types[name] := HashMap.getElem_insert
      have h_eq : types[name] = types'[name] := by simp_all
      (congrArg Val h_eq).mp ret

inductive Expr : Ty → VarTypes → Type where
  | val {ty types} : Val ty → Expr ty types
  | var {types}:
    (name: String) →
    {h_name_in_types : name ∈ types} →
    Expr types[name] types
  | add {types}: Expr Ty.int types → Expr Ty.int types → Expr Ty.int types
  | let_ {var_type types ty} :
    (var: String) →
    Expr var_type types →
    Expr ty (types.insert var var_type) →
    Expr ty types
deriving Repr

def eval {ty types}: Expr ty types → VarValues types → Val ty
  | .val v, _ => v
  | Expr.var name, values => values.get name
  | .add e1 e2, values =>
    let v1 : Int := (eval e1 values : Int)
    let v2 : Int := (eval e2 values : Int)
    v1 + v2
  | .let_ var var_expr ret_expr, values => 
    let var_val := eval var_expr values
    let values' := values.insert var var_val
    eval ret_expr values'
