import Interpreter.Types.Ty
import Interpreter.Types.Val
import Interpreter.Types.Name
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Utils.Key


namespace Interpreter.Types
open Std (HashMap DHashMap)


abbrev VarTypes := HashMap Name Ty


abbrev TyVal := (ty : Ty) × Val ty
structure VarValues (varTypes : VarTypes) where
  hashMap : HashMap Name TyVal
  full : ∀ k, k ∈ hashMap <-> k ∈ varTypes
  types_eq : ∀ k, (h : k ∈ hashMap) -> hashMap[k].fst = varTypes[k]'(full k |>.mp h)
  deriving Repr


-- TODO: These will be added as lemmas in 4.20. Upgrade!
@[simp]
axiom Std.HashMap.mem_map_iff
{K α β : Type _} [BEq K] [Hashable K]
{k : K} {f : K -> α -> β} {hm : HashMap K α}
: k ∈ hm.map f <-> k ∈ hm
@[simp]
axiom Std.HashMap.getElem_map
{K α β : Type _} [BEq K] [Hashable K]
{k : K} {f : K -> α -> β} {hm : HashMap K α}
{k_mem_hm : k ∈ hm}
: (hm.map f)[k]'(by simp_all only [mem_map_iff]) = f k hm[k]


variable {vt : VarTypes}
instance : Inhabited (VarValues vt) := ⟨{
    -- hashMap := vt.map fun name ty => ⟨ty, default⟩ -- Too hard to prove
    hashMap := vt.map fun _ ty => ⟨ty, default⟩
    full k := by
      rw [Std.HashMap.mem_map_iff]
    types_eq name name_mem_vt := by
      rw [Std.HashMap.mem_map_iff] at name_mem_vt
      rw [Std.HashMap.getElem_map]
  }⟩
instance : EmptyCollection (VarValues {}) := ⟨{
    hashMap := {}
    full k := by apply Iff.intro <;> simp
    types_eq k h := by exfalso ; simp_all only [Std.HashMap.not_mem_empty]
  }⟩
instance : Membership Name (VarValues vt) where
  mem vv k := k ∈ vv.hashMap
instance : GetElem (VarValues vt) Name TyVal (fun vt name => name ∈ vt) where
  getElem vv k k_mem_vv := vv.hashMap[k]


-- instance {k v} [BEq k] [Hashable k]
-- : LawfulEmptyCollectionMembership k (HashMap k v) where
--   mem_empty _ := HashMap.not_mem_empty
-- 
-- 


@[simp]
theorem VarValues.mem_iff {name : Name} {vv : VarValues vt}
: name ∈ vv <-> name ∈ vt :=
  vv.full name
@[simp]
theorem VarValues.fst_getElem {name : Name} {vv : VarValues vt}
{name_mem_vv : name ∈ vv}
: vv[name].fst = vt[name]'(vv.full name |>.mp name_mem_vv) := by
  change vv.hashMap[name].fst = _
  exact vv.types_eq name name_mem_vv


def VarValues.insert
(name : Name) {ty : Ty} (val : Val ty) (vv : VarValues vt)
: VarValues $ vt.insert name ty :=
  {
    hashMap := vv.hashMap.insert name ⟨ty, val⟩
    full k := by
      rw [HashMap.mem_insert, HashMap.mem_insert, beq_iff_eq]
      apply Iff.intro
      all_goals
        rintro (name_eq_k | k_mem_vv)
        . -- name = k
          left
          assumption
        . -- k ∈ vv.hashMap
          right
          first | apply (vv.full k).mp | apply (vv.full k).mpr
          assumption
    types_eq k k_mem_vv_insert := by
      rw [HashMap.getElem_insert, HashMap.getElem_insert]
      by_cases h : name = k
      . simp_all only [beq_self_eq_true, dite_true]
      . simp_all only [beq_iff_eq, dite_false]
        rw [vv.types_eq k]
  }
