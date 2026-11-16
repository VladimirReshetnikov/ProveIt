import PA194PAeqUniversalAtomicCongruence
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.UniversalFormulaCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic PA194PAeq.UniversalTermCongruence
open PA194PAeqTermBlueprint PA194PAeq.UniversalTermCongruence Entailment Entailment.FiniteContext Semiformula Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev T : Theory language := ordinaryPAeq
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
local prefix:max "#'" => Semiterm.bvar (V := V) (L := language)
local prefix:max "&'" => Semiterm.fvar (V := V) (L := language)
local postfix:max "⤉" => Bootstrapping.Semiformula.shift
@[simp] theorem typedEq_val {n : Nat} (s t : Semiterm V language n) :
    (s ≐ₚ t).val = equalityCode s.val t.val := rfl

theorem replace_aux (φ : V) :
    IsSemiformula language 1 φ →
    Provable T (^∀ ^∀ imp language (equalityCode (^#1) (^#0)) (imp language (subst language (^#1 ∷ 0) φ) (subst language (^#0 ∷ 0) φ))) := by
  apply IsFormula.sigma1_structural_induction₂_ss
  · definability
  case hand =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V language 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V language 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (φ ⋏ ψ).subst ![#'1] 🡒 (φ ⋏ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [-Bootstrapping.Semiformula.substs_and, φ, ψ] using this
    suffices
        T.internalize V ⊢
          (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] ⋏ ψ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] ⋏ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hor =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V language 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V language 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (φ ⋎ ψ).subst ![#'1] 🡒 (φ ⋎ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [-Bootstrapping.Semiformula.substs_or, φ, ψ] using this
    suffices
        T.internalize V ⊢
          (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] ⋎ ψ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] ⋎ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hverum =>
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 ⊤ 🡒 ⊤) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [typedEq] using this
    suffices Theory.internalize V T ⊢ (&'1 ≐ₚ &'0) 🡒 ⊤ 🡒 ⊤ by
      apply TProof.all₂!
      simpa
    apply dhyp!; exact CV!
  case hfalsum =>
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 ⊥ 🡒 ⊥) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [typedEq] using this
    suffices Theory.internalize V T ⊢ (&'1 ≐ₚ &'0) 🡒 ⊥ 🡒 ⊥ by
      apply TProof.all₂!
      simpa
    apply dhyp!; exact efq!
  case hrel =>
    intro k R v hR hv
    obtain ⟨rfl,rfl⟩ := (source_relations k R).mp hR
    let s : Semiterm V language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
    let t : Semiterm V language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
    have veq : v = ?[s.val,t.val] := by simp [s,t,Bootstrapping.Arithmetic.vec2_eq hv.lh]
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (s ≐ₚ t).subst ![#'1] 🡒 (s ≐ₚ t).subst ![#'0]) by
      have h := (tprovable_iff_provable (T := T)).mp this
      simpa [typedEq,equalityCode,veq,Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ] using h
    simpa [T,Theory.internalize] using UniversalAtomicCongruence.positive s t
  case hnrel =>
    intro k R v hR hv
    obtain ⟨rfl,rfl⟩ := (source_relations k R).mp hR
    let s : Semiterm V language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
    let t : Semiterm V language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
    have veq : v = ?[s.val,t.val] := by simp [s,t,Bootstrapping.Arithmetic.vec2_eq hv.lh]
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (∼(s ≐ₚ t)).subst ![#'1] 🡒 (∼(s ≐ₚ t)).subst ![#'0]) by
      have h := (tprovable_iff_provable (T := T)).mp this
      have hs : IsSemiterm language 1 s.val := by simpa using s.isSemiterm
      have ht : IsSemiterm language 1 t.val := by simpa using t.isSemiterm
      have hw1 : IsSemitermVec language 1 2 ((^#1)∷(0:V)) := by simp
      have hw0 : IsSemitermVec language 1 2 ((^#0)∷(0:V)) := by simp
      have hv1 : IsUTermVec language 2
          (termSubst language ((^#1)∷(0:V)) s.val ∷ termSubst language ((^#1)∷(0:V)) t.val ∷ (0:V)) := by
        simp [(hw1.termSubst hs).isUTerm,(hw1.termSubst ht).isUTerm]
      have hv0 : IsUTermVec language 2
          (termSubst language ((^#0)∷(0:V)) s.val ∷ termSubst language ((^#0)∷(0:V)) t.val ∷ (0:V)) := by
        simp [(hw0.termSubst hs).isUTerm,(hw0.termSubst ht).isUTerm]
      simpa [typedEq,equalityCode,veq,Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,
        neg_rel hR hv1,neg_rel hR hv0] using h
    simpa [T,Theory.internalize] using UniversalAtomicCongruence.negative s t
  case hall =>
    intro p hp ih
    let φ : Semiformula V language 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (∀⁰ φ).subst ![#'1] 🡒 (∀⁰ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, typedEq, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using this
    have ih : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ∀⁰ φ⤉⤉.subst ![#'0, &'1] 🡒 ∀⁰ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!; simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs]
    apply deduct'!
    apply TProof.all_imp_all!
    apply deductInv'!
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free, SemitermVec.q,
      Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs, one_add_one_eq_two]
    using TProof.specialize₂! ih (&'1) (&'2)
  case hexs =>
    intro p hp ih
    let φ : Semiformula V language 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 (∃⁰ φ).subst ![#'1] 🡒 (∃⁰ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, typedEq, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using! this
    have ih : T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ∃⁰ φ⤉⤉.subst ![#'0, &'1] 🡒 ∃⁰ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!; simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs]
    apply deduct'!
    apply TProof.exs_imp_exs!
    apply deductInv'!
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free, SemitermVec.q,
      Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs, one_add_one_eq_two]
      using TProof.specialize₂! ih (&'1) (&'2)

theorem universal (φ : Semiformula V language 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
  apply (tprovable_iff_provable (T := T)).mpr
  simpa using replace_aux φ.val (by simpa using φ.isSemiformula)

theorem replace (φ : Semiformula V language 1) (u₁ u₂ : Term V language) :
    T.internalize V ⊢ (u₁ ≐ₚ u₂) 🡒 φ.subst ![u₁] 🡒 φ.subst ![u₂] := by
  have h := TProof.specialize₂! (universal φ) u₂ u₁
  simpa [Bootstrapping.Semiformula.substs_substs] using h

#print axioms universal
#print axioms replace
#print axioms replace_aux
end PA194PAeq.UniversalFormulaCongruence
