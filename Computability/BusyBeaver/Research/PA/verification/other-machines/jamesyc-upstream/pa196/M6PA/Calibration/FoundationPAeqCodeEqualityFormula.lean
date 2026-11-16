module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeEqualityAtoms
@[expose] public section
/-! Adapted from Foundation EquationalTheory (Apache-2.0). Genuine definable
model-code structural induction for PAeq formula equality replacement. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open _root_.FFL.FirstOrder.Entailment Entailment.FiniteContext
open Bootstrapping.Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Semiterm.bvar (V:=V) (L:=Presentation.language)
local prefix:max "&'" => Semiterm.fvar (V:=V) (L:=Presentation.language)
local postfix:max "⤉" => Bootstrapping.Semiformula.shift
local infix:50 " ≐ₚ " => typedEq
local infix:50 " ≉ₚ " => typedNe
local infix:50 " ^=ₚ " => equalityCode
private lemma vec2_eq {v : V} (h : len v=2) : ?[v.[0],v.[1]]=v :=
  nth_ext' 2 (by simp [one_add_one_eq_two]) h (by
    intro i hi
    have : i=0 ∨ i=1 := le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi)
    rcases this with rfl|rfl <;> simp)

lemma replace_aux (φ : V) :
    IsSemiformula Presentation.language 1 φ →
    Provable U
      (^∀ ^∀ imp Presentation.language (^#1 ^=ₚ ^#0) (imp Presentation.language (subst Presentation.language (^#1 ∷ 0) φ) (subst Presentation.language (^#0 ∷ 0) φ)))
      := by
  classical
  apply IsFormula.sigma1_structural_induction₂_ss
  · definability
  case hand =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V Presentation.language 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V Presentation.language 1 := ⟨q, by simpa using hq⟩
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (φ ⋏ ψ).subst ![#'1] 🡒 (φ ⋏ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-Semiformula.substs_and, -Bootstrapping.substs_and, φ, ψ] using this
    suffices
        (U).internalize V ⊢
          (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] ⋏ ψ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] ⋏ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    have ihφ : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ihp
    have ihψ : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ihq
    have ihφ :
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
        using this
    have ihψ :
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
        using this
    cl_prover [ihφ, ihψ]
  case hor =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V Presentation.language 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V Presentation.language 1 := ⟨q, by simpa using hq⟩
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (φ ⋎ ψ).subst ![#'1] 🡒 (φ ⋎ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-Semiformula.substs_or, -Bootstrapping.substs_or, φ, ψ] using this
    suffices
        (U).internalize V ⊢
          (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] ⋎ ψ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] ⋎ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    have ihφ : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ihp
    have ihψ : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ihq
    have ihφ :
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
        using this
    have ihψ :
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
        using this
    cl_prover [ihφ, ihψ]
  case hverum =>
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ⊤ 🡒 ⊤) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-typedEq_subst,equalityCode] using this
    suffices Theory.internalize V U ⊢ (&'1 ≐ₚ &'0) 🡒 ⊤ 🡒 ⊤ by
      apply TProof.all₂!
      simpa
    cl_prover
  case hfalsum =>
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ⊥ 🡒 ⊥) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-typedEq_subst,equalityCode] using this
    suffices Theory.internalize V U ⊢ (&'1 ≐ₚ &'0) 🡒 ⊥ 🡒 ⊥ by
      apply TProof.all₂!
      simpa
    cl_prover
  case hrel =>
    intro k R v hR hv
    obtain ⟨rfl,rfl⟩ := (Presentation.source_relations k R).mp hR
    let t : Semiterm V Presentation.language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
    let u : Semiterm V Presentation.language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
    have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
    suffices (U).internalize V ⊢
        ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t ≐ₚ u).subst ![#'1] 🡒 (t ≐ₚ u).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-typedEq_subst,veq,val_all,equalityCode] using! this
    simpa using replace_eq t u
  case hnrel =>
    intro k R v hR hv
    obtain ⟨rfl,rfl⟩ := (Presentation.source_relations k R).mp hR
    let t : Semiterm V Presentation.language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
    let u : Semiterm V Presentation.language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
    have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
    suffices (U).internalize V ⊢
        ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t ≉ₚ u).subst ![#'1] 🡒 (t ≉ₚ u).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [-typedNe_subst,veq,val_all,equalityCode] using! this
    simpa using replace_ne t u
  case hall =>
    intro p hp ih
    let φ : Semiformula V Presentation.language 2 := ⟨p, hp⟩
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (∀¹ φ).subst ![#'1] 🡒 (∀¹ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, typedEq_val, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using this
    have ih :
      (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ih
    suffices
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ∀¹ φ⤉⤉.subst ![#'0, &'1] 🡒 ∀¹ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!;
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    apply deduct'
    apply TProof.all_imp_all!
    apply deductInv'
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free, SemitermVec.q,
      Semiformula.shift_substs, Semiformula.substs_substs, one_add_one_eq_two]
    using TProof.specialize₂! ih (&'1) (&'2)
  case hexs =>
    intro p hp ih
    let φ : Semiformula V Presentation.language 2 := ⟨p, hp⟩
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (∃¹ φ).subst ![#'1] 🡒 (∃¹ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, typedEq_val, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using! this
    have ih :
      (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := U)).mpr
      simpa [equalityCode] using ih
    suffices
        (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 ∃¹ φ⤉⤉.subst ![#'0, &'1] 🡒 ∃¹ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!;
      simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    apply deduct'
    apply TProof.exs_imp_exs!
    apply deductInv'
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free, SemitermVec.q,
      Semiformula.shift_substs, Semiformula.substs_substs, one_add_one_eq_two]
      using TProof.specialize₂! ih (&'1) (&'2)

lemma replace' (φ : Semiformula V Presentation.language 1) :
    (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
  apply (tprovable_iff_provable (T := U)).mpr
  simpa [equalityCode] using replace_aux φ.val

lemma replace (φ : Semiformula V Presentation.language 1) (u₁ u₂ : Term V Presentation.language) :
    (U).internalize V ⊢ (u₁ ≐ₚ u₂) 🡒 φ.subst ![u₁] 🡒 φ.subst ![u₂] := by
  have := TProof.specialize₂! (replace' φ) u₂ u₁
  simpa [Semiformula.substs_substs] using this

#print axioms replace_aux
#print axioms replace'
#print axioms replace
end M6.PA.FoundationPAeqCode
