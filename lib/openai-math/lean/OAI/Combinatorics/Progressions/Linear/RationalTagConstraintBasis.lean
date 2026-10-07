/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {η B κ : Type*} [Fintype η] [Fintype B]

theorem realRationalCoordinateSpan_iInf (U : η → Submodule ℚ (B → ℚ)) :
    realRationalCoordinateSpan (⨅ a, U a) = ⨅ a, realRationalCoordinateSpan (U a) := by
  unfold realRationalCoordinateSpan
  rw [real_baseChange_iInf]
  apply Submodule.map_iInf_of_ker_le realRationalCoordinateEquiv.surjective
  rw [LinearMap.ker_eq_bot.mpr realRationalCoordinateEquiv.injective]
  exact bot_le

theorem realRationalCoordinateSpan_top :
    realRationalCoordinateSpan (⊤ : Submodule ℚ (B → ℚ)) = ⊤ := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr realRationalCoordinateEquiv.surjective

theorem realRationalCoordinateSpan_iInf_basis (U : η → Submodule ℚ (B → ℚ))
    (b : Basis κ ℚ ↥(⨅ a, U a)) :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      ⨅ a, realRationalCoordinateSpan (U a) := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = ⨅ a, U a := by
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.subtype_apply,
      Submodule.map_top, Submodule.range_subtype] using
      congrArg (Submodule.map (⨅ a, U a).subtype) b.span_eq
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    ((congrArg realRationalCoordinateSpan hb).trans (realRationalCoordinateSpan_iInf U))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def rationalTagConstraintIntersection (cs : List (RationalTagConstraint J))
    (j : Fin m) : Submodule ℚ (J j → ℚ) :=
  ⨅ i : Fin cs.length, (cs.get i).rationalSpace j

theorem exists_rationalTagConstraintList_basis
    (cs : List (RationalTagConstraint J)) (j : Fin m) {p : ℝ}
    (hp : 0 ≤ p) (hdim : (Fintype.card (J j) : ℝ) ≤ p)
    (hlen : (cs.length : ℝ) ≤ p) (hcs : ∀ c ∈ cs, c.BudgetLE p) :
    ∃ n : ℕ, n ≤ Fintype.card (J j) ∧
      ∃ b : Basis (Fin n) ℚ (rationalTagConstraintIntersection cs j),
        ∀ a i, rationalLogHeight ((b a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  choose v hv hheight using fun i : Fin cs.length =>
    (cs.get i).exists_rationalSpace_spanning j hp (hcs _ (List.get_mem _ _))
  obtain ⟨n, hn, b, hb⟩ := exists_submodule_intersection_basis_logHeight
    (Pi.basisFun ℚ (J j)) (fun i : Fin cs.length => (cs.get i).rationalSpace j)
    v hv hp hdim (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hlen) hheight
  exact ⟨n, hn, b, hb⟩

private theorem constraint_realSpaces_member_iff {X : Type*}
    (c : RationalTagConstraint J) (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (c.rationalSpace j)) ↔
      c.member point := by
  constructor
  · intro h
    simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
      RationalTagConstraint.member] using h c.tag
  · intro h j
    by_cases hj : j = c.tag
    · subst j
      simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
        RationalTagConstraint.member] using h
    · rw [c.rationalSpace_of_ne hj, realRationalCoordinateSpan_top]
      trivial

theorem rationalTagConstraintList_basis_member_iff {X : Type*}
    (cs : List (RationalTagConstraint J)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (rationalTagConstraintIntersection cs j))
    (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ c ∈ cs, c.member point := by
  have hspan (j : Fin m) :
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ))) =
        ⨅ k : Fin cs.length, realRationalCoordinateSpan ((cs.get k).rationalSpace j) :=
    realRationalCoordinateSpan_iInf_basis
      (fun k : Fin cs.length => (cs.get k).rationalSpace j) (b j)
  simp_rw [hspan, Submodule.mem_iInf]
  constructor
  · intro h c hc
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    apply (constraint_realSpaces_member_iff c point).mp
    intro j
    simpa only [hk] using h j k
  · intro h j k
    exact (constraint_realSpaces_member_iff (cs.get k) point).mpr
      (h _ (List.get_mem _ _)) j

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases {X : Type*}
    {Kinitial K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Kinitial K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = Kinitial ∩ {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  classical
  obtain ⟨cs, hlen, hbudget, hK⟩ := hcert
  have hl : (cs.length : ℝ) ≤ p := (Nat.cast_le.mpr hlen).trans hblocks
  choose n hn b hb using fun j =>
    exists_rationalTagConstraintList_basis cs j hp (hdim j) hl hbudget
  refine ⟨rationalTagConstraintIntersection cs, n, b, hn, hb, ?_⟩
  rw [hK]
  ext point
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    rationalTagConstraintList_basis_member_iff cs n b point]

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases_univ {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases hp hdim hblocks
  exact ⟨W, n, b, hn, hb, by simpa only [Set.univ_inter] using hK⟩

end Erdos3.VectorPolynomial

end

end OAI
