/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
import OAI.Combinatorics.Progressions.Polynomial.RaisedDegreeRank

namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem refiltered_lieTreeEval_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (d : I → ℕ) (v : I → L) (hv : ∀ i, v i ∈ F.gradedRefiltrationLayer U (d i))
    (a : FreeMagma I) : lieTreeEval v a ∈ F.gradedRefiltrationLayer U (lieTreeWeight d a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.gradedRefiltrationLayer_lie_mem U ha hb

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem refiltered_rank_bracket_frequency (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ξ η : L →ₗ[ℚ] ℚ)
    (hξ : ∀ x ∈ U,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω s x = x →
        D.filtration.gradedFrequency b ω hF ξ x = 0)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : I → L) (hv : ∀ i, v i ∈ D.filtration.gradedRefiltrationLayer U (d i)) :
    η (lieTreeEval v a) = 0 := by
  have htop : lieTreeEval v a ∈ D.filtration.gradedRefiltrationLayer U s := by
    simpa only [hd] using D.filtration.refiltered_lieTreeEval_mem U d v hv a
  have hleaves (i : I) : v i ∈ R.filtration.layer (d i) 1 := by
    have h := D.filtration.gradedRefiltrationLayer_le U (d i) (hv i)
    rw [← R.associated] at h
    change v i ∈ R.filtration.layer (d i) 0 at h
    rwa [R.filtration.rank_zero_eq_one] at h
  have hrank : lieTreeEval v a ∈ R.filtration.layer s r := by
    simpa only [hd, hr] using R.filtration.lieTreeEval_mem_length v d hleaves a
  rw [← hrestrict _ hrank]
  exact D.filtration.frequency_zero_on_refiltered_top b ω hF U ξ hξ _ htop

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_sub_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ξ η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (ξ - η) x = realifyFunctional ξ x - realifyFunctional η x := by
  induction x using TensorProduct.inductionOn with
  | tmul t v => simp only [realifyFunctional_tmul, LinearMap.sub_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

theorem realifyFunctional_eq_on_submodule {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℚ V) (ξ η : V →ₗ[ℚ] ℚ) (h : ∀ x ∈ P, ξ x = η x)
    (x : ℝ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℝ) :
    realifyFunctional ξ x = realifyFunctional η x := by
  have hker : P ≤ LinearMap.ker (ξ - η) := by
    intro y hy
    change ξ y - η y = 0
    exact sub_eq_zero.mpr (h y hy)
  have hz := (mem_realified_frequency_kernel_iff (ξ - η) x).mp (Submodule.baseChange_mono ℝ hker hx)
  rw [realifyFunctional_sub_apply] at hz
  exact sub_eq_zero.mp hz

namespace NilpotentLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_refiltered_lieTreeEval_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (d : I → ℕ) (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ F.realGradedRefiltrationLayer U (d i))
    (a : FreeMagma I) : lieTreeEval v a ∈ F.realGradedRefiltrationLayer U (lieTreeWeight d a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.realGradedRefiltrationLayer_lie_mem U ha hb

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem real_refiltered_rank_bracket_frequency (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ξ η : L →ₗ[ℚ] ℚ)
    (hξ : ∀ x ∈ U,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω s x = x →
        D.filtration.gradedFrequency b ω hF ξ x = 0)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) :
    realifyFunctional η (lieTreeEval v a) = 0 := by
  have htop : lieTreeEval v a ∈ D.filtration.realGradedRefiltrationLayer U s := by
    simpa only [hd] using D.filtration.real_refiltered_lieTreeEval_mem U d v hv a
  have hleaves (i : I) : v i ∈ R.filtration.realification.layer (d i) 1 := by
    have h : v i ∈ D.filtration.realification.layer (d i) :=
      D.filtration.realGradedRefiltrationLayer_le U (d i) (hv i)
    rw [← R.real_associated] at h
    change v i ∈ R.filtration.realification.layer (d i) 0 at h
    rwa [R.filtration.realification.rank_zero_eq_one] at h
  have hrank : lieTreeEval v a ∈ (R.filtration.layer s r).baseChange ℝ := by
    have h : lieTreeEval v a ∈ R.filtration.realification.layer s r := by
      simpa only [hd, hr] using R.filtration.realification.lieTreeEval_mem_length v d hleaves a
    exact h
  rw [← realifyFunctional_eq_on_submodule (R.filtration.layer s r) ξ η hrestrict _ hrank]
  exact D.filtration.real_frequency_zero_on_refiltered_top b ω hF U ξ hξ _ htop

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

def ControlledRankBracketFactorization (_R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (A P B : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin n → D.filtration.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ A * P * B = X ∧
    D.filtration.SymbolSlowBound D.basis ω hF (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.SymbolRationalGrid D.basis ω hF (fun _ => 1) m B ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
      lieTreeWeight d a = s → a.length = r →
      ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
    P.coord ∈ realificationLieSubalgebra (D.filtration.symbolPointwiseSubalgebra D.basis ω hF (fun _ => 1) U)

theorem controlledRankBracketFactorization_of_frequency_restriction (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (ξ η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (h : D.filtration.ControlledSymbolFactorization D.basis ω hF ξ T X p)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x) :
    R.ControlledRankBracketFactorization ω hF η T X p := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, hξ, hP⟩ := h
  refine ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, ?_, hP⟩
  intro k d a hd hr u hu
  exact R.real_refiltered_rank_bracket_frequency D.basis ω hF U ξ η hξ hrestrict d a hd hr u hu

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) :
    ∃ (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : Fin n → D.filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
      (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
        lieTreeWeight d a = s → a.length = r → ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
      D.filtration.SymbolFactorizationIn D.basis ω hF T X p l U := by
  obtain ⟨l, A, P, B, U, v, hl, hlp, hprod, hA, hB, hv, hU, hh, hker, hP⟩ := h
  exact ⟨l, U, v, hl, hlp, hv, hU, hh, hker, A, P, B, hprod, hA, hB, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : R.ControlledRankBracketFactorization ω hF η T X q := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hh, hη, hP⟩ := h
  exact ⟨m, A, P, B, U, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    D.filtration.symbolSlowBound_mono D.basis ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A hA,
    hB, hv, hU, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
