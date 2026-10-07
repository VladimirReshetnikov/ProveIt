import OAI.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
import OAI.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
import OAI.Combinatorics.Progressions.Linear.SubmoduleQuotientSectionBasis

namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι η V : Type*} [Fintype ι] [Fintype η]
  [AddCommGroup V] [Module ℚ V]

theorem basis_generator_matrix_range (b : Basis ι ℚ V) (v : η → V)
    (U : Submodule ℚ V) (hspan : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => b.repr (v j) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_submodule_quotient_presentation_exp_height
    [DecidableEq ι] (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ T : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap ∧ D * T = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((T i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((T i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_quotient_presentation_exp_height (fun i j => b.repr (v j) i)
      hHpos hv hp hrows hcols hH
  exact ⟨d, hd, D, T, hker.trans (basis_generator_matrix_range b v U hspan), hDT, hD, hT⟩

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct Classical

theorem exists_bounded_submodule_quotient_section_with_coordinates
    {ι η V : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ (eQ : Basis (Fin d) ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V) (qS : ℕ),
        Function.RightInverse S U.mkQ ∧
        Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
        (∀ i j, |(b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p + 2) ^ 45)) ∧
        (∀ j, (fun i => (b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        ∀ j i, RationalHeightLE (((eQ.coord j).comp U.mkQ) (b i))
          ⌈Real.exp ((p + 2) ^ 7)⌉₊ := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_submodule_quotient_presentation_exp_height b U v hspan hHpos hv hp hrows hcols hH
  obtain ⟨eQ, S, hright, hrightR, _hentryQ, hentryR, hcoord⟩ :=
    exists_submoduleQuotientSectionBasis_with_coordinates b U D T hker hDT
  have hdim : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simp only [Fintype.card_fin]
    exact (Nat.cast_le.mpr hd).trans hrows
  obtain ⟨habs, qS, _heq, hqS, hqSbound, hgrid⟩ :=
    rational_section_entry_budget T hp hrows hdim hT
  refine ⟨d, hd, eQ, S, qS, hright, hrightR, hqS, hqSbound, ?_, ?_, ?_⟩
  · intro i j
    rw [hentryR]
    exact habs i j
  · intro j
    choose z hz using fun i => hgrid i j
    refine ⟨z, ?_⟩
    funext i
    change (z i : ℝ) = (qS : ℝ) * (b.baseChange ℝ).repr
      (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i
    rw [hentryR]
    exact (hz i).symm
  · intro j i
    change RationalHeightLE (eQ.repr (U.mkQ (b i)) j) _
    rw [hcoord]
    exact ⟨Nat.cast_le.mp ((hD j i).1.trans (Nat.le_ceil _)),
      Nat.cast_le.mp ((hD j i).2.trans (Nat.le_ceil _))⟩

theorem exists_bounded_submodule_quotient_section
    {ι η V : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ (eQ : Basis (Fin d) ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V) (qS : ℕ),
        Function.RightInverse S U.mkQ ∧
        Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
        (∀ i j, |(b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p + 2) ^ 45)) ∧
        ∀ j, (fun i => (b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS := by
  obtain ⟨d, hd, eQ, S, qS, hright, hrightR, hqS, hqSbound, hentry, hgrid, _hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates b U v hspan hHpos hv
      hp hrows hcols hH
  exact ⟨d, hd, eQ, S, qS, hright, hrightR, hqS, hqSbound, hentry, hgrid⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

def allocatedCandidateCommonFastSectionInput (p : ℝ) : ℝ := (p + 2) ^ 4 + 1

def allocatedCandidateCommonFastGeometryLog (p : ℝ) : ℝ :=
  (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 + 1

noncomputable def allocatedCandidateCommonFastCoordinateHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((allocatedCandidateCommonFastSectionInput p + 2) ^ 7)⌉₊

theorem allocatedCandidateCommonFastSectionInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastSectionInput p ∧
    p ≤ allocatedCandidateCommonFastSectionInput p := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hp4 : p + 2 ≤ (p + 2) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (4 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastSectionInput]
  constructor <;> linarith

theorem allocatedCandidateCommonFastGeometryLog_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastGeometryLog p ∧
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastGeometryLog p := by
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hbase : 1 ≤ allocatedCandidateCommonFastSectionInput p + 2 := by linarith
  have hpow : allocatedCandidateCommonFastSectionInput p + 2 ≤
      (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (47 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastGeometryLog]
  constructor <;> linarith

theorem allocatedCandidateCommonFastCoordinateHeight_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
    (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  refine ⟨one_le_ceil_exp _, ?_⟩
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  apply (ceil_exp_le_exp_add_one (by positivity :
    0 ≤ (allocatedCandidateCommonFastSectionInput p + 2) ^ 7)).trans
  apply Real.exp_le_exp.mpr
  have hpow := pow_le_pow_right₀ (by linarith :
    1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 7 ≤ (47 : ℕ))
  dsimp [allocatedCandidateCommonFastGeometryLog]
  linarith only [hpow]

def allocatedCandidateCommonFastBudget (s : ℕ) (p : ℝ) : ℝ :=
  allocatedCandidateCommonFastGeometryLog p +
    NilpotentLieFiltration.pointwiseFastSectionInput s p

theorem allocatedCandidateCommonFastBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastBudget s p ∧
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤ allocatedCandidateCommonFastBudget s p ∧
    p ≤ allocatedCandidateCommonFastBudget s p := by
  have hgeom := allocatedCandidateCommonFastGeometryLog_bounds hp
  have hpoint : 0 ≤ NilpotentLieFiltration.pointwiseFastSectionInput s p := by
    dsimp [NilpotentLieFiltration.pointwiseFastSectionInput]
    positivity
  have hpg := (allocatedCandidateCommonFastSectionInput_bounds hp).2.trans hgeom.2
  dsimp [allocatedCandidateCommonFastBudget]
  constructor
  · linarith only [hpoint]
  constructor
  · linarith only [hgeom.1]
  · linarith only [hpg, hpoint]

theorem allocatedCandidateCommonFastGeneratorHeight_le {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  exact Real.exp_le_exp.mpr (allocatedCandidateCommonFastGeometryLog_bounds hp).2

theorem exists_allocatedCandidateCommonFastBudget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedCandidateCommonFastBudget s p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 4 + 1
  let A := (X + Polynomial.C (s + 3)) ^ (s + 3)
  let P := (Q + 2) ^ 47 + 1 + (2 * A + A ^ 2 + X)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, A, X, Polynomial.eval₂_pow, allocatedCandidateCommonFastBudget,
    allocatedCandidateCommonFastGeometryLog, allocatedCandidateCommonFastSectionInput,
    NilpotentLieFiltration.pointwiseFastSectionInput] using hbudget p hp

namespace NilpotentLieFiltration

variable {ι κ γ L M : Type*} [Fintype ι] [Fintype κ] [Fintype γ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)

local notation "fast" => W.map (F.associatedGradedMap G φ hφ)
local notation "bg" => G.associatedGradedBasis c ν hG

include hv hW in

theorem exists_allocatedCandidateCommonFastGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card κ ∧
      ∃ (eQ : Basis (Fin d) ℚ (G.AssociatedGraded ⧸ (fast).toSubmodule))
        (lift : (G.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] G.AssociatedGraded)
        (qS : ℕ),
        BasisGradedSubmodule bg ν (fast).toSubmodule ∧
        Function.RightInverse lift (fast).toSubmodule.mkQ ∧
        Function.RightInverse (lift.baseChange ℝ) ((fast).toSubmodule.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp (allocatedCandidateCommonFastGeometryLog p) ∧
        (∀ i j, |((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤
            Real.exp (allocatedCandidateCommonFastGeometryLog p)) ∧
        (∀ j, (fun i => ((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        (∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ) (bg i))
          (allocatedCandidateCommonFastCoordinateHeight p)) ∧
        1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
        (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
          Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  classical
  obtain ⟨hspan, hfast, hheight⟩ :=
    F.gradedImage_bounded_spanning G φ hφ b ω hF c ν hG W v hv hW hp hι hvH hφH
  have hq0 := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hpq := (allocatedCandidateCommonFastSectionInput_bounds hp).2
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSbound, hentry, hgrid, hθ⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates bg (fast).toSubmodule
      (F.gradedImageSpanningFamily G φ hφ v) hspan
      (one_le_ceil_exp ((p + 2) ^ 4))
      (fun i a => rationalHeightLE_ceil_exp (hheight a i))
      hq0 (hκ.trans hpq) (hγ.trans hpq)
      (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  refine ⟨d, hd, eQ, lift, qS, hfast, hsection, hsectionR, hqS, ?_, ?_, hgrid,
    hθ, allocatedCandidateCommonFastCoordinateHeight_bounds hp⟩
  · exact hqSbound.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num)))
  · intro i j
    apply (hentry i j).trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_right₀ (by linarith :
      1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 45 ≤ (47 : ℕ))).trans
    exact le_add_of_nonneg_right (by norm_num)

end NilpotentLieFiltration
end Erdos3

end

end OAI
