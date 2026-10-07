import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
import OAI.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]

theorem shearObservable_local_realEval (A : PolynomialSlots Y d P.weight) (u : Y → ℝ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono (A.loweringAt u)).patchValue P.kernel := by
  exact PolynomialSlots.shearObservable_eval_orbit P.form A P.weight_mono
    P.weight_pos P.weight_le P.kernel u

theorem shearObservable_local_integerEval (A : PolynomialSlots Y d P.weight) (u : Y → ℤ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u i : ℝ)))).patchValue P.kernel := by
  change P.shearObservable (QuotientGroup.mk
    ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitEval
      (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) = _
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact P.shearObservable_local_realEval A _

theorem fullSliceLaw_shearObservable_score [Fintype Y] [DecidableEq Y]
    (A : PolynomialSlots Y d P.weight) {N : Y → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (hq : 0 < q) (hlen : ∀ i, 0 < S.length i)
    (f : (Y → ℤ) → ℝ) (lam : ℝ) :
    (S.fullSliceLaw hlen).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (𝔼 u ∈ S.integerPoints, ((f u - lam : ℝ) : ℂ) *
        (P.shearObservable (QuotientGroup.mk
          ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
            (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) : ℂ)).re := by
  rw [S.fullSliceLaw_mean hlen, S.expect_integerPoints hq, Complex.re_expect]
  apply Finset.expect_congr rfl
  intro u _
  rw [P.shearObservable_local_integerEval]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {I : Type*} [Fintype I] [DecidableEq I]
  {keep : I → Prop} [DecidablePred keep] {N : I → ℕ} {q : ℕ}

theorem fiberSliceLaw_mean_eq_fullSliceLaw
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (test : (I → ℤ) → ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean (fun u => test u.val) =
      (S.fullSliceLaw hlen).mean (fun u => test (finiteSplitPoint keep u.val fixed)) := by
  rw [S.fiberSliceLaw_mean hlen fixed hfixed, S.fullSliceLaw_mean hlen]
  rfl

end ResidueBoxSlice

namespace PolynomialSlots

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {w : Fin d → ℕ}

noncomputable def coordinateFiberForm (A : PolynomialSlots I d w)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialSlots {i // keep i} d w :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberForm_loweringAt_integer (A : PolynomialSlots I d w)
    (keep : I → Prop) [DecidablePred keep] (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    (A.coordinateFiberForm keep fixed).loweringAt (fun i => (u i : ℝ)) =
      A.loweringAt (fun i => ((finiteSplitPoint keep u fixed i : ℤ) : ℝ)) := by
  rw [coordinateFiberForm, reparam_loweringAt]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

end PolynomialSlots

namespace PolynomialPatch

variable {X I : Type*} [Fintype I] [DecidableEq I] {s d : ℕ}
    (P : PolynomialPatch X s d)

theorem fiberSliceLaw_shear_score_eq_fullSliceLaw
    (A : PolynomialSlots I d P.weight) (keep : I → Prop) [DecidablePred keep]
    {N : I → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : (I → ℤ) → ℝ) (lam : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (S.fullSliceLaw hlen).mean (fun u => (f (finiteSplitPoint keep u.val fixed) - lam) *
        (P.form.shearTransformedSlots P.weight_mono
          ((A.coordinateFiberForm keep fixed).loweringAt
            (fun i => (u.val i : ℝ)))).patchValue P.kernel) := by
  rw [S.fiberSliceLaw_mean hlen fixed hfixed, S.fullSliceLaw_mean hlen]
  simp only [PolynomialSlots.coordinateFiberForm_loweringAt_integer]
  rfl

theorem fiberSliceLaw_shearObservable_score
    [Fintype (PolynomialShearIndex P.weight)]
    (A : PolynomialSlots I d P.weight) (keep : I → Prop) [DecidablePred keep]
    {N : I → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < S.length i) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : (I → ℤ) → ℝ) (lam : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (𝔼 u ∈ S.integerPoints, ((f (finiteSplitPoint keep u fixed) - lam : ℝ) : ℂ) *
        (P.shearObservable (QuotientGroup.mk
          ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
            (fun _ : {i // keep i} => 1) u
              ((A.coordinateFiberForm keep fixed).shearPolynomialOrbit s P.weight_le))) : ℂ)).re := by
  rw [P.fiberSliceLaw_shear_score_eq_fullSliceLaw A keep S hlen fixed hfixed f lam]
  exact P.fullSliceLaw_shearObservable_score (A.coordinateFiberForm keep fixed) S hq hlen
    (fun u => f (finiteSplitPoint keep u fixed)) lam

end PolynomialPatch

end Erdos3

end

end OAI
