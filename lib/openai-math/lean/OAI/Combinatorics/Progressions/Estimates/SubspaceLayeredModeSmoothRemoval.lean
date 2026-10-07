/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
import OAI.Combinatorics.Progressions.Linear.CoefficientModeRankContradiction

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem smoothProductPMF_translation_test_le {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (v : I → ℤ) :
    ‖(∑' x, ((smoothProductPMF S hS x).toReal : ℂ) * φ (x + v)) -
      ∑' x, ((smoothProductPMF S hS x).toReal : ℂ) * φ x‖ ≤
        4 * (3 : ℝ) ^ Fintype.card I *
          (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * ‖rectangularLatticePoint 0 S v‖) := by
  have hsmall' : (2 * (1 : ℝ) + 2) ^ Fintype.card I *
      ((Fintype.card I * probabilityProfileLipschitz : ℝ≥0) : ℝ) * δ ≤ 1 / 2 := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, show 2 * (1 : ℝ) + 2 = 4 by norm_num] using hsmall
  have hm := rectangular_profile_mass_lower (smoothProductProfile I) (smoothProductProfile_lipschitz I)
    0 S hS zero_le_one hδ hδ1 hmesh (smoothProductProfile_zero_outside I)
    (smoothProductProfile_integral I) hsmall'
  have ht := normalized_rectangular_translation_test_le (smoothProductProfile I)
    (smoothProductProfile_lipschitz I) 0 S hS1 zero_le_one
    (smoothProductProfile_zero_outside I) hm φ hφ v
  simpa only [smoothProductPMF, realWeightPMF_apply, rectangularWeight,
    rectangularLatticePoint_zero_origin, NNReal.coe_mul, NNReal.coe_natCast,
    show 2 * (1 : ℝ) + 1 = 3 by norm_num] using ht

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothProductPMF_toReal_sum {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' x, (smoothProductPMF S hS x).toReal) = 1 := by
  simp only [smoothProductPMF, realWeightPMF_apply, tsum_div_const]
  exact div_self (smoothProductSamples_sum_pos S hS).ne'

theorem smoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (x : I → ℤ)
    (hx : x ∉ rectangularWeightIndices 0 S 1) : (smoothProductPMF S hS x).toReal = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile I) 0 S hS
    (smoothProductProfile_zero_outside I) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [smoothProductPMF, realWeightPMF_apply, hz, zero_div]

theorem smoothProductPMF_shift_transfer {I X : Type*} [Fintype I] [Fintype X] [Nonempty X]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r B : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, ((smoothProductPMF S hS x).toReal : ℂ) * f x‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + B := by
  apply finite_probability_shift_transfer (fun x => (smoothProductPMF S hS x).toReal)
    (rectangularWeightIndices 0 S 1) (smoothProductPMF_toReal_zero_off S hS)
    (fun _ => ENNReal.toReal_nonneg) (smoothProductPMF_toReal_sum S hS) shift f _ hlocal
  intro u
  apply (smoothProductPMF_translation_test_le S hS hS1 hδ hδ1 hmesh hsmall f hf (shift u)).trans
  calc
    4 * (3 : ℝ) ^ Fintype.card I *
        (((Fintype.card I : ℝ) * probabilityProfileLipschitz) *
          ‖rectangularLatticePoint 0 S (shift u)‖) ≤
      4 * (3 : ℝ) ^ Fintype.card I *
        (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r) := by
      gcongr
      exact hshift u
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem smooth_row_shift_transfer {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    {h : ℕ} (N s : I → ℕ) (hN : ∀ i, 0 < N i) (rows : Fin h → K → ℤ)
    (S : K × I → ℝ) (hS : ∀ z, 0 < S z) (hS1 : ∀ z, 1 ≤ S z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / S z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hscale : ∀ z, (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * S z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (s j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B) :
    ‖∑' z : K × I → ℤ,
      ((smoothProductPMF S hS z).toReal : ℂ) * Φ (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  apply smoothProductPMF_shift_transfer S hS hS1 hδ hδ1 hmesh hsmall
    (integerRowShift (N := N) rows s)
    (fun x => integerRowShift_normalized_bound rows s x S hS hC hrows hr hscale)
    (fun z => Φ (fun k j => (z (k, j) : ℝ))) (fun z => hΦ _)
  intro z
  simpa only [integerRowShift_real] using hlocal (fun k j => (z (k, j) : ℝ))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficient_mode_finite_removal {I K J S : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype S] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N s : I → ℕ) (hs : ∀ k, 0 < s k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : S → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (base : K → I → ℝ) (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1) :
    let shift : (∀ k, Fin (N k)) → I → ℝ := fun x k => (s k : ℝ) * ((x k).val : ℝ)
    let L := coefficientFunctional (fun d j => (frequency d j : ℝ))
    ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base a shift x k j)) p) +
        MvPolynomial.eval (fun z => rowShiftedTuple base a shift x z.1 z.2) Q : ℝ) :
          CircleFourier.Circle) *
      ∏ t, test t (integerSiteValue (site t) (rowShiftedTuple base a shift x))‖ ^ (2 ^ (n + 1)) < ζ := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hNp k⟩⟩
  have hcs := coefficient_mode_with_lower_site_cauchySchwarz (Nat.succ_pos n) site a hzero base
    (fun (x : ∀ k, Fin (N k)) k => (s k : ℝ) * ((x k).val : ℝ))
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) p hp Q hQ test htest
  exact hcs.trans_lt (coefficientMode_paired_bias_lt_of_rank frequency a p hp W N s hs hζ hN
    H hH hA hscale hrank hrow hrowBudget hnonzero hdenom hcoeff)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

noncomputable def coefficientModeTestedPhase {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ t, test t (integerSiteValue (site t) b)

theorem coefficientModeTestedPhase_norm_le {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1) (b : K → I → ℝ) :
    ‖coefficientModeTestedPhase L p Q site test b‖ ≤ 1 := by
  rw [coefficientModeTestedPhase, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one₀ (fun t _ => norm_nonneg _) (fun t _ => htest t _)

theorem coefficient_mode_smooth_removal {I K J T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype T] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : T → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r β : ℝ} (hC : 0 ≤ C) (ha : ∀ i k, |(a i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, ((n + 1 : ℕ) : ℝ) * C * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (n + 1))) :
    ‖∑' z : K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      coefficientModeTestedPhase (coefficientFunctional (fun d j => (frequency d j : ℝ)))
        p Q site test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  apply smooth_row_shift_transfer N stride hNp a V hV hV1 hδ hδ1 hmesh hsmall hC ha hr hmove
    (coefficientModeTestedPhase (coefficientFunctional (fun d j => (frequency d j : ℝ))) p Q site test)
    (coefficientModeTestedPhase_norm_le _ p Q site test htest)
  intro b
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hβ
  have h := coefficient_mode_finite_removal frequency a p hp W N stride hs hζ hN H hH hA hscale
    hrank hrow hrowBudget hnonzero hdenom hcoeff site hzero b Q hQ test htest
  exact (show _ < ζ from h).le.trans hpower

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def lowerModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) :
    MvPolynomial (K × I) ℝ := coefficientModePolynomial L (p - homogeneousPart h p) + Q

theorem lowerModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    {n : ℕ} (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1) :
    (lowerModePolynomial L (n + 1) p Q).totalDegree < n + 1 := by
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
  apply max_lt
  · exact (coefficientModePolynomial_degreeLE L _ (sub_homogeneousPart_degreeLE hp)).trans_lt
      (Nat.lt_succ_self n)
  · exact hQ

theorem lowerModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) (b : K → I → ℝ) :
    L (substitute (fun j => rowPolynomial (fun k => b k j)) (homogeneousPart h p)) +
      MvPolynomial.eval (fun z => b z.1 z.2) (lowerModePolynomial L h p Q) =
    L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q := by
  rw [lowerModePolynomial, map_add, coefficientModePolynomial_eval, map_sub, map_sub]
  ring

theorem coefficientModeTestedPhase_top {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase L p Q site test b =
      coefficientModeTestedPhase L (homogeneousPart h p) (lowerModePolynomial L h p Q) site test b := by
  unfold coefficientModeTestedPhase
  rw [lowerModePolynomial_eval]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem inhomogeneous_coefficient_mode_local_removal {I K J T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype T] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : T → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (n + 1)))
    (base : K → I → ℝ) :
    ‖𝔼 x : Fin (n + 1) → ∀ j, Fin (N j),
      coefficientModeTestedPhase (coefficientFunctional (fun d j => (frequency d j : ℝ)))
        p Q site test (rowShiftedTuple base a
          (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  have he (b : K → I → ℝ) := coefficientModeTestedPhase_top
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) (n + 1) p Q site test b
  simp_rw [he]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hβ
  exact (coefficient_mode_finite_removal frequency a (homogeneousPart (n + 1) p)
    (homogeneousPart_homogeneous _ _) W N stride hs hζ hN H hH hA hscale
    ((hasLayerSamplingRank_homogeneousPart_iff _ _ _ _ _).mpr hrank)
    hrow hrowBudget hnonzero hdenom hcoeff site hzero base
    (lowerModePolynomial _ (n + 1) p Q) (lowerModePolynomial_degree _ p hp Q hQ)
    test htest).le.trans hpower

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

theorem inhomogeneous_coefficient_mode_smooth_removal {I K J T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype T] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : T → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r β : ℝ} (hC : 0 ≤ C) (ha : ∀ i k, |(a i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, ((n + 1 : ℕ) : ℝ) * C * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (n + 1))) :
    ‖∑' z : K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      coefficientModeTestedPhase (coefficientFunctional (fun d j => (frequency d j : ℝ)))
        p Q site test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  have he (b : K → I → ℝ) := coefficientModeTestedPhase_top
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) (n + 1) p Q site test b
  simp_rw [he]
  exact coefficient_mode_smooth_removal frequency a (homogeneousPart (n + 1) p)
    (homogeneousPart_homogeneous _ _) W N stride hs hζ hN H hH hA hscale
    ((hasLayerSamplingRank_homogeneousPart_iff _ _ _ _ _).mpr hrank)
    hrow hrowBudget hnonzero hdenom hcoeff site hzero
    (lowerModePolynomial _ (n + 1) p Q) (lowerModePolynomial_degree _ p hp Q hQ)
    test htest V hV hV1 hδ hδ1 hmesh hsmall hC ha hr hmove hβ hpower

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def lowerLayerPolynomial {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) : MvPolynomial (K × I) ℝ :=
  ∑ j, if j < i then coefficientModePolynomial (L j) (p j) else 0

theorem lowerLayerPolynomial_degree {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) :
    (lowerLayerPolynomial i L p).totalDegree < i.val + 1 := by
  apply lt_of_le_of_lt (b := i.val) _ (Nat.lt_succ_self _)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  by_cases hji : j < i
  · rw [ite_eq_left hji]
    exact (coefficientModePolynomial_degreeLE (L j) (p j) (hp j)).trans
      (Nat.succ_le_of_lt hji)
  · simp [hji]

theorem lowerLayerPolynomial_eval {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    MvPolynomial.eval (fun z => b z.1 z.2) (lowerLayerPolynomial i L p) =
      ∑ j, if j < i then L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) else 0 := by
  rw [lowerLayerPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j < i <;> simp [hji, coefficientModePolynomial_eval]

noncomputable def layeredModeTestedPhase {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) b)

theorem exists_layered_mode_reduction {I K S : Type*} [Fintype K] [Fintype S] [DecidableEq S]
    {m : ℕ} {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)] (i : Fin m)
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  classical
  let Q' := lowerLayerPolynomial i L p + Q
  have hQ' : Q'.totalDegree < i.val + 1 :=
    lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
      (max_lt (lowerLayerPolynomial_degree i L p hp) hQ)
  let low (b : K → I → ℝ) :=
    L i (substitute (fun u => rowPolynomial (fun k => b k u)) (p i)) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q'
  obtain ⟨test', ht, he⟩ := exists_absorbed_integer_site_tests
    (fun j : {j : Fin m // i < j} => j.val.val + 1) site
    (fun j => L j.val) (fun j => hfactor j.val j.property)
    (fun j => p j.val) (fun j => hp j.val) low test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  have hsplit : (∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q = low b +
      ∑ j : {j : Fin m // i < j},
        L j.val (substitute (fun u => rowPolynomial (fun k => b k u)) (p j.val)) := by
    rw [sum_split_at_layer i]
    dsimp [low, Q']
    rw [map_add, lowerLayerPolynomial_eval]
    ring
  unfold layeredModeTestedPhase
  rw [hsplit]
  exact he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem layeredModeTestedPhase_norm_le {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ)
    (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredModeTestedPhase L p Q site test b‖ ≤ 1 := by
  rw [layeredModeTestedPhase, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one₀ (fun s _ => norm_nonneg _) (fun s _ => htest s _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

theorem layered_mode_smooth_removal {I K T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype T] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (i : Fin m)
    (frequency : (K →₀ ℕ) → J i → ℤ) (a : Fin (i.val + 1) → K → ℤ)
    (L : ∀ j, VectorPolynomial K ℝ (J j → ℝ) →ₗ[ℝ] ℝ)
    (hL : L i = coefficientFunctional (fun d j => (frequency d j : ℝ)))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (W : Submodule ℝ (J i → ℝ)) (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (i.val + 1) H R W (p i))
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((i.val + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (site : T → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (T → J j → ℝ) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j q = M (siteEvaluation (fun t k => (site t k : ℝ)) q))
    (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r β : ℝ} (hC : 0 ≤ C) (ha : ∀ i k, |(a i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, ((i.val + 1 : ℕ) : ℝ) * C * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase L p Q site test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_layered_mode_reduction i L p hp site hfactor Q hQ test htest
  simp_rw [he, hL]
  exact inhomogeneous_coefficient_mode_smooth_removal frequency a (p i) (hp i)
    W N stride hs hζ hN H hH hA hscale hrank hrow hrowBudget hnonzero hdenom hcoeff
    site hzero Q' hQ' test' ht V hV hV1 hδ hδ1 hmesh hsmall hC ha hr hmove hβ hpower

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_restrictCoefficients {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (p : VectorPolynomial I ℝ V) (hm : ∀ d, coefficients p d ∈ U)
    {w : I → ℕ} {h : ℕ} (hp : DegreeLE w h p) : DegreeLE w h (restrictCoefficients U p hm) := by
  apply (degreeLE_map_iff w h U.subtype Subtype.val_injective _).mp
  simpa only [map_restrictCoefficients] using hp

theorem coefficientModeTestedPhase_map {I K S V W : Type*} [Fintype K] [Fintype S]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ V) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase (L.comp (map f)) p Q site test b =
      coefficientModeTestedPhase L (map f p) Q site test b := by
  simp only [coefficientModeTestedPhase, LinearMap.comp_apply, map_substitute]

theorem layeredModeTestedPhase_map {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {V W : Fin m → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (f : ∀ j, V j →ₗ[ℝ] W j) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase (fun j => (L j).comp (map (f j))) p Q site test b =
      layeredModeTestedPhase L (fun j => map (f j) (p j)) Q site test b := by
  simp only [layeredModeTestedPhase, LinearMap.comp_apply, map_substitute]

theorem exists_subspace_layered_mode_reduction {I K S : Type*}
    [Fintype K] [Fintype S] [DecidableEq S] {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)] (i : Fin m)
    (U : ∀ j, Submodule ℝ (V j)) (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j (map (U j).subtype q) = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  let p' := fun j => restrictCoefficients (U j) (p j) (hm j)
  have hp' j : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_layered_mode_reduction i
    (fun j => (L j).comp (map (U j).subtype)) p' hp' site hfactor Q hQ test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  simpa only [layeredModeTestedPhase_map, coefficientModeTestedPhase_map, p',
    map_restrictCoefficients] using he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

theorem subspace_layered_mode_smooth_removal {I K T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype T] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (i : Fin m)
    (frequency : (K →₀ ℕ) → J i → ℤ) (a : Fin (i.val + 1) → K → ℤ)
    (L : ∀ j, VectorPolynomial K ℝ (J j → ℝ) →ₗ[ℝ] ℝ)
    (hL : L i = coefficientFunctional (fun d j => (frequency d j : ℝ)))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((i.val + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : U i,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (site : T → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (T → U j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j (map (U j).subtype q) = M (siteEvaluation (fun t k => (site t k : ℝ)) q))
    (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r β : ℝ} (hC : 0 ≤ C) (ha : ∀ i k, |(a i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, ((i.val + 1 : ℕ) : ℝ) * C * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase L p Q site test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_subspace_layered_mode_reduction i U L p hm hp site hfactor Q hQ test htest
  simp_rw [he, hL]
  exact inhomogeneous_coefficient_mode_smooth_removal frequency a (p i) (hp i)
    (U i) N stride hs hζ hN H hH hA hscale hrank hrow hrowBudget hnonzero hdenom hcoeff
    site hzero Q' hQ' test' ht V hV hV1 hδ hδ1 hmesh hsmall hC ha hr hmove hβ hpower

end Erdos3.VectorPolynomial

end

end OAI
