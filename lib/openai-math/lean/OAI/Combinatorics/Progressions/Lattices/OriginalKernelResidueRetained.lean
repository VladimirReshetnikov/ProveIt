import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.FiniteProductWeightL1
import OAI.Combinatorics.Progressions.Geometry.PrincipalCoefficientPositiveSupport
import OAI.Combinatorics.Progressions.Linear.KernelProductFiber

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_residue_weight (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] (v : ℤ) :
    ((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight (v : ZMod q) =
      ((Finset.filter (fun x => x ≡ v [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  simp only [FiniteProbabilityWeights.fiberLaw, FiniteProbabilityWeights.fiberMean]
  simp only [ZMod.intCast_eq_intCast_iff]
  rw [intervalUniformWeights_mean]
  exact @integerInterval_indicator_expect a b hab.le
    (fun x : ℤ => x ≡ v [ZMOD (q : ℤ)]) (fun _ => Int.instDecidableModEq)

theorem intervalUniformWeights_residue_weight_error (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] (r : ZMod q) :
    |((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight r - 1 / (q : ℝ)| ≤
      1 / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hr : (((r.val : ℕ) : ℤ) : ZMod q) = r := by simp
  rw [← hr, intervalUniformWeights_residue_weight]
  have hc := scalarResidue_card_absolute_error a b q r.val hab.le hq
  have heq :
      ((Finset.filter (fun x => x ≡ (r.val : ℤ) [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) - 1 / (q : ℝ) =
      (((Finset.filter (fun x => x ≡ (r.val : ℤ) [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) - ((b - a : ℤ) : ℝ) / (q : ℝ)) /
          ((b - a : ℤ) : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right (by simpa only [Int.cast_natCast] using hc) hL.le

theorem intervalUniformWeights_residue_l1_error (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] :
    (∑ r : ZMod q, |((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight r - 1 / (q : ℝ)|) ≤
      (q : ℝ) / ((b - a : ℤ) : ℝ) := by
  calc
    _ ≤ ∑ _r : ZMod q, 1 / ((b - a : ℤ) : ℝ) := by
      exact Finset.sum_le_sum (fun r _ => intervalUniformWeights_residue_weight_error a b hab q r)
    _ = _ := by simp [ZMod.card, div_eq_mul_inv]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem scalarCubeResidueWeights_pi_complex_riemann {G I : Type*}
    [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (L M : G → ℕ) (hL : ∀ g, 0 < L g) (m : G → Option I → ℕ)
    (r : ∀ g i, ZMod (m g i)) (hm : ∀ g i, 0 < m g i)
    (hmM : ∀ g i, m g i ≤ M g)
    (hsize : ∀ g, (Fintype.card I + 1) * M g ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant I * ((M g : ℝ) / L g) <
      volume.real (scalarCubeDomain I))
    (φ : (G → Option I → ℝ) → ℂ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I (L g) (M g) (hL g)
      (m g) (r g) (hm g) (hmM g) (hsize g))).complexMean
        (fun z => φ (fun g i => (z g i : ℝ) / L g)) -
      ∫ x, φ x ∂scalarCubeProductMeasure G I‖ ≤
      2 * (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ g, (M g : ℝ) / L g := by
  have hreLip : LipschitzWith K (fun x => (φ x).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have himLip : LipschitzWith K (fun x => (φ x).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have hre := scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall
    (fun x => (φ x).re) hreLip hB
    (fun x => (Complex.abs_re_le_norm _).trans (hb x))
  have him := scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall
    (fun x => (φ x).im) himLip hB
    (fun x => (Complex.abs_im_le_norm _).trans (hb x))
  have hi : Integrable φ (scalarCubeProductMeasure G I) :=
    Integrable.mono' (integrable_const B) hφ.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have hire : (∫ x, φ x ∂scalarCubeProductMeasure G I).re =
      ∫ x, (φ x).re ∂scalarCubeProductMeasure G I := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hi).symm
  have hiim : (∫ x, φ x ∂scalarCubeProductMeasure G I).im =
      ∫ x, (φ x).im ∂scalarCubeProductMeasure G I := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hi).symm
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have h := add_le_add hre him
  simpa only [Complex.sub_re, Complex.sub_im, FiniteProbabilityWeights.complexMean_re,
    FiniteProbabilityWeights.complexMean_im, hire, hiim, ← two_mul, mul_assoc] using h

variable {G I : Type*} [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]

theorem kernelResidue_joint_complex_riemann (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (r : G → Option I → ZMod q)
    (hsize : (Fintype.card I + 1) * q ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((q : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (F : (G → Option I → ZMod q) → (G → Option I → ℝ) → ℂ)
    {K : ℝ≥0} {B : ℝ} (hF : LipschitzWith K (F r))
    (hB : 0 ≤ B) (hbound : ∀ x, ‖F r x‖ ≤ B) :
    ‖(FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I L q hL
        (fun _ => q) (r g) (fun _ => hq) (fun _ => le_rfl) hsize)).complexMean
        (fun z => F (fun g i => ((z g i : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L)) -
      ∫ x, F r x ∂scalarCubeProductMeasure G I‖ ≤
      2 * (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        (Fintype.card G * ((q : ℝ) / L)) := by
  have he := (FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I L q hL
    (fun _ => q) (r g) (fun _ => hq) (fun _ => le_rfl) hsize)).complexMean_congr_support
    (f := fun z => F (fun g i => ((z g i : ℤ) : ZMod q)) (fun g i => (z g i : ℝ) / L))
    (g := fun z => F r (fun g i => (z g i : ℝ) / L)) (by
      intro z hz
      have hr := scalarCubeResiduePi_support (fun _ : G => L) (fun _ => q) (fun _ => hL)
        (fun _ _ => q) r (fun _ _ => hq) (fun _ _ => le_rfl) (fun _ => hsize) z hz
      rw [show (fun g i => ((z g i : ℤ) : ZMod q)) = r from funext (fun g => funext (hr g))])
  rw [he]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    scalarCubeResidueWeights_pi_complex_riemann (fun _ : G => L) (fun _ => q) (fun _ => hL)
      (fun _ _ => q) r (fun _ _ => hq) (fun _ _ => le_rfl) (fun _ => hsize)
      (fun _ => hsmall) (F r) hF hB hbound

theorem kernelResidue_polynomial_complex_riemann (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (r : G → Option I → ZMod q)
    (hsize : (Fintype.card I + 1) * q ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((q : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    {Out : Type*} (poly : Out → MvPolynomial (G × Option I) ℤ)
    (φ : (Out → ZMod q) → (G → Option I → ℝ) → ℂ)
    {K : ℝ≥0} {B : ℝ} (hφ : ∀ v, LipschitzWith K (φ v))
    (hB : 0 ≤ B) (hbound : ∀ v x, ‖φ v x‖ ≤ B) :
    ‖(FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I L q hL
        (fun _ => q) (r g) (fun _ => hq) (fun _ => le_rfl) hsize)).complexMean
        (fun z => φ (fun o => ((MvPolynomial.eval (fun a => (z a.1 a.2 : ℤ)) (poly o) : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L)) -
      ∫ x, φ (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (fun a => r a.1 a.2) (poly o)) x ∂scalarCubeProductMeasure G I‖ ≤
      2 * (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        (Fintype.card G * ((q : ℝ) / L)) := by
  let F := fun (v : G → Option I → ZMod q) =>
    φ (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (fun a => v a.1 a.2) (poly o))
  have h := kernelResidue_joint_complex_riemann L q hL hq r hsize hsmall
    F (hφ _) hB (hbound _)
  have heval (p : MvPolynomial (G × Option I) ℤ) (v : G × Option I → ℤ) :
      ((MvPolynomial.eval v p : ℤ) : ZMod q) =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod q)) (fun a => (v a : ZMod q)) p :=
    integerPolynomial_eval_residue p q v
  simpa only [F, heval] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
variable (q : ℕ) (hq : 0 < q) (r : ZMod q)
variable (hlength : scalarCubeNormalizationThreshold Empty q 32
  (256 * probabilityProfileLipschitz) ≤ principalIntervalLength K T γ)

include hK hT hγ hlarge in
theorem principalCoefficientResidue_normalizer_lower :
    let hs := scalarCubeNormalizationThreshold_spec Empty hlength
    1 / 2 ≤ (scalarCubeResidueWeights Empty (principalIntervalLength K T γ) q hs.1
      (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1).mean
      (fun z => principalIntervalWeight K T γ
        (fun i => (z i : ℝ) / principalIntervalLength K T γ)) := by
  let L := principalIntervalLength K T γ
  let w := principalIntervalWeight K T γ
  have hs := scalarCubeNormalizationThreshold_spec Empty hlength
  have hw := principalIntervalWeight_range hK hT hγ hlarge
  have hLip := principalIntervalWeight_lipschitz hK hT hγ hlarge
  have ht : (q : ℝ) * scalarCubeRiemannAllowance Empty 16
      (128 * probabilityProfileLipschitz) / (1 / 4) ≤ L := by
    convert hs.2.2.2 using 1
    simp only [scalarCubeRiemannAllowance, NNReal.coe_mul, NNReal.coe_ofNat]
    ring
  have hb (x) : ‖w x‖ ≤ (16 : ℝ) := by
    rw [Real.norm_of_nonneg (hw x).1]
    exact (hw x).2
  have hr := scalarCubeResidueWeights_riemann_of_length Empty L q hs.1
    (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1 w hLip
    (by norm_num : (0 : ℝ) ≤ 16) hb (by norm_num : (0 : ℝ) < 1 / 4)
    hs.2.2.1 ht
  have h1 := scalarCubeResidueWeights_riemann_of_length Empty L q hs.1
    (fun _ => 1) (fun _ => 0) (fun _ => by norm_num) (fun _ => hq) hs.2.1 w hLip
    (by norm_num : (0 : ℝ) ≤ 16) hb (by norm_num : (0 : ℝ) < 1 / 4)
    hs.2.2.1 ht
  have hn : (scalarCubeResidueWeights Empty L q hs.1 (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => hq) hs.2.1).mean
      (fun z => w (fun i => (z i : ℝ) / L)) = 1 :=
    (principalNormalizedSource hK hT hγ hlarge).normalized
  rw [hn] at h1
  have h1' := (abs_le.mp h1).2
  have hr' := (abs_le.mp hr).1
  dsimp only
  linarith

noncomputable def principalCoefficientResidueSource : NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfWeight Empty (principalIntervalLength K T γ) q
    (scalarCubeNormalizationThreshold_spec Empty hlength).1 (fun _ => q) (fun _ => r)
    (fun _ => hq) (fun _ => le_rfl)
    (scalarCubeNormalizationThreshold_spec Empty hlength).2.1
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalCoefficientResidue_normalizer_lower hK hT hγ hlarge q hq r hlength)

theorem principalCoefficientResidueSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget
      (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength) A
      (scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q) := by
  apply scalarCubePrimitiveBudget_of_raw_bounds _ A 32 (256 * probabilityProfileLipschitz) q
  · exact le_rfl
  · norm_num [principalCoefficientResidueSource, normalizedScalarCubeSourceOfWeight]
  · change 2 * (128 * probabilityProfileLipschitz) ≤ 256 * probabilityProfileLipschitz
    simp only [← mul_assoc]
    norm_num

private theorem weights_ext {X : Type*} [Fintype X] {p q : FiniteProbabilityWeights X}
    (h : ∀ x, p.weight x = q.weight x) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

private theorem residue_one_eq_uniform (L : ℕ) (hL : 0 < L) (hsize : 1 ≤ L) :
    scalarCubeResidueWeights Empty L 1 hL (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => le_rfl) (by simpa using hsize) =
      integerScalarCubeWeights Empty L hL := by
  classical
  let p := integerScalarCubeWeights Empty L hL
  have hr : scalarCubeResidueSet Empty L (fun _ => 1) (fun _ => 0) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro z
    apply (mem_scalarCubeResidueSet L (fun _ => 1) (fun _ => 0) z).mpr
    intro i
    exact Subsingleton.elim _ _
  have hm : p.mass Finset.univ = 1 := p.total
  apply weights_ext
  intro z
  change (p.condition _ _).weight z = p.weight z
  simp only [FiniteProbabilityWeights.condition, hr, Finset.mem_univ, ite_true, hm, div_one]

private theorem principalSource_baseLaw :
    (principalNormalizedSource hK hT hγ hlarge).baseLaw =
      integerScalarCubeWeights Empty (principalIntervalLength K T γ)
        (principalIntervalLength_pos hK hT hγ) :=
  residue_one_eq_uniform _ _ (Nat.succ_le_iff.mpr (principalIntervalLength_pos hK hT hγ))

private theorem reweight_mass_eq {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hn : p.mean w = 1) (G : Finset X) (hG : 0 < p.mass G) :
    (p.reweight w hw hn).mass G = p.mass G * (p.condition G hG).mean w := by
  rw [FiniteProbabilityWeights.mass_mul_condition_mean]
  simp [FiniteProbabilityWeights.mass, FiniteProbabilityWeights.mean,
    FiniteProbabilityWeights.reweight, mul_ite]

private theorem reweight_condition_weight {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hn : p.mean w = 1) (G : Finset X) (hG : 0 < p.mass G)
    (hGw : 0 < (p.reweight w hw hn).mass G) (z : X) :
    (p.condition G hG).weight z * (w z / (p.condition G hG).mean w) =
      ((p.reweight w hw hn).condition G hGw).weight z := by
  simp only [FiniteProbabilityWeights.condition]
  rw [reweight_mass_eq p w hw hn G hG]
  by_cases hz : z ∈ G
  · simp only [hz, ite_true, FiniteProbabilityWeights.reweight]
    change p.weight z / p.mass G * (w z / (p.condition G hG).mean w) =
      (p.weight z * w z) / (p.mass G * (p.condition G hG).mean w)
    ring
  · simp only [hz, ite_false, zero_div, zero_mul]

include hq hlength in
theorem principalCoefficientResidue_mass_pos :
    0 < (principalNormalizedSource hK hT hγ hlarge).source.mass
      (scalarCubeResidueSet Empty (principalIntervalLength K T γ)
        (fun _ => q) (fun _ => r)) := by
  let s := principalNormalizedSource hK hT hγ hlarge
  let G := scalarCubeResidueSet Empty (principalIntervalLength K T γ)
    (fun _ => q) (fun _ => r)
  have hs := scalarCubeNormalizationThreshold_spec Empty hlength
  have hG := scalarCubeResidue_mass_pos Empty (principalIntervalLength K T γ) q hs.1
    (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1
  have hGb : 0 < s.baseLaw.mass G := by
    rw [principalSource_baseLaw]
    exact hG
  have he := reweight_mass_eq s.baseLaw _ (fun z => (s.weight_range _).1) s.normalized G hGb
  change s.source.mass G = _ at he
  rw [he]
  apply mul_pos hGb
  have hz := principalCoefficientResidue_normalizer_lower hK hT hγ hlarge q hq r hlength
  have hz' : 1 / 2 ≤ (s.baseLaw.condition G hGb).mean
      (fun z => s.weight (fun i => (z i : ℝ) / s.length)) := by
    simp only [s, principalSource_baseLaw]
    exact hz
  linarith

theorem principalCoefficientResidueSource_law :
    (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).source =
      (principalNormalizedSource hK hT hγ hlarge).source.condition
        (scalarCubeResidueSet Empty (principalIntervalLength K T γ)
          (fun _ => q) (fun _ => r))
        (principalCoefficientResidue_mass_pos hK hT hγ hlarge q hq r hlength) := by
  classical
  let s := principalNormalizedSource hK hT hγ hlarge
  let G := scalarCubeResidueSet Empty (principalIntervalLength K T γ)
    (fun _ => q) (fun _ => r)
  have hs := scalarCubeNormalizationThreshold_spec Empty hlength
  have hG := scalarCubeResidue_mass_pos Empty (principalIntervalLength K T γ) q hs.1
    (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1
  have hGb : 0 < s.baseLaw.mass G := by
    rw [principalSource_baseLaw]
    exact hG
  let w := fun z : IntegerScalarCubeBox Empty s.length =>
    s.weight (fun i => (z i : ℝ) / s.length)
  have hp : scalarCubeResidueWeights Empty (principalIntervalLength K T γ) q hs.1
      (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1 =
      s.baseLaw.condition G hGb := by
    simp only [s, principalSource_baseLaw]
    rfl
  apply weights_ext (X := IntegerScalarCubeBox Empty (principalIntervalLength K T γ))
  intro z
  have hsour :
      (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).source.weight z =
        (scalarCubeResidueWeights Empty (principalIntervalLength K T γ) q hs.1
          (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1).weight z *
        (w z / (scalarCubeResidueWeights Empty (principalIntervalLength K T γ) q hs.1
          (fun _ => q) (fun _ => r) (fun _ => hq) (fun _ => le_rfl) hs.2.1).mean w) := rfl
  rw [hsour, hp]
  exact reweight_condition_weight s.baseLaw w (fun z => (s.weight_range _).1) s.normalized G hGb
    (principalCoefficientResidue_mass_pos hK hT hγ hlarge q hq r hlength) z

theorem principalCoefficientResidueSource_positive_support
    (z : IntegerScalarCubeBox Empty
      (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).length)
    (hz : (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).source.weight z ≠ 0) :
    ((principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).length : ℝ) / 4 ≤
      (z none : ℝ) := by
  apply principalNormalizedSource_positive_support hK hT hγ hlarge z
  rw [principalCoefficientResidueSource_law] at hz
  intro he
  apply hz
  simp [FiniteProbabilityWeights.condition, he]

open scoped Classical

theorem scalarCubeResidueSet_empty_eq_filter (L q : ℕ) (r : ZMod q) :
    scalarCubeResidueSet Empty L (fun _ => q) (fun _ => r) =
      Finset.univ.filter (fun z : IntegerScalarCubeBox Empty L => ((z none : ℤ) : ZMod q) = r) := by
  ext z
  simp only [mem_scalarCubeResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h none
  · intro h i
    cases i with
    | none => exact h
    | some e => exact e.elim

include hq hlength in
theorem principalCoefficientResidue_mass_pos_filter :
    0 < (principalNormalizedSource hK hT hγ hlarge).source.mass
      (Finset.filter (α := IntegerScalarCubeBox Empty (principalIntervalLength K T γ))
        (fun z =>
        ((z none : ℤ) : ZMod q) = r) Finset.univ) := by
  have hf : Finset.filter (α := IntegerScalarCubeBox Empty (principalIntervalLength K T γ))
        (fun z =>
      ((z none : ℤ) : ZMod q) = r) Finset.univ =
      scalarCubeResidueSet Empty (principalIntervalLength K T γ) (fun _ => q) (fun _ => r) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_scalarCubeResidueSet]
    constructor
    · intro h a
      cases a with
      | none => exact h
      | some a => exact a.elim
    · exact fun h => h none
  rw [hf]
  exact principalCoefficientResidue_mass_pos hK hT hγ hlarge q hq r hlength

theorem principalCoefficientResidueSource_law_filter :
    (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength).source =
      (principalNormalizedSource hK hT hγ hlarge).source.condition
        (Finset.filter (α := IntegerScalarCubeBox Empty (principalIntervalLength K T γ))
        (fun z =>
          ((z none : ℤ) : ZMod q) = r) Finset.univ)
        (principalCoefficientResidue_mass_pos_filter hK hT hγ hlarge q hq r hlength) := by
  have hf : Finset.filter (α := IntegerScalarCubeBox Empty (principalIntervalLength K T γ))
        (fun z =>
      ((z none : ℤ) : ZMod q) = r) Finset.univ =
      scalarCubeResidueSet Empty (principalIntervalLength K T γ) (fun _ => q) (fun _ => r) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_scalarCubeResidueSet]
    constructor
    · intro h a
      cases a with
      | none => exact h
      | some a => exact a.elim
    · exact fun h => h none
  simpa only [hf] using principalCoefficientResidueSource_law hK hT hγ hlarge q hq r hlength

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hlong : scalarCubeNormalizationThreshold Empty q 32
  (256 * probabilityProfileLipschitz) ≤
    (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length)

noncomputable def allocatedPrincipalCoefficientResidueSource : NormalizedScalarCubeSource Empty :=
  principalCoefficientResidueSource
    (K := (basisAxisScale (basis j) i : ℝ)) (T := (S.value : ℝ) ^ (j.val + 1))
    (γ := principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _)
    (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive)) q hq r hlong

include hq hlong in
theorem allocatedPrincipalCoefficientResidue_mass_pos :
    0 < (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.mass
      (Finset.univ.filter (fun z => ((z none : ℤ) : ZMod q) = r)) :=
  principalCoefficientResidue_mass_pos_filter _ _ _ _ q hq r hlong

theorem allocatedPrincipalCoefficientResidueSource_law :
    (allocatedPrincipalCoefficientResidueSource q hq r B U basis hR S j i hactive hlong).source =
      (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.condition
        (Finset.univ.filter (fun z => ((z none : ℤ) : ZMod q) = r))
        (allocatedPrincipalCoefficientResidue_mass_pos q hq r B U basis hR S j i hactive hlong) :=
  principalCoefficientResidueSource_law_filter _ _ _ _ q hq r hlong

theorem allocatedPrincipalCoefficientResidueSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget
      (allocatedPrincipalCoefficientResidueSource q hq r B U basis hR S j i hactive hlong) A
      (scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q) :=
  principalCoefficientResidueSource_primitive _ _ _ _ q hq r hlong A

theorem allocatedPrincipalCoefficientResidueSource_positive_support
    (z : IntegerScalarCubeBox Empty
      (allocatedPrincipalCoefficientResidueSource q hq r B U basis hR S j i hactive hlong).length)
    (hz : (allocatedPrincipalCoefficientResidueSource q hq r B U basis hR S j i hactive hlong).source.weight z ≠ 0) :
    ((allocatedPrincipalCoefficientResidueSource q hq r B U basis hR S j i hactive hlong).length : ℝ) / 4 ≤
      (z none : ℝ) :=
  principalCoefficientResidueSource_positive_support _ _ _ _ q hq r hlong z hz

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_empty_residue_law (L q : ℕ) (hL : 0 < L)
    [NeZero q] :
    (integerScalarCubeWeights Empty L hL).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)) =
      (intervalUniformWeights 0 (L : ℤ) (by exact_mod_cast hL)).fiberLaw
        (fun x => (x.val : ZMod q)) := by
  apply FiniteProbabilityWeights.ext_weight
  funext r
  simpa only [FiniteProbabilityWeights.fiberLaw, FiniteProbabilityWeights.fiberMean] using
    integerScalarCubeWeights_zero_mean Empty L hL
      (fun z => if (z : ZMod q) = r then 1 else 0)

theorem integerScalarCubeWeights_empty_residue_mass_pos
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L) (r : ZMod q) :
    0 < (integerScalarCubeWeights Empty L hL).mass
      (Finset.univ.filter (fun x => ((x none : ℤ) : ZMod q) = r)) := by
  rw [← scalarCubeResidueSet_empty_eq_filter]
  exact scalarCubeResidue_mass_pos Empty L q hL (fun _ => q) (fun _ => r)
    (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL)

theorem integerScalarCubeWeights_empty_residue_condition
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L) (r : ZMod q) :
    (integerScalarCubeWeights Empty L hL).condition
      (Finset.univ.filter (fun x => ((x none : ℤ) : ZMod q) = r))
      (integerScalarCubeWeights_empty_residue_mass_pos L q hL hq hqL r) =
    scalarCubeResidueWeights Empty L q hL (fun _ => q) (fun _ => r)
      (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL) := by
  unfold scalarCubeResidueWeights
  congr 1
  exact (scalarCubeResidueSet_empty_eq_filter L q r).symm

theorem integerScalarCubeWeights_empty_residue_l1
    (L q : ℕ) (hL : 0 < L) [NeZero q] :
    (∑ r : ZMod q,
      |((integerScalarCubeWeights Empty L hL).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q))).weight r -
          (FiniteProbabilityWeights.uniform (ZMod q)).weight r|) ≤ (q : ℝ) / L := by
  rw [integerScalarCubeWeights_empty_residue_law]
  simpa only [FiniteProbabilityWeights.uniform, ZMod.card, one_div, Int.cast_sub,
    Int.cast_natCast, Int.cast_zero, sub_zero] using
    intervalUniformWeights_residue_l1_error 0 L (by exact_mod_cast hL) q

theorem integerScalarCubeWeights_empty_pi_residue_disintegration
    {G : Type*} [Fintype G] [DecidableEq G]
    (L q : ℕ) [NeZero q] (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L)
    (test : (G → ZMod q) → (G → IntegerScalarCubeBox Empty L) → ℂ) :
    (FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty L hL)).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) =
    (FiniteProbabilityWeights.pi (fun _ : G =>
      (integerScalarCubeWeights Empty L hL).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)))).complexMean (fun r =>
      (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty L q hL
        (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
          (by simpa using hqL))).complexMean (test r)) := by
  rw [FiniteProbabilityWeights.pi_complexMean_disintegrate
    (fun _ : G => integerScalarCubeWeights Empty L hL)
    (fun _ x => ((x none : ℤ) : ZMod q))
    (fun _ r => integerScalarCubeWeights_empty_residue_mass_pos L q hL hq hqL r) test]
  apply congrArg (FiniteProbabilityWeights.pi (fun _ : G =>
    (integerScalarCubeWeights Empty L hL).fiberLaw
      (fun x => ((x none : ℤ) : ZMod q)))).complexMean
  funext r
  apply congrArg (fun p : FiniteProbabilityWeights (G → IntegerScalarCubeBox Empty L) =>
    p.complexMean (test r))
  apply congrArg FiniteProbabilityWeights.pi
  funext g
  exact integerScalarCubeWeights_empty_residue_condition L q hL hq hqL (r g)

theorem integerScalarCubeWeights_empty_pi_uniform_residue_error
    {G : Type*} [Fintype G] [DecidableEq G]
    (L q : ℕ) [NeZero q] (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L)
    (test : (G → ZMod q) → (G → IntegerScalarCubeBox Empty L) → ℂ)
    (hbound : ∀ r x, ‖test r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty L hL)).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty L q hL
          (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
            (by simpa using hqL))).complexMean (test r)‖ ≤
      (Fintype.card G : ℝ) * ((q : ℝ) / L) := by
  let μ := (integerScalarCubeWeights Empty L hL).fiberLaw
    (fun x => ((x none : ℤ) : ZMod q))
  let ν := FiniteProbabilityWeights.uniform (ZMod q)
  let F (r : G → ZMod q) :=
    (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty L q hL
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
        (by simpa using hqL))).complexMean (test r)
  have hF (r : G → ZMod q) : ‖F r‖ ≤ 1 := by
    apply (FiniteProbabilityWeights.norm_complexMean_le_mean_norm _ _).trans
    exact (FiniteProbabilityWeights.mean_mono _ (hbound r)).trans_eq
      (FiniteProbabilityWeights.mean_const _ 1)
  rw [integerScalarCubeWeights_empty_pi_residue_disintegration L q hL hq hqL test,
    ← FiniteProbabilityWeights.pi_uniform_complexMean]
  exact (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1
    (FiniteProbabilityWeights.pi (fun _ : G => μ))
    (FiniteProbabilityWeights.pi (fun _ : G => ν)) F hF).trans
      ((FiniteProbabilityWeights.pi_weight_l1_le_sum (fun _ : G => μ) (fun _ : G => ν)).trans
        ((Finset.sum_le_sum (fun _ _ => integerScalarCubeWeights_empty_residue_l1 L q hL)).trans_eq
          (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem originalKernel_residue_slow_quadrature (L q : ℕ) [NeZero q]
    (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L) <
      volume.real (scalarCubeDomain Empty))
    (F : (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty L hL)).complexMean
        (fun z => F (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (Fintype.card G * ((q : ℝ) / L)) := by
  let test := fun (r : G → ZMod q) (z : G → IntegerScalarCubeBox Empty L) =>
    F r (fun g i => (z g i : ℝ) / L)
  let law := fun (r : G → ZMod q) => FiniteProbabilityWeights.pi
    (fun g : G => scalarCubeResidueWeights Empty L q hL
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL))
  let e : ℝ := 2 * (2 * scalarCubeGridBoundaryConstant Empty /
    volume.real (scalarCubeDomain Empty) + K) * (Fintype.card G * ((q : ℝ) / L))
  have hcond (r : G → ZMod q) :
      ‖(law r).complexMean (test r) - ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    simpa only [law, test, e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      scalarCubeResidueWeights_pi_complex_riemann (fun _ : G => L) (fun _ => q) (fun _ => hL)
        (fun (_ : G) (_ : Option Empty) => q) (fun g _ => r g) (fun _ _ => hq)
        (fun _ _ => le_rfl) (fun _ => by simpa using hqL)
        (fun _ => hsmall) (F r) (hF r) zero_le_one (hbound r)
  have hmix := integerScalarCubeWeights_empty_pi_uniform_residue_error L q hL hq hqL
    test (fun r z => hbound r _)
  have havg : ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hcond r)).trans_eq (by simp)
  calc
    _ ≤ ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty L hL)).complexMean
        (fun z => test (fun g => ((z g none : ℤ) : ZMod q)) z) -
          𝔼 r : G → ZMod q, (law r).complexMean (test r)‖ +
        ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
          𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Fintype.card G * ((q : ℝ) / L)) + e := add_le_add hmix havg
    _ = _ := by dsimp only [e]; ring

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerScalarCubeWeights_empty_pi_residue_disintegration_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) =
    (FiniteProbabilityWeights.pi (fun g : G =>
      (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)))).complexMean (fun r =>
      (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
        (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
          (by simpa using hqL g))).complexMean (test r)) := by
  rw [FiniteProbabilityWeights.pi_complexMean_disintegrate
    (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))
    (fun _ x => ((x none : ℤ) : ZMod q))
    (fun g r => integerScalarCubeWeights_empty_residue_mass_pos (L g) q (hL g) hq (hqL g) r) test]
  apply congrArg (FiniteProbabilityWeights.pi (fun g : G =>
    (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
      (fun x => ((x none : ℤ) : ZMod q)))).complexMean
  funext r
  apply congrArg (fun p : FiniteProbabilityWeights (∀ g, IntegerScalarCubeBox Empty (L g)) =>
    p.complexMean (test r))
  apply congrArg FiniteProbabilityWeights.pi
  funext g
  exact integerScalarCubeWeights_empty_residue_condition (L g) q (hL g) hq (hqL g) (r g)

theorem integerScalarCubeWeights_empty_pi_uniform_residue_error_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ)
    (hbound : ∀ r x, ‖test r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
          (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
            (by simpa using hqL g))).complexMean (test r)‖ ≤
      ∑ g, (q : ℝ) / L g := by
  let μ := fun g => (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
    (fun x => ((x none : ℤ) : ZMod q))
  let ν := FiniteProbabilityWeights.uniform (ZMod q)
  let F (r : G → ZMod q) :=
    (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
        (by simpa using hqL g))).complexMean (test r)
  have hF (r : G → ZMod q) : ‖F r‖ ≤ 1 := by
    apply (FiniteProbabilityWeights.norm_complexMean_le_mean_norm _ _).trans
    exact (FiniteProbabilityWeights.mean_mono _ (hbound r)).trans_eq
      (FiniteProbabilityWeights.mean_const _ 1)
  rw [integerScalarCubeWeights_empty_pi_residue_disintegration_varying L q hL hq hqL test,
    ← FiniteProbabilityWeights.pi_uniform_complexMean]
  exact (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1
    (FiniteProbabilityWeights.pi (fun g : G => μ g))
    (FiniteProbabilityWeights.pi (fun _ : G => ν)) F hF).trans
      ((FiniteProbabilityWeights.pi_weight_l1_le_sum (fun g : G => μ g) (fun _ : G => ν)).trans
        (Finset.sum_le_sum (fun g _ => integerScalarCubeWeights_empty_residue_l1 (L g) q (hL g))))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem originalKernel_residue_slow_retained_quadrature
    {G Z : Type*} [Fintype G] [DecidableEq G] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (L q : ℕ) [NeZero q] (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L) <
      volume.real (scalarCubeDomain Empty))
    (F : Z → (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    (hMeas : ∀ r, Measurable (fun zx : Z × (G → Option Empty → ℝ) => F zx.1 r zx.2))
    {K : ℝ≥0} (hLip : ∀ z r, LipschitzWith K (F z r))
    (hbound : ∀ z r x, ‖F z r x‖ ≤ 1) :
    ‖(∫ z, (FiniteProbabilityWeights.pi
        (fun _ : G => integerScalarCubeWeights Empty L hL)).complexMean
          (fun y => F z (fun g => ((y g none : ℤ) : ZMod q))
            (fun g i => (y g i : ℝ) / L)) ∂μ) -
      ∫ z, 𝔼 r : G → ZMod q,
        ∫ x, F z r x ∂scalarCubeProductMeasure G Empty ∂μ‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (Fintype.card G * ((q : ℝ) / L)) := by
  let p := FiniteProbabilityWeights.pi
    (fun _ : G => integerScalarCubeWeights Empty L hL)
  let a (z : Z) := p.complexMean
    (fun y => F z (fun g => ((y g none : ℤ) : ZMod q))
      (fun g i => (y g i : ℝ) / L))
  let b (z : Z) := 𝔼 r : G → ZMod q,
    ∫ x, F z r x ∂scalarCubeProductMeasure G Empty
  have haMeas : Measurable a := by
    unfold a FiniteProbabilityWeights.complexMean
    apply Finset.measurable_sum
    intro y _
    exact measurable_const.mul ((hMeas _).comp (measurable_id.prodMk measurable_const))
  have haBound (z : Z) : ‖a z‖ ≤ 1 := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    exact (p.mean_mono (fun y => hbound z _ _)).trans_eq (p.mean_const 1)
  have haInt : Integrable a μ :=
    (integrable_const (1 : ℝ)).mono' haMeas.aestronglyMeasurable (ae_of_all μ haBound)
  have hiMeas (r : G → ZMod q) :
      StronglyMeasurable (fun z => ∫ x, F z r x ∂scalarCubeProductMeasure G Empty) :=
    (hMeas r).stronglyMeasurable.integral_prod_right'
  have hiBound (z : Z) (r : G → ZMod q) :
      ‖∫ x, F z r x ∂scalarCubeProductMeasure G Empty‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const
        (ae_of_all (scalarCubeProductMeasure G Empty) (hbound z r))
  have hbMeas : Measurable b := by
    unfold b
    simp only [Fintype.expect_eq_sum_div_card]
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun r _ => (hiMeas r).measurable)
  have hbBound (z : Z) : ‖b z‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hiBound z r)).trans_eq (by simp)
  have hbInt : Integrable b μ :=
    (integrable_const (1 : ℝ)).mono' hbMeas.aestronglyMeasurable (ae_of_all μ hbBound)
  change ‖(∫ z, a z ∂μ) - ∫ z, b z ∂μ‖ ≤ _
  rw [← integral_sub haInt hbInt]
  have he := ae_of_all μ (fun z =>
    originalKernel_residue_slow_quadrature L q hL hq hqL hsmall
      (F z) (hLip z) (hbound z))
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const he

end Erdos3

end

end OAI
