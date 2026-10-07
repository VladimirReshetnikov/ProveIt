/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
import OAI.Combinatorics.Progressions.Linear.KernelCoreComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnMap (V : J → G) : (J → ZMod q) →+ G where
  toFun t := ∑ j, t j • V j
  map_zero' := by simp
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]

omit [NeZero q] in
theorem residueColumnMap_single (V : J → G) (j : J) :
    residueColumnMap (q := q) V (Pi.single j (1 : ZMod q)) = V j := by
  simp [residueColumnMap, Pi.single_apply, ite_smul]

theorem additiveCharacter_zmod_smul (χ : AddChar G ℂ) (t : ZMod q) (x : G) :
    χ (t • x) = χ x ^ t.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul]
  exact χ.map_nsmul_eq_pow t.val x

theorem residueColumn_character_zero_iff (V : J → G) (χ : AddChar G ℂ) :
    χ.compAddMonoidHom (residueColumnMap (q := q) V) = 0 ↔ ∀ j, χ (V j) = 1 := by
  constructor
  · intro h j
    have hh := DFunLike.congr_fun h (Pi.single j (1 : ZMod q))
    simpa only [AddChar.compAddMonoidHom_apply, residueColumnMap_single, AddChar.zero_apply] using hh
  · intro h
    ext t
    change χ (∑ j, t j • V j) = 1
    exact (additiveCharacterKernel χ).sum_mem (fun j _ => by
      change χ (t j • V j) = 1
      rw [additiveCharacter_zmod_smul, h, one_pow])

theorem residueColumn_character_mean (V : J → G) (χ : AddChar G ℂ) :
    (𝔼 t : J → ZMod q, χ (residueColumnMap (q := q) V t)) =
      if ∀ j, χ (V j) = 1 then 1 else 0 := by
  have h := AddChar.expect_eq_ite (χ.compAddMonoidHom (residueColumnMap (q := q) V))
  simpa only [AddChar.compAddMonoidHom_apply, residueColumn_character_zero_iff] using h

noncomputable def residueColumnAverage (V : J → G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

variable [Fintype G]

theorem finiteFourierCoeff_residueColumnAverage (V : J → G) (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (residueColumnAverage (q := q) V f) χ =
      (if ∀ j, χ (V j) = 1 then 1 else 0) * finiteFourierCoeff f χ := by
  have htranslate (a : G) : finiteFourierCoeff (fun x => f (x + a)) χ =
      χ a * finiteFourierCoeff f χ := by
    have h := finiteFourierCoeff_translate f (-a) χ
    rw [AddChar.map_neg_eq_conj] at h
    simpa only [sub_neg_eq_add, Complex.star_def, starRingEnd_self_apply] using h
  unfold finiteFourierCoeff residueColumnAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 t : J → ZMod q, finiteFourierCoeff (fun x => f (x + residueColumnMap (q := q) V t)) χ) = _
  simp_rw [htranslate]
  rw [← Finset.expect_mul, residueColumn_character_mean]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

theorem residueColumn_survival_probability (χ : AddChar G ℂ) :
    (𝔼 V : J → G, if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
      (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J := by
  have hpoint (V : J → G) :
      (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
        ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, χ (V j) = 1
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  calc
    _ = 𝔼 V : J → G, ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 :=
      Finset.expect_congr rfl (fun V _ => hpoint V)
    _ = (∑ x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J /
        (Fintype.card G : ℝ) ^ Fintype.card J := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow]
      congr 1
      simpa using (Fintype.prod_sum
        (fun _j : J => fun x : G => if χ x = 1 then (1 : ℝ) else 0)).symm
    _ = _ := by rw [Fintype.expect_eq_sum_div_card, div_pow]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

theorem residueColumnAverage_energy (V : J → G) (f : G → ℂ) :
    (𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) * ‖finiteFourierCoeff f χ‖ ^ 2 := by
  rw [← finiteFourier_parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [finiteFourierCoeff_residueColumnAverage]
  split_ifs <;> simp

theorem residueColumnAverage_mean_energy (f : G → ℂ) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J *
          ‖finiteFourierCoeff f χ‖ ^ 2 := by
  simp_rw [residueColumnAverage_energy]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.expect_mul, residueColumn_survival_probability]

theorem primeAffine_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℂ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, ‖f x‖ ^ 2) := by
  rw [residueColumnAverage_mean_energy]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, (p : ℝ)⁻¹ ^ Fintype.card J *
        ‖finiteFourierCoeff f χ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro χ _
      by_cases hχ : χ = 0
      · subst χ
        have hz : finiteFourierCoeff f 0 = 0 := by
          simpa [finiteFourierCoeff] using hf
        simp [hz]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀
          (Finset.expect_nonneg (fun x _ => by split_ifs <;> norm_num))
          (primePowerCharacter_kernel_probability hp hG hχ) _
    _ = _ := by rw [← Finset.mul_sum, finiteFourier_parseval]

theorem primeAffine_contraction {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℂ) (hf : (𝔼 x, f x) = 0) :
    Real.sqrt (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) ≤
      (p : ℝ) ^ (-(Fintype.card J : ℝ) / 2) * Real.sqrt (𝔼 x : G, ‖f x‖ ^ 2) := by
  have hs : Real.sqrt ((p : ℝ)⁻¹ ^ Fintype.card J) =
      (p : ℝ) ^ (-(Fintype.card J : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = ((p : ℝ) ^ (-(Fintype.card J : ℝ))) ^ (1 / (2 : ℝ)) := by
        rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast, inv_pow]
      _ = (p : ℝ) ^ (-(Fintype.card J : ℝ) * (1 / 2)) :=
        (Real.rpow_mul (Nat.cast_nonneg p) _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ Real.sqrt ((p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, ‖f x‖ ^ 2)) :=
      Real.sqrt_le_sqrt (primeAffine_contraction_sq (q := q) hp hG f hf)
    _ = _ := by rw [Real.sqrt_mul (by positivity), hs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {p a : ℕ} [NeZero (p ^ a)]

theorem primePowerResidue_contraction_sq (hp : p.Prime)
    (f : (I → ZMod (p ^ a)) → ℂ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → I → ZMod (p ^ a), 𝔼 X : I → ZMod (p ^ a),
      ‖𝔼 t : J → ZMod (p ^ a), f (X + ∑ j, t j • V j)‖ ^ 2) ≤
        (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 X, ‖f X‖ ^ 2) := by
  have hG : Fintype.card (I → ZMod (p ^ a)) = p ^ (a * Fintype.card I) := by
    simp [pow_mul]
  simpa only [residueColumnAverage, residueColumnMap, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] using primeAffine_contraction_sq (J := J) (q := p ^ a) hp hG f hf

theorem primePowerResidue_contraction (hp : p.Prime)
    (f : (I → ZMod (p ^ a)) → ℂ) (hf : (𝔼 x, f x) = 0) :
    Real.sqrt (𝔼 V : J → I → ZMod (p ^ a), 𝔼 X : I → ZMod (p ^ a),
      ‖𝔼 t : J → ZMod (p ^ a), f (X + ∑ j, t j • V j)‖ ^ 2) ≤
        (p : ℝ) ^ (-(Fintype.card J : ℝ) / 2) * Real.sqrt (𝔼 X, ‖f X‖ ^ 2) := by
  have hG : Fintype.card (I → ZMod (p ^ a)) = p ^ (a * Fintype.card I) := by
    simp [pow_mul]
  simpa only [residueColumnAverage, residueColumnMap, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] using primeAffine_contraction (J := J) (q := p ^ a) hp hG f hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnRealAverage (V : J → G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

theorem residueColumnAverage_ofReal (V : J → G) (f : G → ℝ) (x : G) :
    residueColumnAverage (q := q) V (fun y => (f y : ℂ)) x =
      (residueColumnRealAverage (q := q) V f x : ℂ) := by
  simp only [residueColumnAverage, residueColumnRealAverage, Fintype.expect_eq_sum_div_card,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

variable [Fintype G]

theorem residueColumnRealAverage_mean (V : J → G) (f : G → ℝ) :
    (𝔼 x : G, residueColumnRealAverage (q := q) V f x) = 𝔼 x : G, f x := by
  unfold residueColumnRealAverage
  rw [Finset.expect_comm]
  have hshift (t : J → ZMod q) : (𝔼 x : G, f (x + residueColumnMap (q := q) V t)) = 𝔼 x : G, f x :=
    Fintype.expect_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) _ _ (fun _ => rfl)
  simp only [hshift, Fintype.expect_const]

theorem primeAffine_real_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, residueColumnRealAverage (q := q) V f x ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, f x ^ 2) := by
  have hfc : (𝔼 x : G, (f x : ℂ)) = 0 := by
    have hc := congrArg (fun y : ℝ => (y : ℂ)) hf
    simpa only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_natCast, Complex.ofReal_zero] using hc
  have h := primeAffine_contraction_sq (q := q) (J := J) hp hG (fun x => (f x : ℂ)) hfc
  simpa only [residueColumnAverage_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

noncomputable def residueAffineSource : FiniteProbabilityWeights ((J → G) × G) :=
  (FiniteProbabilityWeights.uniform (J → G)).prod (FiniteProbabilityWeights.uniform G)

noncomputable def residueAffineKernel (z : (J → G) × G) : FiniteProbabilityWeights G :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun t => z.2 + residueColumnMap (q := q) z.1 t)

theorem residueAffineKernel_mean (z : (J → G) × G) (f : G → ℝ) :
    (residueAffineKernel (q := q) z).mean f = residueColumnRealAverage (q := q) z.1 f z.2 := by
  rw [residueAffineKernel, FiniteProbabilityWeights.fiberLaw_mean, FiniteProbabilityWeights.uniform_mean]
  rfl

theorem residueAffineKernel_preserves_mean (f : G → ℝ) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f) =
      (FiniteProbabilityWeights.uniform G).mean f := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean, residueColumnRealAverage_mean, Fintype.expect_const]

noncomputable def residueAffineCoupling :
    FiniteProbabilityCoupling (residueAffineSource (J := J) (G := G)) (FiniteProbabilityWeights.uniform G) :=
  FiniteProbabilityCoupling.ofKernel _ _ (residueAffineKernel (q := q))
    (residueAffineKernel_preserves_mean (q := q))

theorem residueAffineKernel_centered_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ)
    (hf : (FiniteProbabilityWeights.uniform G).mean f = 0) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform G).mean (fun x => f x ^ 2) := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean]
  exact primeAffine_real_contraction_sq hp hG f (by simpa only [FiniteProbabilityWeights.uniform_mean] using hf)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
  (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)

include hp hcard

theorem affineCoupling_level_abs_le {κ : ℝ} (hκ : 0 ≤ κ)
    (hcap : ∀ i, (p i : ℝ)⁻¹ ^ Fintype.card J ≤ κ ^ 2)
    (k : ℕ) (w : (∀ i, (J → G i) × G i) → ℝ) (f : (∀ i, G i) → ℝ) :
    let μ := fun i => residueAffineSource (J := J) (G := G i)
    let ν := fun i => FiniteProbabilityWeights.uniform (G i)
    |productCouplingPairing (fun i => residueAffineCoupling (q := q i) (J := J) (G := G i))
      (productANOVATruncation μ (Finset.univ.powersetCard k) w)
      (productANOVATruncation ν (Finset.univ.powersetCard k) f)| ≤
        κ ^ k * Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) *
          Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) := by
  exact productCouplingPairing_level_abs_le _ _ (fun i => residueAffineKernel (q := q i))
    (fun i => (p i : ℝ)⁻¹ ^ Fintype.card J) (fun _ => by positivity)
    (fun i => residueAffineKernel_centered_sq (hp i) (hcard i))
    (fun i => residueAffineKernel_preserves_mean (q := q i)) hκ hcap k w f

theorem affineCoupling_tail_abs_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i, (p i : ℝ)⁻¹ ^ Fintype.card J ≤ κ ^ 2)
    (r : ℕ) (D : Finset (Finset ι)) (hmin : ∀ S ∈ D, r ≤ S.card)
    (w : (∀ i, (J → G i) × G i) → ℝ) (f : (∀ i, G i) → ℝ) :
    let μ := fun i => residueAffineSource (J := J) (G := G i)
    let ν := fun i => FiniteProbabilityWeights.uniform (G i)
    |productCouplingPairing (fun i => residueAffineCoupling (q := q i) (J := J) (G := G i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
        κ ^ r * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  exact productCouplingPairing_tail_abs_le _ _ (fun i => residueAffineKernel (q := q i))
    (fun i => (p i : ℝ)⁻¹ ^ Fintype.card J) (fun _ => by positivity)
    (fun i => residueAffineKernel_centered_sq (hp i) (hcard i))
    (fun i => residueAffineKernel_preserves_mean (q := q i)) hκ0 hκ1 hcap r D hmin w f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productAffine_centered_contraction_sq {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
    (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)
    (f : (∀ i, G i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => residueAffineSource (J := J) (G := G i))).mean
      (fun x => productMatrixApply (fun i => centeredKernelMatrix (FiniteProbabilityWeights.uniform (G i))
        (residueAffineKernel (q := q i) (J := J))) f x ^ 2) ≤
      (∏ i, (p i : ℝ)⁻¹ ^ Fintype.card J) *
        (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (G i))).mean
          (fun y => f y ^ 2) := by
  apply productMatrixApply_sq_le _ _ _ (fun i => (p i : ℝ)⁻¹ ^ Fintype.card J) (fun _ => by positivity)
  intro i g
  apply centeredKernelMatrix_sq_le _ _ _ (by positivity)
  intro h hh
  exact residueAffineKernel_centered_sq (hp i) (hcard i) h hh

theorem productAffine_centered_pairing_sq {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
    (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)
    (w : (∀ i, (J → G i) × G i) → ℝ) (f : (∀ i, G i) → ℝ) :
    ((FiniteProbabilityWeights.pi (fun i => residueAffineSource (J := J) (G := G i))).mean
      (fun x => w x * productMatrixApply (fun i => centeredKernelMatrix (FiniteProbabilityWeights.uniform (G i))
        (residueAffineKernel (q := q i) (J := J))) f x)) ^ 2 ≤
      (∏ i, (p i : ℝ)⁻¹ ^ Fintype.card J) *
        (FiniteProbabilityWeights.pi (fun i => residueAffineSource (J := J) (G := G i))).mean
          (fun x => w x ^ 2) *
        (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (G i))).mean
          (fun y => f y ^ 2) := by
  apply productMatrixApply_pairing_sq_le _ _ _ (fun i => (p i : ℝ)⁻¹ ^ Fintype.card J) (fun _ => by positivity)
  intro i g
  apply centeredKernelMatrix_sq_le _ _ _ (by positivity)
  intro h hh
  exact residueAffineKernel_centered_sq (hp i) (hcard i) h hh

theorem productAffine_uniform_centered_sq {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
    (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)
    {P : ℝ} (hP : 0 < P) (hmin : ∀ i, P ≤ (p i : ℝ)) (f : (∀ i, G i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => residueAffineSource (J := J) (G := G i))).mean
      (fun x => productMatrixApply (fun i => centeredKernelMatrix (FiniteProbabilityWeights.uniform (G i))
        (residueAffineKernel (q := q i) (J := J))) f x ^ 2) ≤
      (P⁻¹ ^ Fintype.card J) ^ Fintype.card ι *
        (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (G i))).mean
          (fun y => f y ^ 2) := by
  apply (productAffine_centered_contraction_sq p q a hp hcard f).trans
  apply mul_le_mul_of_nonneg_right _ (FiniteProbabilityWeights.mean_nonneg _ (fun y => sq_nonneg (f y)))
  have hi (i : ι) : (p i : ℝ)⁻¹ ≤ P⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hP (hmin i)
  have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset ι))
    (fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (p i))) (Fintype.card J))
    (fun i _ => pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg (p i))) (hi i) (Fintype.card J))
  simpa only [Finset.prod_const, Finset.card_univ] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_mono {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) {I J : Finset ι}
    {x y : ∀ i, σ → ZMod (q i)} (hIJ : I ⊆ J) (hxy : ∀ i ∈ I, y i = x i) :
    primeCoordinateCell lo N q J y ⊆ primeCoordinateCell lo N q I x := by
  intro z hz
  obtain ⟨hz, heq⟩ := (mem_primeCoordinateCell lo N q J y z).mp hz
  exact (mem_primeCoordinateCell lo N q I x z).mpr ⟨hz, fun i hi => (heq i (hIJ hi)).trans (hxy i hi)⟩

noncomputable def primeCoordinateMean {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ :=
  𝔼 z : primeCoordinateCell lo N q I x, f z.val

theorem primeCoordinateMean_eq_physical {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell lo N q I x) :
    primeCoordinateMean f lo N q I x = physicalResidueMean f lo N (∏ i ∈ I, q i) u := by
  unfold primeCoordinateMean
  rw [primeCoordinateCell_anchor lo N q I x u hu]
  exact primeCoordinateCell_mean lo N q hcop I u f

noncomputable def PrimeCoordinateStable {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → (primeCoordinateCell lo N q (I ∪ J) y).Nonempty →
    ‖primeCoordinateMean f lo N q I x - primeCoordinateMean f lo N q (I ∪ J) y‖ ≤ δ

theorem primeCoordinateStable_of_empty {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hempty : ¬ (primeCoordinateCell lo N q I x).Nonempty) : PrimeCoordinateStable f lo N q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  obtain ⟨z, hz⟩ := hnonempty
  exact False.elim (hempty ⟨z, primeCoordinateCell_mono lo N q Finset.subset_union_left hxy hz⟩)

universe u v

theorem exists_prime_cell_physical_comparison
    {ι : Type*} [DecidableEq ι] {σ : Type u} [Fintype σ] [DecidableEq σ]
    {s bound : ℕ} {gap : ℝ} (base : PhysicalEpochSource.{u, v} σ s bound)
    (T : base.model.Niltest (fun _ : σ => 1)) (horbit : T.orbit = base.fixedMap.orbit)
    (hpositive : T.UnitIntervalValued) (hcomplexity : T.ComplexityLE base.incomingBudget)
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I J : Finset ι) (hIJ : Disjoint I J) (x y : ∀ i, σ → ZMod (q i))
    (hxy : ∀ i ∈ I, y i = x i) (u v : σ → ℤ)
    (hu : u ∈ primeCoordinateCell base.lower base.sides q I x)
    (hv : v ∈ primeCoordinateCell base.lower base.sides q (I ∪ J) y)
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (hinverse : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hrecord : 2 ≤ base.recordBudget)
    (hdiscrepancy : gap ≤ ‖primeCoordinateMean T.eval base.lower base.sides q I x -
      primeCoordinateMean T.eval base.lower base.sides q (I ∪ J) y‖) :
    ∃ c : PhysicalEpochComparison base (∏ i ∈ I, q i) 1 (∏ i ∈ J, q i) gap,
      c.Controlled ∧ c.anchor = u ∧ c.refined = v := by
  have hvmem := primeCoordinateCell_mono base.lower base.sides q Finset.subset_union_left hxy hv
  have hanchorCell := primeCoordinateCell_anchor base.lower base.sides q I x u hu
  have hcompat : ∀ i, v i ≡ u i [ZMOD ((∏ j ∈ I, q j : ℕ) : ℤ)] := by
    rw [hanchorCell] at hvmem
    exact ((mem_primeCoordinateCell_anchor base.lower base.sides q hcop I u v).mp hvmem).2
  have huinside := (mem_translatedIntegerBox base.lower base.sides u).mp
    ((mem_primeCoordinateCell base.lower base.sides q I x u).mp hu).1
  have hvinside := (mem_translatedIntegerBox base.lower base.sides v).mp
    ((mem_primeCoordinateCell base.lower base.sides q (I ∪ J) y v).mp hv).1
  have hm : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => hq i)
  have hJ : 0 < ∏ i ∈ J, q i := Finset.prod_pos (fun i _ => hq i)
  have hphysical : gap ≤ ‖physicalResidueMean T.eval base.lower base.sides (∏ i ∈ I, q i) u -
      physicalResidueMean T.eval base.lower base.sides ((∏ i ∈ I, q i) * ∏ i ∈ J, q i) v‖ := by
    rw [primeCoordinateMean_eq_physical T.eval base.lower base.sides q hcop I x u hu,
      primeCoordinateMean_eq_physical T.eval base.lower base.sides q hcop (I ∪ J) y v hv,
      Finset.prod_union hIJ] at hdiscrepancy
    exact hdiscrepancy
  obtain ⟨c, hc, hcu, hcv, _, _⟩ := exists_initial_physical_comparison base T horbit hpositive hcomplexity
    hm hJ u v huinside hvinside hcompat hgap hgap1 hinverse hrecord hphysical
  exact ⟨c, hc, hcu, hcv⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def primeCoordinateObservation {ι σ : Type*} (q : ι → ℕ) (z : σ → ℤ) : ∀ i, σ → ZMod (q i) :=
  fun i j => (z j : ZMod (q i))

noncomputable def primeCoordinateReference {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] : ∀ i, FiniteProbabilityWeights (σ → ZMod (q i)) :=
  fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i))

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  dsimp only [primeCoordinateReference, FiniteProbabilityWeights.uniform]
  positivity

noncomputable def primeCoordinateLaw {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)] :
    FiniteProbabilityWeights (∀ i, σ → ZMod (q i)) :=
  (FiniteProbabilityWeights.uniformFinset (translatedIntegerBox lo N) hbox).fiberLaw
    (fun z => primeCoordinateObservation q z.val)

noncomputable def primeCoordinateDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (f : (σ → ℤ) → ℝ) : (∀ i, σ → ZMod (q i)) → ℝ :=
  observedProductDensity (primeCoordinateReference (σ := σ) q)
    (FiniteProbabilityWeights.uniformFinset (translatedIntegerBox lo N) hbox)
    (fun z => primeCoordinateObservation q z.val) (fun z => f z.val)

theorem primeCoordinateDensity_nonneg {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (f : (σ → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z)
    (x : ∀ i, σ → ZMod (q i)) : 0 ≤ primeCoordinateDensity lo N hbox q f x := by
  unfold primeCoordinateDensity observedProductDensity
  apply finiteWeightDensity_nonneg
  intro y
  apply FiniteProbabilityWeights.fiberMean_nonneg
  intro z
  exact hf z.val z.property

theorem primeCoordinateDensity_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateDensity lo N hbox q (fun _ => 1) x =
      (primeCoordinateLaw lo N hbox q).weight x /
        (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight x := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev ResiduePrimeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :=
  {z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a //
    ∀ i ∈ I, (fun j => ((z j).val : ZMod (q i))) = x i}

noncomputable def residuePrimeCoordinateMean {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ := by
  classical
  exact 𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)

noncomputable def ResiduePrimeCoordinateStable {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    ‖residuePrimeCoordinateMean f lo N M a q I x -
      residuePrimeCoordinateMean f lo N M a q (I ∪ J) y‖ ≤ δ

noncomputable def primeCoordinateCell_subtypeEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell lo N q I x ≃
      {z : translatedIntegerBox lo N // ∀ i ∈ I, (fun j => (z.val j : ZMod (q i))) = x i} where
  toFun z := ⟨⟨z.val, ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).1⟩,
    ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).2⟩
  invFun z := ⟨z.val.val, (mem_primeCoordinateCell lo N q I x z.val.val).mpr ⟨z.val.property, z.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def affineSampleAlphabetEquiv {J I R : Type*} :
    (Option J × I → R) ≃ (J → I → R) × (I → R) where
  toFun z := (fun j i => z (some j, i), fun i => z (none, i))
  invFun z := baseArrayJoin (fun k => z.1 k.1 k.2) z.2
  left_inv z := baseArrayJoin_eta z
  right_inv _ := rfl

theorem affineSampleAlphabet_weight {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (z : Option J × I → R) :
    (residueAffineSource (J := J) (G := I → R)).weight (affineSampleAlphabetEquiv z) =
      (FiniteProbabilityWeights.uniform (Option J × I → R)).weight z := by
  change (Fintype.card (J → I → R) : ℝ)⁻¹ * (Fintype.card (I → R) : ℝ)⁻¹ =
    (Fintype.card (Option J × I → R) : ℝ)⁻¹
  rw [Fintype.card_congr (affineSampleAlphabetEquiv (J := J) (I := I) (R := R))]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

theorem affineSampleAlphabet_mean {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (f : ((J → I → R) × (I → R)) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → R)).mean
      (fun z => f (affineSampleAlphabetEquiv z)) =
      (residueAffineSource (J := J) (G := I → R)).mean f :=
  FiniteProbabilityWeights.mean_equiv _ _ affineSampleAlphabetEquiv affineSampleAlphabet_weight f

def affinePrimeCoordinateObservation {ι J I : Type*} (q : ι → ℕ)
    (z : Option J × I → ℤ) : ∀ i, (J → I → ZMod (q i)) × (I → ZMod (q i)) :=
  fun i => affineSampleAlphabetEquiv (primeCoordinateObservation q z i)

theorem affinePrimeCoordinateObservation_apply {ι J I : Type*} (q : ι → ℕ)
    (z : Option J × I → ℤ) (i : ι) :
    affinePrimeCoordinateObservation q z i =
      (fun j k => (z (some j, k) : ZMod (q i)), fun k => (z (none, k) : ZMod (q i))) := rfl

end Erdos3

end

end OAI
