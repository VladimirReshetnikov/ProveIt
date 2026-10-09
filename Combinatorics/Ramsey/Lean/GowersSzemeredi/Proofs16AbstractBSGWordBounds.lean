import GowersSzemeredi.Proofs16AbstractBSGWordSystem
import GowersSzemeredi.Proofs16ThresholdWordDensityBounds

/-! Exact polynomial dependence of the abstract BSG word densities on
input density and doubling. Coefficients depend only on word length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem absBsgWordLambda_monomial (c K : Real) (hK : K ≠ 0) :
    absBsgWordLambda c K = absBsgWordLambda 1 1 * c^28 / K^18 := by
  unfold absBsgWordLambda absBsgKappa absBsgEps absBsgEta absBsgDelta2 absBsgDelta
  field_simp

theorem absBsgWordEta_monomial (c K : Real) (hK : K ≠ 0) :
    absBsgWordEta c K = absBsgWordEta 1 1 * c^10 / K^7 := by
  unfold absBsgWordEta absBsgEta absBsgDelta2 absBsgDelta
  field_simp

def absBsgWordCoefficient (k : Nat) : Real :=
  thresholdColumnWordDensity (absBsgWordLambda 1 1) (absBsgWordEta 1 1) k

def absBsgWordDensityExponent : Nat → Nat
  | 0 => 28
  | k+1 => 104 + 3*absBsgWordDensityExponent k

def absBsgWordDoublingExponent : Nat → Nat
  | 0 => 18
  | k+1 => 68 + 3*absBsgWordDoublingExponent k

theorem absBsgWordCoefficient_pos (k : Nat) : 0 < absBsgWordCoefficient k := by
  have hp := absBsgWord_parameters_pos (by norm_num : (0 : Real) < 1)
    (by norm_num : (0 : Real) < 1) k
  exact thresholdColumnWordDensity_pos hp.1 hp.2.1 k

/-- Each fixed word length loses a fixed power of density and doubling. -/
theorem absBsgWordDensity_monomial (c K : Real) (hK : K ≠ 0) (k : Nat) :
    thresholdColumnWordDensity (absBsgWordLambda c K) (absBsgWordEta c K) k =
      absBsgWordCoefficient k * c^(absBsgWordDensityExponent k) /
        K^(absBsgWordDoublingExponent k) := by
  induction k with
  | zero => exact absBsgWordLambda_monomial c K hK
  | succ k ih =>
    change (absBsgWordEta c K)^2*(absBsgWordLambda c K)^3*
        (thresholdColumnWordDensity (absBsgWordLambda c K) (absBsgWordEta c K) k)^3/128 =
      ((absBsgWordEta 1 1)^2*(absBsgWordLambda 1 1)^3*(absBsgWordCoefficient k)^3/128)*
        c^(104+3*absBsgWordDensityExponent k)/K^(68+3*absBsgWordDoublingExponent k)
    rw [ih, absBsgWordLambda_monomial c K hK, absBsgWordEta_monomial c K hK]
    have hc : c^104*(c^(absBsgWordDensityExponent k))^3 =
        c^(104+3*absBsgWordDensityExponent k) := by
      rw [←pow_mul, ←pow_add]; congr 1; omega
    have hkd : K^68*(K^(absBsgWordDoublingExponent k))^3 =
        K^(68+3*absBsgWordDoublingExponent k) := by
      rw [←pow_mul, ←pow_add]; congr 1; omega
    rw [←hc, ←hkd]
    field_simp

theorem absBsgWordDensityExponent_add52 (k : Nat) :
    absBsgWordDensityExponent k + 52 = 80*3^k := by
  induction k with
  | zero => norm_num [absBsgWordDensityExponent]
  | succ k ih => rw [absBsgWordDensityExponent, pow_succ]; omega

theorem absBsgWordDoublingExponent_add34 (k : Nat) :
    absBsgWordDoublingExponent k + 34 = 52*3^k := by
  induction k with
  | zero => norm_num [absBsgWordDoublingExponent]
  | succ k ih => rw [absBsgWordDoublingExponent, pow_succ]; omega

/-- In the unit range the finite minimum is exactly the last word density. -/
theorem relationWordCutoff_eq {lambda eta : Real}
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (he : 0 < eta) (he1 : eta ≤ 1) (k : Nat) :
    relationWordCutoff lambda eta k = thresholdColumnWordDensity lambda eta k / 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [relationWordCutoff, ih, min_eq_right]
    exact div_le_div_of_nonneg_right
      (thresholdColumnWordDensity_antitone hl hl1 he he1 (Nat.le_succ k)) (by norm_num)

/-- The core's parameters lie in the unit range at density at most one
and doubling at least one. -/
theorem absBsgWord_parameters_le_one {c K : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (hK : 1 ≤ K) : absBsgWordLambda c K ≤ 1 ∧ absBsgWordEta c K ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hd0 : 0 ≤ absBsgDelta c K := by unfold absBsgDelta; positivity
  have hd1 : absBsgDelta c K ≤ 1 := by
    unfold absBsgDelta
    apply (div_le_one (by positivity)).mpr
    linarith
  have hd20 : 0 ≤ absBsgDelta2 c K := by unfold absBsgDelta2; positivity
  have hd21 : absBsgDelta2 c K ≤ 1 := by
    have hm : c * absBsgDelta c K ≤ 1 :=
      (mul_le_mul hc1 hd1 hd0 (by norm_num)).trans_eq (by ring)
    unfold absBsgDelta2
    linarith
  have he0 : 0 ≤ absBsgEta c K := by unfold absBsgEta; positivity
  have he1 : absBsgEta c K ≤ 1 := by
    have hp := pow_le_one₀ hd20 hd21 (n := 5)
    unfold absBsgEta
    linarith
  have hep0 : 0 ≤ absBsgEps c K := by unfold absBsgEps; positivity
  have hep1 : absBsgEps c K ≤ 1 := by unfold absBsgEps; linarith
  have hprod0 : 0 ≤ absBsgEps c K * absBsgEps c K * absBsgEta c K := by positivity
  have hprod1 : absBsgEps c K * absBsgEps c K * absBsgEta c K ≤ 1 := by
    calc absBsgEps c K * absBsgEps c K * absBsgEta c K ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hK2 : (1 : Real) ≤ K^2 := one_le_pow₀ hK
  have hK4 : (1 : Real) ≤ K^4 := one_le_pow₀ hK
  constructor
  · have hp := pow_le_one₀ hprod0 hprod1 (n := 2)
    unfold absBsgWordLambda absBsgKappa
    have hdiv : (absBsgEps c K * absBsgEps c K * absBsgEta c K)^2/K^4 ≤ 1 :=
      (div_le_one (by positivity)).mpr (hp.trans hK4)
    linarith
  · unfold absBsgWordEta
    exact (div_le_one (by positivity)).mpr (he1.trans hK2)

/-- The precise subset cutoff is also a polynomial monomial. -/
theorem absBsgWordBeta_monomial {c K : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (hK : 1 ≤ K) (k : Nat) :
    absBsgWordBeta c K k = (absBsgWordCoefficient k / 2) *
      c^(absBsgWordDensityExponent k) / K^(absBsgWordDoublingExponent k) := by
  have hK0 : 0 < K := by linarith
  have hp := absBsgWord_parameters_pos hc hK0 k
  have hu := absBsgWord_parameters_le_one hc hc1 hK
  unfold absBsgWordBeta
  rw [relationWordCutoff_eq hp.1 hu.1 hp.2.1 hu.2, absBsgWordDensity_monomial c K hK0.ne' k]
  ring

end LeanProofs.GowersSzemeredi
