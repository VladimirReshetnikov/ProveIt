/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.NNReal.Defs
import OAI.Combinatorics.Progressions.Estimates.AlgebraicMajorUniformExponent
import OAI.Combinatorics.Progressions.Estimates.ModeRemovalThresholds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem add_le_exp_add_one {x y P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hx : x ≤ Real.exp P) (hy : y ≤ Real.exp Q) : x+y ≤ Real.exp (P+Q+1) := by
  have hx' := hx.trans (Real.exp_le_exp.mpr (show P ≤ P+Q by linarith))
  have hy' := hy.trans (Real.exp_le_exp.mpr (show Q ≤ P+Q by linarith))
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp (P+Q) := by linarith
    _ ≤ Real.exp 1*Real.exp (P+Q) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem sum_le_exp_card_add_sum {I : Type*} [Fintype I]
    (x P : I → ℝ) (hP : ∀ i, 0 ≤ P i) (hx : ∀ i, x i ≤ Real.exp (P i)) :
    (∑ i, x i) ≤ Real.exp ((Fintype.card I : ℝ)+∑ i, P i) := by
  have hi (i) : P i ≤ ∑ j, P j := Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)
  have hcard : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  calc
    _ ≤ ∑ _i : I, Real.exp (∑ j, P j) :=
      Finset.sum_le_sum (fun i _ => (hx i).trans (Real.exp_le_exp.mpr (hi i)))
    _ = (Fintype.card I : ℝ)*Real.exp (∑ j, P j) := by simp
    _ ≤ Real.exp (Fintype.card I)*Real.exp (∑ j, P j) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem coe_toNNReal_le_exp {x P : ℝ} (hx : x ≤ Real.exp P) :
    (Real.toNNReal x : ℝ) ≤ Real.exp P := by
  rw [Real.coe_toNNReal']
  exact max_le hx (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalIdealErrorShare (E cost : ℝ) : ℝ :=
  Real.exp (-(E + cost + 3))

theorem physicalIdealErrorShare_pos (E cost : ℝ) : 0 < physicalIdealErrorShare E cost :=
  Real.exp_pos _

theorem physicalIdealErrorShare_le_one {E cost : ℝ} (hE : 0 ≤ E) (hc : 0 ≤ cost) :
    physicalIdealErrorShare E cost ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  linarith

theorem physicalIdealErrorShare_inv (E cost : ℝ) :
    (physicalIdealErrorShare E cost)⁻¹ = Real.exp (E + cost + 3) := by
  simp only [physicalIdealErrorShare, Real.exp_neg, inv_inv]

theorem exp_mul_physicalIdealErrorShare (E cost : ℝ) :
    Real.exp cost * physicalIdealErrorShare E cost = Real.exp (-E - 3) := by
  rw [physicalIdealErrorShare, ← Real.exp_add]
  congr 1
  ring

theorem physicalIdealErrorShare_half_inverse_le (E cost : ℝ) :
    (physicalIdealErrorShare E cost / 2)⁻¹ ≤ Real.exp (E + cost + 4) := by
  rw [inv_div, div_eq_mul_inv, physicalIdealErrorShare_inv]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + cost + 3) :=
      mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem physicalIdealErrorShare_scale_mesh (n : ℕ) {S E cost : ℝ}
    (hE : 0 ≤ E) (hc : 0 ≤ cost) (hS : Real.exp (E + cost + 3) ≤ S) :
    1 / S ^ (n + 1) ≤ physicalIdealErrorShare E cost := by
  have hS1 : 1 ≤ S :=
    (Real.one_le_exp_iff.mpr (show 0 ≤ E + cost + 3 by positivity)).trans hS
  have hpow : S ≤ S ^ (n + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hS1 (show 1 ≤ n + 1 by omega)
  calc
    _ ≤ 1 / Real.exp (E + cost + 3) :=
      one_div_le_one_div_of_le (Real.exp_pos _) (hS.trans hpow)
    _ = _ := by rw [physicalIdealErrorShare, Real.exp_neg, one_div]

theorem physicalIdeal_three_errors_le {V W K E a b c η ε mesh : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haV : a ≤ Real.exp V) (hbW : b ≤ Real.exp W) (hcK : c ≤ Real.exp K)
    (hη : η ≤ physicalIdealErrorShare E V)
    (hε : ε ≤ physicalIdealErrorShare E W)
    (hmesh : mesh ≤ physicalIdealErrorShare E (W + K)) :
    a * η + b * (ε + c * mesh) ≤ Real.exp (-E) := by
  have hfirst : a * η ≤ Real.exp (-E - 3) := by
    calc
      _ ≤ a * physicalIdealErrorShare E V := mul_le_mul_of_nonneg_left hη ha
      _ ≤ Real.exp V * physicalIdealErrorShare E V :=
        mul_le_mul_of_nonneg_right haV (physicalIdealErrorShare_pos E V).le
      _ = _ := exp_mul_physicalIdealErrorShare E V
  have hsecond : b * ε ≤ Real.exp (-E - 3) := by
    calc
      _ ≤ b * physicalIdealErrorShare E W := mul_le_mul_of_nonneg_left hε hb
      _ ≤ Real.exp W * physicalIdealErrorShare E W :=
        mul_le_mul_of_nonneg_right hbW (physicalIdealErrorShare_pos E W).le
      _ = _ := exp_mul_physicalIdealErrorShare E W
  have hprod : b * c ≤ Real.exp (W + K) := by
    rw [Real.exp_add]
    exact mul_le_mul hbW hcK hc (Real.exp_pos _).le
  have hthird : b * (c * mesh) ≤ Real.exp (-E - 3) := by
    rw [← mul_assoc]
    calc
      _ ≤ (b * c) * physicalIdealErrorShare E (W + K) :=
        mul_le_mul_of_nonneg_left hmesh (mul_nonneg hb hc)
      _ ≤ Real.exp (W + K) * physicalIdealErrorShare E (W + K) :=
        mul_le_mul_of_nonneg_right hprod (physicalIdealErrorShare_pos E (W + K)).le
      _ = _ := exp_mul_physicalIdealErrorShare E (W + K)
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-E - 3) := by rw [mul_add]; linarith
    _ ≤ Real.exp 3 * Real.exp (-E - 3) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem algebraicMajor_mass_le_exp (d : ℕ) {p massF₀ massE massV Cbase : ℝ}
    (hp : 0 ≤ p) (_hF₀ : 0 ≤ massF₀) (_hE : 0 ≤ massE)
    (_hV : 0 ≤ massV) (hC : 0 ≤ Cbase)
    (hF₀p : massF₀ ≤ Real.exp p) (hEp : massE ≤ Real.exp p)
    (hVp : massV ≤ Real.exp p) (hCp : Cbase ≤ Real.exp p) :
    massF₀ + (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (((d : ℝ) + 3) * (p + 2)) := by
  have hsum : massE + massV ≤ Real.exp (2*p + 1) := by
    simpa only [two_mul] using add_le_exp_add_one hp hp hEp hVp
  have hbase := one_add_le_exp_succ hp hCp
  have hterm : (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (2*p + 1 + (d : ℝ)*(p + 1)) := by
    calc
      _ ≤ Real.exp (2*p + 1) * (Real.exp (p + 1))^d := by
        exact mul_le_mul hsum
          (pow_le_pow_left₀ (by positivity) hbase d) (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have htotal := add_le_exp_add_one hp
    (by positivity : 0 ≤ 2*p + 1 + (d : ℝ)*(p + 1)) hF₀p hterm
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem algebraicMajor_denominator_le_exp (d qV qNat : ℕ) {p : ℝ}
    (hqV : (qV : ℝ) ≤ Real.exp p) (hqNat : (qNat : ℝ) ≤ Real.exp p) :
    (((qV*qNat)^(d+1) : ℕ) : ℝ) ≤
      Real.exp (2*((d : ℝ)+1)*p) := by
  have hprod : ((qV*qNat : ℕ) : ℝ) ≤ Real.exp (2*p) := by
    rw [Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hqV hqNat (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ = (((qV*qNat : ℕ) : ℝ))^(d+1) := by rw [Nat.cast_pow]
    _ ≤ (Real.exp (2*p))^(d+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem exists_algebraicMajor_output_budget (d a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
    ∀ massF₀ massE massV Cbase : ℝ,
    0 ≤ massF₀ → 0 ≤ massE → 0 ≤ massV → 0 ≤ Cbase →
    massF₀ ≤ Real.exp ((p+a)^a) → massE ≤ Real.exp ((p+a)^a) →
    massV ≤ Real.exp ((p+a)^a) → Cbase ≤ Real.exp ((p+a)^a) →
    ∀ qV qNat : ℕ, (qV : ℝ) ≤ Real.exp ((p+a)^a) →
    (qNat : ℝ) ≤ Real.exp ((p+a)^a) →
    massF₀ + (massE + massV) * (1 + Cbase)^((d+1)^2) ≤
      Real.exp ((p+C)^C) ∧
    (((qV*qNat)^((d+1)^2+1) : ℕ) : ℝ) ≤ Real.exp ((p+C)^C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_algebraicMajor_uniform_exponent d a
  refine ⟨C, hC, ?_⟩
  intro p hp massF₀ massE massV Cbase hF₀ hE hV hbase hF₀p hEp hVp hbasep qV qNat hqV hqNat
  obtain ⟨hmass, hden⟩ := hbudget p hp
  constructor
  · apply (algebraicMajor_mass_le_exp ((d+1)^2) (by positivity) hF₀ hE hV hbase
      hF₀p hEp hVp hbasep).trans
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hmass
  · apply (algebraicMajor_denominator_le_exp ((d+1)^2) qV qNat hqV hqNat).trans
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hden

end Erdos3

end

section

namespace Erdos3

noncomputable def modeProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊

noncomputable def modeProfileLog (P : ℝ) : ℝ := 5 * P + (modeProfileBound : ℝ) + 4

theorem modeProfileLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeProfileLog P := by
  unfold modeProfileLog
  positivity

theorem modeRemovalConstants_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    modeRemovalTranslationConstant d ≤ Real.exp (modeProfileLog P) ∧
      modeRemovalMeshConstant d ≤ Real.exp (modeProfileLog P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (d : ℝ) ≤ Real.exp P := hd.trans (by linarith [Real.add_one_le_exp P])
  have hL : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (modeProfileBound : ℝ) := by
    have hc : (probabilityProfileLipschitz : ℝ) ≤ modeProfileBound := Nat.le_ceil _
    exact hc.trans (by linarith [Real.add_one_le_exp (modeProfileBound : ℝ)])
  constructor
  · unfold modeRemovalTranslationConstant
    calc
      _ ≤ Real.exp 4 * (Real.exp 3) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 + 3 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; nlinarith)
  · unfold modeRemovalMeshConstant
    calc
      _ ≤ (Real.exp 4) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; linarith)

theorem modeRemovalMesh_inv_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    1 / modeRemovalMesh d ≤ Real.exp (modeProfileLog P + 3) := by
  have hc0 := modeRemovalMeshConstant_nonneg d
  have hc : modeRemovalMeshConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).2
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  simp only [modeRemovalMesh, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (modeProfileLog P + 1) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem modeRemovalRadius_inv_le_exp (d : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalRadius d ε ≤ Real.exp (modeProfileLog P + P + 3) := by
  have hc0 := modeRemovalTranslationConstant_nonneg d
  have hc : modeRemovalTranslationConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).1
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have he : 1 / modeRemovalRadius d ε = 2 * (modeRemovalTranslationConstant d + 1) * (1 / ε) := by
    rw [modeRemovalRadius, one_div, inv_div]
    simp only [div_eq_mul_inv, one_mul]
  rw [he]
  calc
    _ ≤ (Real.exp 2 * Real.exp (modeProfileLog P + 1)) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def multiaffineInverseConstant (n : ℕ) : ℕ :=
  denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n

def multiaffineInverseExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

def finiteLayerInverseConstant (m : ℕ) : ℕ := m + 1 + ∑ i : Fin m, multiaffineInverseConstant i.val

def finiteLayerInverseExponent (m : ℕ) : ℕ := ∑ i : Fin m, multiaffineInverseExponent i.val

def finiteLayerInverseLog (m : ℕ) (Z : ℝ) : ℝ :=
  (finiteLayerInverseConstant m : ℝ) + (finiteLayerInverseExponent m : ℝ) * Z

theorem multiaffineBiasBudget_eq_inverse_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      (multiaffineInverseConstant n : ℝ) * (1 / ζ) ^ multiaffineInverseExponent n := by
  rw [multiaffineBiasBudget_eq_power n hζ]
  simp only [multiaffineInverseConstant, multiaffineInverseExponent,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul, inv_pow]

theorem multiaffineBiasBudget_le_exp (n : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ)
    (hZ : 1 / ζ ≤ Real.exp Z) :
    multiaffineBiasBudget n ζ ≤ Real.exp
      ((multiaffineInverseConstant n : ℝ) + (multiaffineInverseExponent n : ℝ) * Z) := by
  have hc : (multiaffineInverseConstant n : ℝ) ≤ Real.exp (multiaffineInverseConstant n : ℝ) := by
    linarith [Real.add_one_le_exp (multiaffineInverseConstant n : ℝ)]
  rw [multiaffineBiasBudget_eq_inverse_power n hζ]
  calc
    _ ≤ Real.exp (multiaffineInverseConstant n : ℝ) *
        (Real.exp Z) ^ multiaffineInverseExponent n := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem finiteLayerInverseLog_nonneg (m : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ finiteLayerInverseLog m Z := by unfold finiteLayerInverseLog; positivity

theorem finiteLayerBiasBudget_le_exp (m : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ) (hZ : 0 ≤ Z)
    (hInv : 1 / ζ ≤ Real.exp Z) : finiteLayerBiasBudget m ζ ≤ Real.exp (finiteLayerInverseLog m Z) := by
  have hsum := sum_le_exp_card_add_sum
    (fun i : Fin m => multiaffineBiasBudget i.val ζ)
    (fun i : Fin m => (multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z)
    (fun _ => by positivity) (fun i => multiaffineBiasBudget_le_exp i.val hζ hInv)
  have hs0 : 0 ≤ (Fintype.card (Fin m) : ℝ) +
      ∑ i : Fin m, ((multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z) := by
    positivity
  have h := one_add_le_exp_succ hs0 hsum
  change 1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ ≤ _
  convert h using 1
  congr 1
  simp only [finiteLayerInverseLog, finiteLayerInverseConstant, finiteLayerInverseExponent,
    Nat.cast_add, Nat.cast_one, Nat.cast_sum, Fintype.card_fin, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

theorem modeRemovalBeta_inv_le_exp {ε P : ℝ} (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBeta ε ≤ Real.exp (P + 2) := by
  have hEP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hmin : (modeRemovalBeta ε)⁻¹ ≤ 2 * Real.exp P := by
    apply inv_min_le_of_inv_le
    · norm_num
      linarith
    · rw [inv_div]
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hεInv (by norm_num : (0 : ℝ) ≤ 2)
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 2 * Real.exp P := by simpa only [one_div] using hmin
    _ ≤ Real.exp 2 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem modeRemovalBias_inv_le_exp (m : ℕ) {ε P : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBias m ε ≤ Real.exp (((2 ^ m : ℕ) : ℝ) * (P + 2)) := by
  have h := pow_le_pow_left₀ (div_nonneg zero_le_one (modeRemovalBeta_pos hε).le)
    (modeRemovalBeta_inv_le_exp hP hεInv) (2 ^ m)
  simpa only [modeRemovalBias, div_pow, one_pow, ← Real.exp_nat_mul] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def modeBiasLog (m : ℕ) (P : ℝ) : ℝ :=
  finiteLayerInverseLog m (((2 ^ m : ℕ) : ℝ) * (P + 2))

noncomputable def modeShrinkLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + modeProfileLog P + 3 * P + 4

noncomputable def modeSideLog (m : ℕ) (P : ℝ) : ℝ :=
  (P + modeShrinkLog m P + modeBiasLog m P + 1) + (P + modeProfileLog P + 3) + 2

theorem modeBiasLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeBiasLog m P :=
  finiteLayerInverseLog_nonneg m (by positivity)

theorem modeShrinkLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeShrinkLog m P := by
  have he := modeProfileLog_nonneg hP
  unfold modeShrinkLog
  positivity

theorem modeSideLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeSideLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  have he := modeProfileLog_nonneg hP
  unfold modeSideLog
  positivity

theorem chosenBiasBudget_le_exp (m : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    finiteLayerBiasBudget m (modeRemovalBias m ε) ≤ Real.exp (modeBiasLog m P) :=
  finiteLayerBiasBudget_le_exp m (modeRemovalBias_pos m hε) (by positivity)
    (modeRemovalBias_inv_le_exp m hε hP hεInv)

theorem modeRemovalShrink_le_exp (m d : ℕ) {P D ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalShrink m d D ρ ε ≤ Real.exp (modeShrinkLog m P) := by
  have hm : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hr := modeRemovalRadius_pos d hε
  have hrInv := modeRemovalRadius_inv_le_exp d hP hd hε hεInv
  have hE := modeProfileLog_nonneg hP
  have hprod : (m : ℝ) * D / (modeRemovalRadius d ε * ρ) ≤
      Real.exp ((m : ℝ) + modeProfileLog P + 3 * P + 3) := by
    calc
      _ = (m : ℝ) * D * (1 / modeRemovalRadius d ε) * (1 / ρ) := by
        simp only [div_eq_mul_inv, mul_inv, one_mul]
        ring
      _ ≤ Real.exp (m : ℝ) * Real.exp P * Real.exp (modeProfileLog P + P + 3) * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h := one_add_le_exp_succ (by positivity) hprod
  have he : ((m : ℝ) + modeProfileLog P + 3 * P + 3) + 1 = modeShrinkLog m P := by
    unfold modeShrinkLog
    ring
  simpa only [modeRemovalShrink, he] using h

theorem modeRemovalSideThreshold_le_exp (m d : ℕ) {P D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (_hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp (modeSideLog m P) := by
  have ht := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hb := chosenBiasBudget_le_exp m hP hε hεInv
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hBlog := modeBiasLog_nonneg m hP
  have hTlog := modeShrinkLog_nonneg m hP
  have hE := modeProfileLog_nonneg hP
  have hb1 : finiteLayerBiasBudget m (modeRemovalBias m ε) + 1 ≤ Real.exp (modeBiasLog m P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hBlog hb
  have ha : S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      Real.exp (P + modeShrinkLog m P + modeBiasLog m P + 1) := by
    calc
      _ ≤ Real.exp P * Real.exp (modeShrinkLog m P) * Real.exp (modeBiasLog m P + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hδ := modeRemovalMesh_pos d
  have hδInv := modeRemovalMesh_inv_le_exp d hP hd
  have hc : 1 / (ρ * modeRemovalMesh d) ≤ Real.exp (P + modeProfileLog P + 3) := by
    calc
      _ = (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp (modeProfileLog P + 3) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum := add_le_exp_add_one (by positivity) (by positivity) ha hc
  have hout := one_add_le_exp_succ (by positivity) hsum
  convert hout using 1
  · unfold modeRemovalSideThreshold
    ring
  · congr 1
    unfold modeSideLog
    ring

end Erdos3

end

end OAI
