/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientLaw

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem profileWidthFactor_le {I : Type*} [Fintype I] (w : I → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    profileWidthFactor w ≤ δ⁻¹ ^ Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, δ⁻¹ := Finset.prod_le_prod₀
      (fun i _ => inv_nonneg.mpr (hδ.le.trans (hw i))) (fun i _ => inv_anti₀ hδ (hw i))
    _ = _ := by simp

theorem normalizedCoefficientCoordinates_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith δ⁻¹ (fun x : I → ℝ => fun i => (x i - c i) / w i) := by
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖(x i-c i)/w i - (y i-c i)/w i‖ ≤ _
  rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div,
    abs_of_pos (hδr.trans_le (hw i))]
  calc
    _ ≤ ‖x-y‖ / w i := div_le_div_of_nonneg_right
      (norm_le_pi_norm (x-y) i) (hδr.le.trans (hw i))
    _ ≤ ‖x-y‖ / (δ : ℝ) := div_le_div_of_nonneg_left (norm_nonneg _) hδr (hw i)
    _ = _ := by simp only [NNReal.coe_inv, dist_eq_norm, div_eq_mul_inv]; ring

noncomputable def affineProductProfileLip (I : Type*) [Fintype I] (δ : ℝ≥0) : ℝ≥0 :=
  Fintype.card I * probabilityProfileLipschitz * δ⁻¹ ^ (Fintype.card I + 1)

theorem affineProductProfile_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith (affineProductProfileLip I δ) (affineProductProfile c w) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwp := profileWidthFactor_pos w (fun i => hδr.trans_le (hw i))
  have hl := (smoothProductProfile_lipschitz I).comp
    (normalizedCoefficientCoordinates_lipschitz c w hδ hw)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hl.dist_le_mul x y
  rw [Real.dist_eq] at hb ⊢
  rw [affineProductProfile_eq, affineProductProfile_eq, ← mul_sub, abs_mul, abs_of_pos hwp]
  calc
    _ ≤ profileWidthFactor w *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left hb hwp.le
    _ ≤ (δ : ℝ)⁻¹ ^ Fintype.card I *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_right (profileWidthFactor_le w hδr hw) (by positivity)
    _ = _ := by
      simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
        NNReal.coe_inv, pow_succ]
      ring

theorem affineProductProfile_cap {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    ∀ x, ‖affineProductProfile c w x‖ ≤ δ⁻¹ ^ Fintype.card I :=
  fun x => (affineProductProfile_norm_le c w (fun i => hδ.trans_le (hw i)) x).trans
    (profileWidthFactor_le w hδ hw)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem pow_le_exp_mul_of_le_exp {x Q P : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp Q)
    (hQ : 0 ≤ Q) (n : ℕ) (hn : (n : ℝ) ≤ P) : x^n ≤ Real.exp (P*Q) := by
  calc
    _ ≤ (Real.exp Q)^n := pow_le_pow_left₀ hx0 hx _
    _ = Real.exp ((n : ℝ)*Q) := (Real.exp_nat_mul Q n).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn hQ)

theorem mixedInterpolation_constants_exp_bounds {I : Type*} [Fintype I] (n : ℕ)
    {δ B L : ℝ≥0} {P W Q : ℝ} (hP : 0 ≤ P) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hI : (Fintype.card I : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hδ : ((δ⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp W)
    (hB : (B : ℝ) ≤ Real.exp Q) (hL : (L : ℝ) ≤ Real.exp Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    ((δ⁻¹^Fintype.card I * B^n : ℝ≥0) : ℝ) ≤ Real.exp (P*(W+Q)) ∧
      ((δ⁻¹^Fintype.card I * (n*L*B^n) + B^n*affineProductProfileLip I δ : ℝ≥0) : ℝ) ≤
        Real.exp ((2*P+1)*(W+Q)+3*P+1) := by
  have hδ0 : 0 ≤ ((δ⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hd := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I) hI
  have hb := pow_le_exp_mul_of_le_exp B.coe_nonneg hB hQ n hn
  have hd1 := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I + 1)
    (by push_cast; linarith : ((Fintype.card I + 1 : ℕ) : ℝ) ≤ P+1)
  have hIE : (Fintype.card I : ℝ) ≤ Real.exp P := hI.trans (by linarith [Real.add_one_le_exp P])
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  constructor
  · simp only [NNReal.coe_mul, NNReal.coe_pow]
    calc
      _ ≤ Real.exp (P*W) * Real.exp (P*Q) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      affineProductProfileLip]
    have hfirst : (((δ⁻¹ : ℝ≥0) : ℝ)^Fintype.card I) * ((n : ℝ)*L*(B : ℝ)^n) ≤
        Real.exp (P*W+P+Q+P*Q) := by
      calc
        _ ≤ Real.exp (P*W) * (Real.exp P * Real.exp Q * Real.exp (P*Q)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : (B : ℝ)^n * ((Fintype.card I : ℝ)*probabilityProfileLipschitz*
        ((δ⁻¹ : ℝ≥0) : ℝ)^(Fintype.card I+1)) ≤ Real.exp (P*Q+2*P+(P+1)*W) := by
      calc
        _ ≤ Real.exp (P*Q) * (Real.exp P * Real.exp P * Real.exp ((P+1)*W)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    exact hsum.trans_eq (congrArg Real.exp (by ring))

end Erdos3

end

section

namespace Erdos3

noncomputable def coefficientReplacementErrorLog {A : Type*} [Semiring A] (D L : A) : A :=
  3 * (D + 1) * (L + 3)

theorem coefficientReplacementError_small {D L target supportLog amplitude ε : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (htarget : 0 ≤ target)
    (hSupport : supportLog ≤ L) (ha0 : 0 ≤ amplitude) (ha : amplitude ≤ Real.exp L)
    (output axes : ℕ) (ho : (output : ℝ) ≤ D) (hn : (axes : ℝ) ≤ D)
    (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-(target + coefficientReplacementErrorLog D L))) :
    (2 * Real.exp supportLog + 1) ^ output *
      (axes * ε * (1 + amplitude + ε) ^ axes) ≤ Real.exp (-target) := by
  let Q := coefficientReplacementErrorLog D L
  have hQ : 0 ≤ Q := by dsimp [Q, coefficientReplacementErrorLog]; positivity
  have he1 : ε ≤ 1 := hε.trans (Real.exp_le_one_iff.mpr (by change -(target + Q) ≤ 0; linarith))
  have heL : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 2 * Real.exp supportLog + 1 ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith [Real.exp_le_exp.mpr hSupport]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have hbase' : 1 + amplitude + ε ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith only [ha, he1, heL]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have ho' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * Real.exp supportLog + 1)
    hbase (by positivity : 0 ≤ L + 3) output ho
  have hn' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 1 + amplitude + ε)
    hbase' (by positivity : 0 ≤ L + 3) axes hn
  have haxes : (axes : ℝ) ≤ Real.exp D := hn.trans (by linarith [Real.add_one_le_exp D])
  have hcost : D * (L + 3) + D + D * (L + 3) ≤ Q := by
    dsimp [Q, coefficientReplacementErrorLog]
    nlinarith [mul_nonneg hD hL]
  have hcoeff : (2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes ≤ Real.exp Q := by
    calc
      _ ≤ Real.exp (D * (L + 3)) * Real.exp D * Real.exp (D * (L + 3)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hcost
  calc
    _ = ((2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes) * ε := by ring
    _ ≤ Real.exp Q * Real.exp (-(target + Q)) :=
      (mul_le_mul_of_nonneg_right hcoeff hε0).trans (mul_le_mul_of_nonneg_left hε (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def inactiveNaturalShortScale (c h q : ℕ) : ℕ := 4 * (2 * ((c + 1) * q)) ^ h

def inactiveShortScaleLog {A : Type*} [Semiring A] (D v : A) : A :=
  4 + D * (1 + D + v)

def inactiveShortCapLog {A : Type*} [Semiring A] (D v : A) : A :=
  D * inactiveShortScaleLog D v

def inactiveShortLipschitzLog {A : Type*} [Semiring A] (D v : A) : A :=
  2 * D + 1 + (D + 2) * inactiveShortScaleLog D v

theorem inactiveShortLogs_nonneg {D v : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) :
    0 ≤ inactiveShortScaleLog D v ∧ 0 ≤ inactiveShortCapLog D v ∧
      0 ≤ inactiveShortLipschitzLog D v := by
  unfold inactiveShortCapLog inactiveShortLipschitzLog inactiveShortScaleLog
  exact ⟨by positivity, by positivity, by positivity⟩

theorem inactiveNaturalShortScale_exp_bound (c h q : ℕ) {D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hc : (c : ℝ) ≤ D) (hh : (h : ℝ) ≤ D)
    (hq : (q : ℝ) ≤ Real.exp v) :
    (inactiveNaturalShortScale c h q : ℝ) ≤ Real.exp (inactiveShortScaleLog D v) := by
  have hc1 : (c : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprod := (mul_le_mul hc1 hq (Nat.cast_nonneg q) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hbase := (mul_le_mul htwo hprod (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hbase
    (by positivity : 0 ≤ 1 + (D + v)) h hh
  have hbound := (mul_le_mul hfour hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  calc
    _ = 4 * (2 * (((c : ℝ) + 1) * q)) ^ h := by simp [inactiveNaturalShortScale]
    _ ≤ _ := hbound
    _ = _ := by unfold inactiveShortScaleLog; congr 1; ring

theorem inactiveNaturalShortResources_exp_bounds (c h q r : ℕ) {D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hc : (c : ℝ) ≤ D) (hh : (h : ℝ) ≤ D)
    (hr : (r : ℝ) ≤ D) (hq : (q : ℝ) ≤ Real.exp v) :
    let N := inactiveNaturalShortScale c h q
    (N : ℝ) ^ r ≤ Real.exp (inactiveShortCapLog D v) ∧
      (((r * (2 * (N : ℝ≥0) ^ 2) * (N : ℝ≥0) ^ r) * (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤
        Real.exp (inactiveShortLipschitzLog D v) := by
  let N := inactiveNaturalShortScale c h q
  have hN : (N : ℝ) ≤ Real.exp (inactiveShortScaleLog D v) :=
    inactiveNaturalShortScale_exp_bound c h q hD hv hc hh hq
  have hNlog := (inactiveShortLogs_nonneg hD hv).1
  have hNr := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg N) hN hNlog r hr
  have hN2 := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg N) hN hNlog 2 le_rfl
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have htwoc : (2 : ℝ) ^ c ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) c hc
  have hrexp : (r : ℝ) ≤ Real.exp D := hr.trans (by linarith [Real.add_one_le_exp D])
  have hsecond := (mul_le_mul htwo hN2 (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul hrexp hsecond (by positivity) (Real.exp_pos _).le) hNr
      (by positivity) (by positivity)) htwoc (by positivity) (by positivity)
  simp only [← Real.exp_add] at hprod
  refine ⟨hNr, ?_⟩
  have hfinal : (r : ℝ) * (2 * (N : ℝ) ^ 2) * (N : ℝ) ^ r * 2 ^ c ≤
      Real.exp (inactiveShortLipschitzLog D v) :=
    hprod.trans_eq (by unfold inactiveShortLipschitzLog; congr 1; ring)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] using hfinal

end Erdos3

end

end OAI
