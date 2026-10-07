import OAI.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
import OAI.Combinatorics.Progressions.Sampling.AmbientL1SamplingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

def affineAmbientMassLog {A : Type*} [Semiring A] (P : A) : A :=
  4 * P ^ 3 + 9 * P ^ 2 + 5 * P

theorem affineAmbientMassLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineAmbientMassLog P := by unfold affineAmbientMassLog; positivity

theorem affineAmbientMass_le_exp {P Q inv mask : ℝ} {sites axes labels : ℕ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hQP : Q ≤ P)
    (hsites : (sites : ℝ) ≤ P) (haxes : (axes : ℝ) ≤ P)
    (hlabels : (labels : ℝ) ≤ Real.exp P)
    (hinv0 : 0 ≤ inv) (hinv : inv ≤ Real.exp P)
    (hmask0 : 0 ≤ mask) (hmask : mask ≤ Real.exp P) :
    (Real.toNNReal ((2 : ℝ) ^ sites * inv * ((labels : ℝ) ^ sites * mask *
      Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q))) : ℝ) ≤
        Real.exp (affineAmbientMassLog P) := by
  rw [Real.toNNReal_of_nonneg (by positivity)]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow : (2 : ℝ) ^ sites ≤ Real.exp (2 * P) := by
    apply (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo sites).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hl : (labels : ℝ) ^ sites ≤ Real.exp (P ^ 2) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hlabels sites).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp : Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q) ≤
      Real.exp (P ^ 2 * (4 * P + 8) + P) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have hsa : (sites : ℝ) * axes ≤ P ^ 2 := by
      simpa only [pow_two] using mul_le_mul hsites haxes (Nat.cast_nonneg _) hP
    have hh := mul_le_mul hsa (show 4 * Q + 8 ≤ 4 * P + 8 by linarith)
      (by linarith : 0 ≤ 4 * Q + 8) (sq_nonneg P)
    linarith
  calc
    _ ≤ Real.exp (2 * P) * Real.exp P *
        (Real.exp (P ^ 2) * Real.exp P * Real.exp (P ^ 2 * (4 * P + 8) + P)) :=
      mul_le_mul (mul_le_mul hpow hinv hinv0 (Real.exp_nonneg _))
        (mul_le_mul (mul_le_mul hl hmask hmask0 (Real.exp_nonneg _)) hexp
          (Real.exp_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold affineAmbientMassLog
      ring

theorem affineAmbientLift_le_exp {P : ℝ} (hP : 0 ≤ P)
    {N mass Lgrid d sites Lsite Lrows : ℝ≥0}
    (hN : (N : ℝ) ≤ Real.exp P) (hmass : (mass : ℝ) ≤ Real.exp (affineAmbientMassLog P))
    (hg : (Lgrid : ℝ) ≤ Real.exp P) (hd : (d : ℝ) ≤ Real.exp P)
    (hs : (sites : ℝ) ≤ Real.exp P) (hl : (Lsite : ℝ) ≤ Real.exp P)
    (hr : (Lrows : ℝ) ≤ Real.exp P) :
    ((N * mass : ℝ≥0) : ℝ) ≤ Real.exp (affineAmbientMassLog P + P) ∧
      ((N * (mass * (Lgrid * d) + mass * (sites * (Lsite * Lrows))) : ℝ≥0) : ℝ) ≤
        Real.exp (2 * affineAmbientMassLog P + 7 * P + 1) := by
  have hM := affineAmbientMassLog_nonneg hP
  constructor
  · simp only [NNReal.coe_mul]
    exact (mul_le_mul hN hmass mass.coe_nonneg (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add, add_comm])
  · simp only [NNReal.coe_mul, NNReal.coe_add]
    rw [mul_add]
    have hfirst : (N : ℝ) * (mass * (Lgrid * d)) ≤ Real.exp (affineAmbientMassLog P + 3 * P) := by
      calc
        _ ≤ Real.exp P * (Real.exp (affineAmbientMassLog P) * (Real.exp P * Real.exp P)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : (N : ℝ) * (mass * (sites * (Lsite * Lrows))) ≤
        Real.exp (affineAmbientMassLog P + 4 * P) := by
      calc
        _ ≤ Real.exp P * (Real.exp (affineAmbientMassLog P) *
          (Real.exp P * (Real.exp P * Real.exp P))) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
      (congrArg Real.exp (by ring))

theorem affineAmbientSiteLip_le_exp {P : ℝ} (hP : 0 ≤ P)
    {axes cutoff r coord L : ℝ≥0} {d period : ℕ}
    (ha : (axes : ℝ) ≤ Real.exp P) (hc : (cutoff : ℝ) ≤ Real.exp P)
    (hr : ((2 * r)⁻¹ : ℝ≥0) ≤ Real.exp P) (hcoord : (coord : ℝ) ≤ Real.exp P)
    (hL : (L : ℝ) ≤ Real.exp P) (hd : (d : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp P) :
    (((axes * cutoff / (2 * r)) * coord * d +
      max (L * coord * period) (4 * period) * (d / period : ℕ) : ℝ≥0) : ℝ) ≤
        Real.exp (9 * P + 5) := by
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hfirst : (((axes * cutoff / (2 * r)) * coord * d : ℝ≥0) : ℝ) ≤ Real.exp (5 * P) := by
    simp only [div_eq_mul_inv, NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ ((Real.exp P * Real.exp P * Real.exp P) * Real.exp P) * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hmax : ((max (L * coord * period) (4 * period) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P + 4) := by
    simp only [NNReal.coe_max, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
    apply max_le
    · calc
        _ ≤ Real.exp P * Real.exp P * Real.exp P := by gcongr
        _ = Real.exp (3 * P) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        _ ≤ Real.exp 4 * Real.exp P := by gcongr
        _ = Real.exp (4 + P) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsecond : ((max (L * coord * period) (4 * period) * (d / period : ℕ) : ℝ≥0) : ℝ) ≤
      Real.exp (4 * P + 4) := by
    simp only [NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp (3 * P + 4) * Real.exp P := mul_le_mul hmax
        ((Nat.cast_le.mpr (Nat.div_le_self d period)).trans hd) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [NNReal.coe_add]
  exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
    (congrArg Real.exp (by ring))

theorem affineAmbientGridLip_le_exp {P : ℝ} (_hP : 0 ≤ P)
    {axes outputs height coord : ℝ≥0}
    (ha : (axes : ℝ) ≤ Real.exp P) (ho : (outputs : ℝ) ≤ Real.exp P)
    (hh : (height : ℝ) ≤ Real.exp P) (hc : (coord : ℝ) ≤ Real.exp P) :
    ((axes * (outputs * (2 * height ^ 2)) * coord : ℝ≥0) : ℝ) ≤ Real.exp (5 * P + 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  calc
    _ ≤ Real.exp P * (Real.exp P * (Real.exp 2 * Real.exp P ^ 2)) * Real.exp P := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

noncomputable def affineAmbientPrimitiveBudget {A : Type*} [Semiring A] (base Q : A) : A :=
  let P₂ := 9 * (9 * (base + Q) + 13) + 5
  2 * affineAmbientMassLog P₂ + 7 * P₂ + 1

theorem affineAmbientPrimitive_bounds {base Q inv mask : ℝ}
    {sites axes labels gridaxes outputs d period : ℕ}
    {N K coords cutoff r radius Lrows height : ℝ≥0}
    (hb : 0 ≤ base) (hQ : 0 ≤ Q)
    (hsites : (sites : ℝ) ≤ base) (haxes : (axes : ℝ) ≤ base)
    (hlabels : (labels : ℝ) ≤ Real.exp base)
    (hinv0 : 0 ≤ inv) (hinv : inv ≤ Real.exp base)
    (hmask0 : 0 ≤ mask) (hmask : mask ≤ Real.exp base)
    (hN : (N : ℝ) ≤ Real.exp base) (hK : (K : ℝ) ≤ Real.exp base)
    (hcoords : (coords : ℝ) ≤ Real.exp base) (hc : (cutoff : ℝ) ≤ Real.exp base)
    (hr : 1 ≤ r) (hradius : 1 ≤ radius)
    (hd : (d : ℝ) ≤ Real.exp base) (hperiod : (period : ℝ) ≤ Real.exp base)
    (hrows : (Lrows : ℝ) ≤ Real.exp base)
    (hgaxes : (gridaxes : ℝ) ≤ base) (houtputs : (outputs : ℝ) ≤ base)
    (hheight : (height : ℝ) ≤ Real.exp base) :
    let mass := Real.toNNReal ((2 : ℝ) ^ sites * inv * ((labels : ℝ) ^ sites * mask *
      Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q)))
    let L : ℝ≥0 := ⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)
    let coord := K * coords
    let Lsite := (axes * cutoff / (2 * r)) * coord * d +
      max (L * coord * period) (4 * period) * (d / period : ℕ)
    let Lgrid := (gridaxes * (outputs * (2 * height ^ 2))) * coords
    let T := affineAmbientPrimitiveBudget base Q
    ((N * mass : ℝ≥0) : ℝ) ≤ Real.exp T ∧
      ((N * (mass * (Lgrid * d) + mass * (sites * (Lsite * Lrows))) : ℝ≥0) : ℝ) ≤ Real.exp T := by
  intro mass L coord Lsite Lgrid T
  let P := base + Q
  let P₁ := 9 * P + 13
  let P₂ := 9 * P₁ + 5
  have hP : 0 ≤ P := add_nonneg hb hQ
  have hbP : base ≤ P := le_add_of_nonneg_right hQ
  have hQP : Q ≤ P := le_add_of_nonneg_left hb
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp [P₂]; positivity
  have hPP₁ : P ≤ P₁ := by dsimp [P₁]; linarith
  have hP₁P₂ : P₁ ≤ P₂ := by dsimp [P₂]; linarith
  have hbP₂ := hbP.trans (hPP₁.trans hP₁P₂)
  have hexp : Real.exp base ≤ Real.exp P₂ := Real.exp_le_exp.mpr hbP₂
  have hbaseE : base ≤ Real.exp base := by linarith [Real.add_one_le_exp base]
  have hL : (L : ℝ) ≤ Real.exp P₁ := by
    have hden : (1 : ℝ) ≤ 2 * (radius : ℝ) := by exact_mod_cast (by linarith : (1 : ℝ≥0) ≤ 2 * radius)
    have hcut : ((axes * cutoff / (2 * radius) : ℝ≥0) : ℝ) ≤ Real.exp (2 * P) := by
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
      apply (div_le_self (by positivity) hden).trans
      calc
        _ ≤ Real.exp P * Real.exp P := mul_le_mul
          ((haxes.trans hbaseE).trans (Real.exp_le_exp.mpr hbP))
          (hc.trans (Real.exp_le_exp.mpr hbP)) cutoff.coe_nonneg (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hraw : Real.exp (axes + 6 * Q + 12) ≤ Real.exp (7 * P + 12) :=
      Real.exp_le_exp.mpr (by linarith)
    change Real.exp (axes + 6 * Q + 12) + _ ≤ _
    exact (add_le_exp_add_one (by positivity) (by positivity) hraw hcut).trans_eq
      (congrArg Real.exp (by dsimp [P₁]; ring))
  have hcoord : (coord : ℝ) ≤ Real.exp P₁ := by
    change (K : ℝ) * coords ≤ _
    calc
      _ ≤ Real.exp base * Real.exp base := mul_le_mul hK hcoords coords.coe_nonneg (Real.exp_nonneg _)
      _ = Real.exp (2 * base) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [P₁, P]; linarith)
  have hrInv : (((2 * r)⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp P₁ := by
    have hden : (1 : ℝ≥0) ≤ 2 * r := by linarith
    have hh : (2 * r)⁻¹ ≤ (1 : ℝ≥0) := inv_le_one_of_one_le₀ hden
    exact (NNReal.coe_le_coe.mpr hh).trans (Real.one_le_exp hP₁)
  have hbase₁ : Real.exp base ≤ Real.exp P₁ := Real.exp_le_exp.mpr (hbP.trans hPP₁)
  have hsite : (Lsite : ℝ) ≤ Real.exp P₂ :=
    affineAmbientSiteLip_le_exp hP₁ ((haxes.trans hbaseE).trans hbase₁)
      (hc.trans hbase₁) hrInv hcoord hL (hd.trans hbase₁) (hperiod.trans hbase₁)
  have hgrid : (Lgrid : ℝ) ≤ Real.exp P₂ := by
    apply (affineAmbientGridLip_le_exp (axes := (gridaxes : ℝ≥0)) (outputs := (outputs : ℝ≥0)) hb (hgaxes.trans hbaseE) (houtputs.trans hbaseE) hheight hcoords).trans
    exact Real.exp_le_exp.mpr (by dsimp [P₂, P₁, P]; linarith)
  have hm : (mass : ℝ) ≤ Real.exp (affineAmbientMassLog P₂) :=
    affineAmbientMass_le_exp hP₂ hQ (hQP.trans (hPP₁.trans hP₁P₂))
      (hsites.trans hbP₂) (haxes.trans hbP₂) (hlabels.trans hexp)
      hinv0 (hinv.trans hexp) hmask0 (hmask.trans hexp)
  have hbound := affineAmbientLift_le_exp (d := (d : ℝ≥0)) (sites := (sites : ℝ≥0)) hP₂ (hN.trans hexp) hm hgrid (hd.trans hexp)
    ((hsites.trans hbaseE).trans hexp) hsite (hrows.trans hexp)
  refine ⟨hbound.1.trans (Real.exp_le_exp.mpr ?_), hbound.2⟩
  change affineAmbientMassLog P₂ + P₂ ≤ 2 * affineAmbientMassLog P₂ + 7 * P₂ + 1
  linarith [affineAmbientMassLog_nonneg hP₂]

theorem exists_affineAmbientPrimitiveSamplingThreshold_bound (K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ base Q : ℝ, 0 ≤ base → 0 ≤ Q →
      (ambientL1SamplingBudget (affineAmbientPrimitiveBudget base Q) + K) ^ K ≤
        (base + Q + A) ^ A := by
  let poly : Polynomial ℕ :=
    (ambientL1SamplingBudget (affineAmbientPrimitiveBudget Polynomial.X 0) + Polynomial.C K) ^ K
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro base Q hbase hQ
  simpa [poly, ambientL1SamplingBudget, ambientL1FourierInput, affineAmbientPrimitiveBudget,
    affineAmbientMassLog, Polynomial.eval₂_pow] using hb (base + Q) (add_nonneg hbase hQ)

end Erdos3.VectorPolynomial

end

end OAI
