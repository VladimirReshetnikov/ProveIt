import OAI.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
import OAI.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds
import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel VectorPolynomial

private theorem twoTermErrorWidth_le_error {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) :
    twoTermErrorWidth B ε ≤ ε := by
  apply (min_le_right (1 : ℝ) (ε / (2 * (1 + B)))).trans
  exact div_le_self hε (by linarith)

private theorem spatialTupleTolerance_le_error (n : ℕ) {G V ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 ≤ ε) :
    spatialTupleTolerance n G V ε ≤ ε := by
  have ha : (1 : ℝ) ≤ 2 * (n + 1 : ℝ) := by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  have hb : (1 : ℝ) ≤ (2 + G) ^ n := one_le_pow₀ (by linarith)
  have hc : (1 : ℝ) ≤ 1 + V := by linarith
  have hab : (1 : ℝ) ≤ 2 * (n + 1 : ℝ) * (2 + G) ^ n := by
    simpa only [one_mul] using mul_le_mul ha hb (by norm_num) (zero_le_one.trans ha)
  have hden : (1 : ℝ) ≤ 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) := by
    simpa only [one_mul] using mul_le_mul hab hc (by norm_num) (zero_le_one.trans hab)
  exact (min_le_right _ _).trans (div_le_self hε hden)

theorem normalizedTupleNarrowWidth_le_exp (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (selection : Fin q ↪ G) (M : ℕ) (p E : ℝ) :
    normalizedTupleNarrowWidth X N selection M p E ≤ Real.exp (-E) := by
  have ht := (spatialTupleTolerance_spec (Fintype.card X)
    (Real.exp_nonneg (p ^ 3 + anisotropicSpatialCapLog p))
    (Real.exp_nonneg (coefficientErrorVolumeLog p + 4))
    (half_pos (Real.exp_pos (-(E + 2))))).1
  calc
    _ ≤ normalizedTupleTolerance X p E :=
      twoTermErrorWidth_le_error (smoothSpatialDisplacementCost_nonneg N selection M) ht.le
    _ ≤ normalizedSpatialShare E / 2 :=
      spatialTupleTolerance_le_error (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (by unfold normalizedSpatialShare; positivity)
    _ ≤ normalizedSpatialShare E := div_le_self (Real.exp_nonneg _) (by norm_num)
    _ ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)

theorem normalizedTupleNarrowWidth_mul_le_exp (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (selection : Fin q ↪ G) (M : ℕ)
    {p E F T C : ℝ} (hC : 0 ≤ C) (hCF : C ≤ Real.exp F) (hE : F + T ≤ E) :
    normalizedTupleNarrowWidth X N selection M p E * C ≤ Real.exp (-T) := by
  calc
    _ ≤ Real.exp (-E) * Real.exp F :=
      mul_le_mul (normalizedTupleNarrowWidth_le_exp X N selection M p E) hCF hC (Real.exp_nonneg _)
    _ = Real.exp (-E + F) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith only [hE])

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

noncomputable def allocatedJointForecastError
    (d a g q S : ℕ) (K C L A δ ξ : ℝ) : ℝ :=
  ((4 * (4 : ℝ) ^ d * (2 * K + 2 * ((d : ℝ) * A)) * δ + K * ξ) +
    2 * ((2 * C + K * L * 2) * ((a : ℝ) * ((q : ℝ) / S)) +
      K * L * (1 / S)) + 4 * a * ((q : ℝ) / S)) +
    2 * ((1 + 2 * (2 * C + K)) * ((g : ℝ) * ((q : ℝ) / S)))

theorem jointForecast_mesh_prefactor_bound
    {D P K C L : ℝ} {a g : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P)
    (ha : (a : ℝ) ≤ D) (hg : (g : ℝ) ≤ D)
    (hK : 0 ≤ K) (_hC : 0 ≤ C) (hL : 0 ≤ L)
    (hKP : K ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hLP : L ≤ Real.exp P) :
    2 * ((2 * C + 2 * K * L) * (a : ℝ) + K * L) + 4 * a +
      2 * (1 + 2 * (2 * C + K)) * g ≤ Real.exp (8 * (D + P + 8)) := by
  have hexp1 : 1 ≤ Real.exp P := Real.one_le_exp hP
  have he : 0 ≤ Real.exp P := Real.exp_nonneg _
  have hsq : Real.exp P ≤ (Real.exp P) ^ 2 := by nlinarith
  have hsq1 : 1 ≤ (Real.exp P) ^ 2 := hexp1.trans hsq
  have hpoly :
      2 * ((2 * C + 2 * K * L) * (a : ℝ) + K * L) + 4 * a +
        2 * (1 + 2 * (2 * C + K)) * g ≤
      2 * ((2 * Real.exp P + 2 * Real.exp P * Real.exp P) * D + Real.exp P * Real.exp P) +
        4 * D + 2 * (1 + 2 * (2 * Real.exp P + Real.exp P)) * D := by
    gcongr
  have hpolysimple :
      2 * ((2 * Real.exp P + 2 * Real.exp P * Real.exp P) * D + Real.exp P * Real.exp P) +
        4 * D + 2 * (1 + 2 * (2 * Real.exp P + Real.exp P)) * D ≤
      32 * (D + 1) * (Real.exp P) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hD,
      mul_le_mul_of_nonneg_left hsq1 hD]
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  calc
    _ ≤ 32 * (D + 1) * (Real.exp P) ^ 2 := hpoly.trans hpolysimple
    _ ≤ Real.exp 32 * Real.exp D * (Real.exp P) ^ 2 := by
      gcongr
      exact Real.add_one_le_exp D
    _ = Real.exp (32 + D + 2 * P) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem jointForecast_spatial_prefactor_bound
    {D P K A : ℝ} {d : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hd : (d : ℝ) ≤ D)
    (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hKP : K ≤ Real.exp P) (hAP : A ≤ Real.exp P) :
    4 * (4 : ℝ) ^ d * (2 * K + 2 * ((d : ℝ) * A)) ≤
        Real.exp (8 * (D + P + 8)) ∧
      (4 : ℝ) ^ d * ((d : ℝ) * A) ≤ Real.exp (8 * (D + P + 8)) := by
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    linarith only [h]
  have hpow : (4 : ℝ) ^ d ≤ Real.exp (2 * D) := by
    calc
      _ ≤ (Real.exp 2) ^ d := by gcongr
      _ = Real.exp ((d : ℝ) * 2) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hd])
  have hdexp : (d : ℝ) ≤ Real.exp D := hd.trans (by linarith only [Real.add_one_le_exp D])
  have hdA : (d : ℝ) * A ≤ Real.exp (D + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hdexp hAP hA (Real.exp_nonneg _)
  have hKDP : K ≤ Real.exp (D + P) :=
    hKP.trans (Real.exp_le_exp.mpr (by linarith only [hD]))
  have hsum : 2 * K + 2 * ((d : ℝ) * A) ≤ 4 * Real.exp (D + P) := by
    linarith only [hKDP, hdA]
  constructor
  · calc
      _ ≤ 4 * Real.exp (2 * D) * (4 * Real.exp (D + P)) := by gcongr
      _ ≤ Real.exp 2 * Real.exp (2 * D) * (Real.exp 2 * Real.exp (D + P)) := by gcongr
      _ = Real.exp (2 + 2 * D + (2 + (D + P))) := by
        simp only [Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hD, hP])
  · calc
      _ ≤ Real.exp (2 * D) * Real.exp (D + P) := by gcongr
      _ = Real.exp (2 * D + (D + P)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hD, hP])

private theorem jointForecast_log_ge_parameter {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    P ≤ 8 * (D + P + 8) := by linarith only [hD, hP]

private theorem jointForecast_scaled_small {B E z : ℝ}
    (hz : z ≤ Real.exp (-(B + E + 4))) :
    Real.exp B * z ≤ Real.exp (-(E + 4)) := by
  calc
    _ ≤ Real.exp B * Real.exp (-(B + E + 4)) :=
      mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem jointForecast_small_half {E : ℝ} (hE : 0 ≤ E) :
    Real.exp (-(E + 4)) ≤ 1 / 2 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith only [hE, Real.add_one_le_exp (E + 4)]

theorem allocatedJointForecastError_le_prefactor
    {D P K C L A δ ξ : ℝ} {d a g q S : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hd : (d : ℝ) ≤ D) (ha : (a : ℝ) ≤ D) (hg : (g : ℝ) ≤ D)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hKP : K ≤ Real.exp P) (hCP : C ≤ Real.exp P)
    (hLP : L ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hq : 0 < q) (_hS : 0 < S) (hδ : 0 ≤ δ) (hξ : 0 ≤ ξ) :
    allocatedJointForecastError d a g q S K C L A δ ξ ≤
      Real.exp (8 * (D + P + 8)) * δ + Real.exp (8 * (D + P + 8)) * ξ +
        Real.exp (8 * (D + P + 8)) * ((q : ℝ) / S) := by
  have hspatial := (jointForecast_spatial_prefactor_bound hD hP hd hK hA hKP hAP).1
  have hmesh := jointForecast_mesh_prefactor_bound hD hP ha hg hK hC hL hKP hCP hLP
  have hKbig := hKP.trans (Real.exp_le_exp.mpr (jointForecast_log_ge_parameter hD hP))
  have hratio : (1 : ℝ) / S ≤ (q : ℝ) / S := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hq
  have hKL := mul_le_mul_of_nonneg_left hratio (mul_nonneg hK hL)
  have hraw : allocatedJointForecastError d a g q S K C L A δ ξ ≤
      (4 * (4 : ℝ) ^ d * (2 * K + 2 * ((d : ℝ) * A))) * δ + K * ξ +
        (2 * ((2 * C + 2 * K * L) * (a : ℝ) + K * L) + 4 * a +
          2 * (1 + 2 * (2 * C + K)) * g) * ((q : ℝ) / S) := by
    unfold allocatedJointForecastError
    nlinarith only [hKL]
  exact hraw.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_right hspatial hδ)
      (mul_le_mul_of_nonneg_right hKbig hξ))
    (mul_le_mul_of_nonneg_right hmesh (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))

theorem allocatedJointForecastError_absorb
    {D P E K C L A δ ξ : ℝ} {d a g q S : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hd : (d : ℝ) ≤ D) (ha : (a : ℝ) ≤ D) (hg : (g : ℝ) ≤ D)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hKP : K ≤ Real.exp P) (hCP : C ≤ Real.exp P)
    (hLP : L ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hq : 0 < q) (hS : 0 < S) (hδ : 0 ≤ δ) (hξ : 0 ≤ ξ)
    (hδsmall : δ ≤ Real.exp (-(8 * (D + P + 8) + E + 4)))
    (hξsmall : ξ ≤ Real.exp (-(8 * (D + P + 8) + E + 4)))
    (hfloor : Real.exp (8 * (D + P + 8)) * ((q : ℝ) / S) ≤ Real.exp (-(E + 4))) :
    allocatedJointForecastError d a g q S K C L A δ ξ ≤ Real.exp (-E) ∧
      δ ≤ 1 ∧ (4 : ℝ) ^ d * ((d : ℝ) * A) * δ ≤ 1 / 2 := by
  have hfirst := allocatedJointForecastError_le_prefactor hD hP hd ha hg hK hC hL hA
    hKP hCP hLP hAP hq hS hδ hξ
  have hδbound := jointForecast_scaled_small hδsmall
  have hξbound := jointForecast_scaled_small hξsmall
  have htotal : allocatedJointForecastError d a g q S K C L A δ ξ ≤
      3 * Real.exp (-(E + 4)) := by linarith only [hfirst, hδbound, hξbound, hfloor]
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  refine ⟨htotal.trans ?_, hδsmall.trans ?_, ?_⟩
  · calc
      _ ≤ Real.exp 4 * Real.exp (-(E + 4)) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
      _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring
  · exact Real.exp_le_one_iff.mpr (by linarith only [hD, hP, hE])
  · exact (mul_le_mul_of_nonneg_right
      (jointForecast_spatial_prefactor_bound hD hP hd hK hA hKP hAP).2 hδ).trans
        (hδbound.trans (jointForecast_small_half hE))

theorem exists_allocatedJointForecastErrorBudget
    {D P V E : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let B := 8 * (D + P + 8)
    let δ := Real.exp (-(B + E + 4))
    ∃ Lmin : ℕ, 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (B + V + E + 6) ∧
      ∀ {d a g q S : ℕ} {K C L A : ℝ},
      (d : ℝ) ≤ D → (a : ℝ) ≤ D → (g : ℝ) ≤ D →
      0 ≤ K → 0 ≤ C → 0 ≤ L → 0 ≤ A →
      K ≤ Real.exp P → C ≤ Real.exp P → L ≤ Real.exp P → A ≤ Real.exp P →
      0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S →
      ∀ {G N X : Type*} [Fintype G] [Fintype N] [Fintype X]
        {r M : ℕ} (selection : Fin r ↪ G) {p lateTarget : ℝ},
      B + E + 4 ≤ lateTarget →
      let ξ := normalizedTupleNarrowWidth X N selection M p lateTarget
      0 < δ ∧ δ ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      2 ≤ S ∧ q ≤ S ∧ C * ((q : ℝ) / S) < 1 ∧
      (4 : ℝ) ^ d * ((d : ℝ) * A) * δ ≤ 1 / 2 ∧
      allocatedJointForecastError d a g q S K C L A δ ξ ≤ Real.exp (-E) := by
  intro B δ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨Lmin, hL, hLbound, hfloor⟩ := exists_forecast_mesh_floor hB hV
    (show 0 ≤ E + 4 by linarith only [hE])
  refine ⟨Lmin, hL, ?_, ?_⟩
  · convert hLbound using 1
    congr 1
    ring
  intro d a g q S K C L A hd ha hg hK hC hLip hA hKP hCP hLP hAP hq hqV hLS
    G N X _ _ _ r M selection p lateTarget hlate ξ
  have hS : 0 < S := hL.trans_le hLS
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hratio : 0 ≤ (q : ℝ) / S := div_nonneg (Nat.cast_nonneg _) hSr.le
  have hmesh := hfloor (Real.exp_nonneg B) (le_refl (Real.exp B)) hqV hLS
  have hδ0 : 0 < δ := Real.exp_pos _
  have hξ0 : 0 < ξ := normalizedTupleNarrowWidth_pos X N selection M p lateTarget
  have hξsmall : ξ ≤ Real.exp (-(B + E + 4)) :=
    (normalizedTupleNarrowWidth_le_exp X N selection M p lateTarget).trans
      (Real.exp_le_exp.mpr (neg_le_neg hlate))
  obtain ⟨herror, hδone, hmass⟩ := allocatedJointForecastError_absorb hD hP hE
    hd ha hg hK hC hLip hA hKP hCP hLP hAP hq hS hδ0.le hξ0.le
    (le_refl δ) hξsmall hmesh
  have hsmall : Real.exp (-(E + 4)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith only [hE])
  have hratioSmall : (q : ℝ) / S < 1 :=
    (le_mul_of_one_le_left hratio (Real.one_le_exp hB)).trans_lt (hmesh.trans_lt hsmall)
  have hqS : q < S := Nat.cast_lt.mp ((div_lt_one hSr).mp hratioSmall)
  have hCmesh : C * ((q : ℝ) / S) < 1 :=
    (mul_le_mul_of_nonneg_right
      (hCP.trans (Real.exp_le_exp.mpr (jointForecast_log_ge_parameter hD hP))) hratio).trans_lt
        (hmesh.trans_lt hsmall)
  refine ⟨hδ0, hδone, hξ0, hξsmall.trans ?_, by omega, hqS.le, hCmesh, hmass, herror⟩
  exact Real.exp_le_one_iff.mpr (by linarith only [hB, hE])

theorem allocatedJointForecast_mesh_of_exp_size
    {G J X : Type*} {P W τ ξ H : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N modulus : X → ℕ) (hmodulus : ∀ i, (modulus i : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (spatialSamplingBudget (2 * P) + P + H) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, (modulus z.2 : ℝ) /
      narrowTrimmedSpatialWidths W τ ξ N z ≤ Real.exp (-H) := by
  have hN (i : X) : 0 < N i :=
    Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize i))
  obtain ⟨hβ, hβinv, hwidth⟩ :=
    narrow_sampler_width_bounds (G := G) (J := J) hP hW hWP hτ hτP hξ hξ1 hξP N hN
  intro z
  have hNr : (0 : ℝ) < N z.2 := Nat.cast_pos.mpr (hN z.2)
  have hnum : (modulus z.2 : ℝ) * (spatialWidthFraction (2 * P) (ξ * τ))⁻¹ ≤
      Real.exp (P + spatialSamplingBudget (2 * P)) := by
    rw [Real.exp_add]
    exact mul_le_mul (hmodulus z.2) (by simpa only [one_div] using hβinv)
      (inv_nonneg.mpr hβ.le) (Real.exp_nonneg _)
  have hden : Real.exp (P + spatialSamplingBudget (2 * P)) ≤
      Real.exp (-H) * (N z.2 : ℝ) := by
    calc
      _ = Real.exp (-H) * Real.exp (spatialSamplingBudget (2 * P) + P + H) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsize z.2) (Real.exp_nonneg _)
  calc
    _ ≤ (modulus z.2 : ℝ) /
        (spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hβ hNr) (hwidth z)
    _ = ((modulus z.2 : ℝ) * (spatialWidthFraction (2 * P) (ξ * τ))⁻¹) / (N z.2 : ℝ) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := (div_le_iff₀ hNr).mpr (hnum.trans hden)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedPathForecastError
    (a g q S : ℕ) (K C L η ξ : ℝ) : ℝ :=
  ((a : ℝ) * ((q : ℝ) / S) +
    (2 * ((2 * C + K * L * 2) * ((a : ℝ) * ((q : ℝ) / S)) +
      K * L * (1 / S)) + 2 * η)) +
    (1 + 2 * (2 * C + K)) * ((g : ℝ) * ((q : ℝ) / S)) + K * ξ

theorem fixedPathForecastError_eq_joint
    {Input G : Type*} [Fintype Input] [Fintype G]
    (q S : ℕ) (K C L η ξ : ℝ) :
    fixedPathForecastError (Fintype.card Input) (Fintype.card G) q S K C L η ξ =
      (((Fintype.card Input : ℝ) * ((q : ℝ) / S) +
        (2 * ((2 * C + K * L * 2) * (∑ _ : Input, (q : ℝ) / S) +
          K * L * (1 / S)) + 2 * η)) +
      (1 + 2 * (2 * C + K)) * ((Fintype.card G : ℝ) * ((q : ℝ) / S))) + K * ξ := by
  simp only [fixedPathForecastError, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem fixedPathForecastError_le_prefactor
    {D P K C H L η ξ : ℝ} {a g q S : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (ha : (a : ℝ) ≤ D) (hg : (g : ℝ) ≤ D)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (_hH : 0 ≤ H) (hL : 0 ≤ L) (hLH : L ≤ 2 * H)
    (hKP : K ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hHP : H ≤ Real.exp P)
    (hq : 0 < q) (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    fixedPathForecastError a g q S K C L η ξ ≤
      Real.exp (8 * (D + P + 9)) * ((q : ℝ) / S) +
      Real.exp (8 * (D + P + 9)) * η + Real.exp (8 * (D + P + 9)) * ξ := by
  have hexp : Real.exp P ≤ Real.exp (P + 1) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hLP : L ≤ Real.exp (P + 1) := by
    rw [Real.exp_add]
    exact hLH.trans ((mul_le_mul_of_nonneg_left hHP (by norm_num)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg P)]))
  have hmesh := jointForecast_mesh_prefactor_bound hD (show 0 ≤ P + 1 by linarith)
    ha hg hK hC hL (hKP.trans hexp) (hCP.trans hexp) hLP
  have hmesh' :
      (a : ℝ) + 2 * ((2 * C + 2 * K * L) * a + K * L) +
        (1 + 2 * (2 * C + K)) * g ≤ Real.exp (8 * (D + P + 9)) := by
    have hnon : 0 ≤ (1 + 2 * (2 * C + K)) * g := by positivity
    have he : 8 * (D + (P + 1) + 8) = 8 * (D + P + 9) := by ring
    rw [he] at hmesh
    exact (show (a : ℝ) + 2 * ((2 * C + 2 * K * L) * a + K * L) +
        (1 + 2 * (2 * C + K)) * g ≤
        2 * ((2 * C + 2 * K * L) * a + K * L) + 4 * a +
          2 * (1 + 2 * (2 * C + K)) * g by
        nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]).trans hmesh
  have hratio : (1 : ℝ) / S ≤ (q : ℝ) / S :=
    div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg _)
  have hKL := mul_le_mul_of_nonneg_left hratio (mul_nonneg hK hL)
  have hraw : fixedPathForecastError a g q S K C L η ξ ≤
      ((a : ℝ) + 2 * ((2 * C + 2 * K * L) * a + K * L) +
        (1 + 2 * (2 * C + K)) * g) * ((q : ℝ) / S) + 2 * η + K * ξ := by
    unfold fixedPathForecastError
    nlinarith only [hKL]
  have hPbig : P ≤ 8 * (D + P + 9) := by linarith
  have hKbig := hKP.trans (Real.exp_le_exp.mpr hPbig)
  have htwobig : (2 : ℝ) ≤ Real.exp (8 * (D + P + 9)) :=
    htwo.trans (Real.exp_le_exp.mpr (by linarith))
  exact hraw.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_right hmesh' (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_right htwobig hη))
    (mul_le_mul_of_nonneg_right hKbig hξ))

private theorem fixedPath_scaled_small {B E z : ℝ}
    (hz : z ≤ Real.exp (-(B + E + 4))) :
    Real.exp B * z ≤ Real.exp (-(E + 4)) := by
  calc
    _ ≤ Real.exp B * Real.exp (-(B + E + 4)) :=
      mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fixedPathForecastError_absorb
    {D P E K C H L η ξ : ℝ} {a g q S : ℕ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (ha : (a : ℝ) ≤ D) (hg : (g : ℝ) ≤ D)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L) (hLH : L ≤ 2 * H)
    (hKP : K ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hHP : H ≤ Real.exp P)
    (hq : 0 < q) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hηsmall : η ≤ Real.exp (-(8 * (D + P + 9) + E + 4)))
    (hξsmall : ξ ≤ Real.exp (-(8 * (D + P + 9) + E + 4)))
    (hfloor : Real.exp (8 * (D + P + 9)) * ((q : ℝ) / S) ≤ Real.exp (-(E + 4))) :
    fixedPathForecastError a g q S K C L η ξ ≤ Real.exp (-E) := by
  have hpre := fixedPathForecastError_le_prefactor (S := S) hD hP ha hg hK hC hH hL hLH
    hKP hCP hHP hq hη hξ
  have hηb := fixedPath_scaled_small hηsmall
  have hξb := fixedPath_scaled_small hξsmall
  have htotal : fixedPathForecastError a g q S K C L η ξ ≤ 3 * Real.exp (-(E + 4)) := by
    linarith only [hpre, hηb, hξb, hfloor]
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  refine htotal.trans ?_
  calc
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_fixedPathForecastErrorBudget
    {D P V E : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let B := 8 * (D + P + 9)
    let η := Real.exp (-(B + E + 4))
    ∃ Lmin : ℕ, 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (B + V + E + 6) ∧
      ∀ {a g q S : ℕ} {K C H L : ℝ},
      (a : ℝ) ≤ D → (g : ℝ) ≤ D →
      0 ≤ K → 0 ≤ C → 0 ≤ H → 0 ≤ L → L ≤ 2 * H →
      K ≤ Real.exp P → C ≤ Real.exp P → H ≤ Real.exp P →
      0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S →
      ∀ {G N X : Type*} [Fintype G] [Fintype N] [Fintype X]
        {r M : ℕ} (selection : Fin r ↪ G) {p lateTarget : ℝ},
      B + E + 4 ≤ lateTarget →
      let ξ := normalizedTupleNarrowWidth X N selection M p lateTarget
      0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      2 ≤ S ∧ q ≤ S ∧ C * ((q : ℝ) / S) < 1 ∧
      fixedPathForecastError a g q S K C L η ξ ≤ Real.exp (-E) := by
  intro B η
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨Lmin, hLmin, hLbound, hfloor⟩ := exists_forecast_mesh_floor hB hV
    (show 0 ≤ E + 4 by linarith only [hE])
  refine ⟨Lmin, hLmin, ?_, ?_⟩
  · convert hLbound using 1
    congr 1
    ring
  intro a g q S K C H L ha hg hK hC hH hL hLH hKP hCP hHP hq hqV hLS
    G N X _ _ _ r M selection p lateTarget hlate ξ
  have hS : 0 < S := hLmin.trans_le hLS
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hratio : 0 ≤ (q : ℝ) / S := div_nonneg (Nat.cast_nonneg _) hSr.le
  have hmesh := hfloor (Real.exp_nonneg B) (le_refl (Real.exp B)) hqV hLS
  have hη0 : 0 < η := Real.exp_pos _
  have hξ0 : 0 < ξ := normalizedTupleNarrowWidth_pos X N selection M p lateTarget
  have hξsmall : ξ ≤ Real.exp (-(B + E + 4)) :=
    (normalizedTupleNarrowWidth_le_exp X N selection M p lateTarget).trans
      (Real.exp_le_exp.mpr (neg_le_neg hlate))
  have herror := fixedPathForecastError_absorb hD hP ha hg hK hC hH hL hLH
    hKP hCP hHP hq hη0.le hξ0.le (le_refl η) hξsmall hmesh
  have hsmall : Real.exp (-(E + 4)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith only [hE])
  have hratioSmall : (q : ℝ) / S < 1 :=
    (le_mul_of_one_le_left hratio (Real.one_le_exp hB)).trans_lt (hmesh.trans_lt hsmall)
  have hqS : q < S := Nat.cast_lt.mp ((div_lt_one hSr).mp hratioSmall)
  have hPbig : P ≤ B := by dsimp only [B]; linarith only [hD, hP]
  have hCmesh : C * ((q : ℝ) / S) < 1 :=
    (mul_le_mul_of_nonneg_right
      (hCP.trans (Real.exp_le_exp.mpr hPbig)) hratio).trans_lt (hmesh.trans_lt hsmall)
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hB, hE])
  exact ⟨hη0, hηone, hξ0, hξsmall.trans hηone, by omega, hqS.le, hCmesh, herror⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_normalizedTupleForecastWidth_budget :
    ∃ A : ℕ, 2 ≤ A ∧
    ∀ {G N X : Type*} [Fintype G] [Fintype N] [Fintype X]
      {q M : ℕ} (selection : Fin q ↪ G) {p E : ℝ},
      0 ≤ p → 0 ≤ E → (M : ℝ) ≤ Real.exp p →
      ((q + 1 : ℕ) : ℝ) ≤ p → (Fintype.card G : ℝ) ≤ p →
      (Fintype.card N : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      let ξ := normalizedTupleNarrowWidth X N selection M p E
      0 < ξ ∧ ξ ≤ Real.exp (-E) ∧ ξ⁻¹ ≤ Real.exp ((p + E + A) ^ A) := by
  obtain ⟨A, hA, hbound⟩ := exists_spatialParameterBudget_bound
  refine ⟨A, hA, ?_⟩
  intro G N X _ _ _ q M selection p E hp hE hM hq hG hN hX ξ
  have hwidth := (normalizedTupleEarlyParameters_bound selection hp hE (le_refl 0)
    hM hq hG hN hX).2
  have hprimitive := (spatialParameterBudget_bounds hp hE (le_refl 0)).2.1
  have hpoly := hbound hp hE (le_refl 0)
  have hlog : 2 * (spatialPrimitiveEnvelope p E 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope p E 0)) + 4 ≤ (p + E + A) ^ A := by
    simpa only [add_zero] using hprimitive.trans hpoly
  exact ⟨normalizedTupleNarrowWidth_pos X N selection M p E,
    normalizedTupleNarrowWidth_le_exp X N selection M p E,
    hwidth.trans (Real.exp_le_exp.mpr hlog)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem fixedPath_scalarCubeBoundary_empty : scalarCubeGridBoundaryConstant Empty = 4 := by
  norm_num [scalarCubeGridBoundaryConstant]

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}

theorem exists_allocatedFixedPathForecastErrorBudget
    {D P V E : ℝ} (hD : 0 ≤ D) (hP : 2 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hG : (Fintype.card G : ℝ) ≤ D)
    (hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ P) :
    let early := 8 * (D + P + 9)
    let η := Real.exp (-(early + E + 4))
    ∃ Lmin : ℕ, 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (early + V + E + 6) ∧
      ∀ (S : LayerSamplerScale (G := G) B U basis R σ) {t : ℝ},
      0 ≤ t → t ≤ 1 → ∀ (Kφ : ℝ≥0), (Kφ : ℝ) ≤ Real.exp P →
      ∀ {q : ℕ}, 0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S.value →
      ∀ {G' N X : Type*} [Fintype G'] [Fintype N] [Fintype X]
        {r M : ℕ} (selection : Fin r ↪ G') {p lateTarget : ℝ},
      early + E + 4 ≤ lateTarget →
      let ξ := normalizedTupleNarrowWidth X N selection M p lateTarget
      0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      2 ≤ S.value ∧ q ≤ S.value ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1 ∧
      fixedPathForecastError
        (Fintype.card (PrincipalTupleIndex
          (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val)))
        (Fintype.card G) q S.value Kφ (scalarCubeGridBoundaryConstant Empty)
        (allocatedOriginalSampleFullSliceLip B U basis S t) η ξ ≤ Real.exp (-E) := by
  intro early η
  have hP0 : 0 ≤ P := by linarith
  obtain ⟨Lmin, hL, hLbound, hbudget⟩ := exists_fixedPathForecastErrorBudget hD hP0 hV hE
  refine ⟨Lmin, hL, hLbound, ?_⟩
  intro S t ht0 ht1 Kφ hK q hq hqV hLS G' N X _ _ _ r M selection p lateTarget hlate ξ
  have ha : (Fintype.card (PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ D := by
    apply le_trans _ hInput
    exact_mod_cast allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S
  have hC0 : 0 ≤ scalarCubeGridBoundaryConstant Empty := by
    rw [fixedPath_scalarCubeBoundary_empty]
    norm_num
  have hCP : scalarCubeGridBoundaryConstant Empty ≤ Real.exp P := by
    rw [fixedPath_scalarCubeBoundary_empty]
    have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h2
    exact (by linarith : (4 : ℝ) ≤ Real.exp 2).trans (Real.exp_le_exp.mpr hP)
  exact hbudget (G := G') (N := N) (X := X) (M := M) (p := p) ha hG Kφ.coe_nonneg hC0
    (allocatedOriginalSampleLiftLip B U basis S).coe_nonneg
    (allocatedOriginalSampleFullSliceLip B U basis S t).coe_nonneg
    (allocatedOriginalSampleFullSliceLip_coe_le_two B U basis S ht0 ht1)
    hK hCP (allocatedOriginalSampleLiftLip_le_exp_of_allAxis B U basis S hLift)
    hq hqV hLS selection hlate

end VectorPolynomial
end Erdos3

end

end OAI
