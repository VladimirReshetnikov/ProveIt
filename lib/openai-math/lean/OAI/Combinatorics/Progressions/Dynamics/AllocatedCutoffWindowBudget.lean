import OAI.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem allocatedCutoffSamplingLog_window_bounds (m dim : ℕ) {P c E S : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hE : 0 ≤ E) (hS : 0 ≤ S) :
    let Q := allocatedCutoffSamplingLog m dim P c E S
    2 ≤ Q ∧ 2 * P + 2 ≤ Q ∧ S ≤ Q := by
  let L := allocatedCutoffFourierLog m dim P c E
  have ha := (allocatedCutoffLipschitzLog_bounds m dim hP hc).1
  have hterm : 0 ≤ 2 * c * (m : ℝ) ^ 3 * ((2 : ℝ) ^ dim) ^ 2 * P ^ 2 := by positivity
  have hdim : 0 ≤ (m * (2 : ℝ) ^ dim) * P := by positivity
  have hL : 2 * P + 1 ≤ L := by
    dsimp only [L, allocatedCutoffFourierLog, allocatedCutoffLipschitzLog]
    linarith only [ha, hterm, hdim, hE]
  have hL0 : 0 ≤ L := by linarith
  have hpow : 1 ≤ (2 * L + 2) ^ 4 := one_le_pow₀ (by linarith)
  have hprod : 0 ≤ 2 * L * (2 * L + 2) ^ 4 := by positivity
  have hsource : 2 * P + 2 ≤ allocatedCutoffSamplingLog m dim P c E S := by
    change 2 * P + 2 ≤ S + 2 * L * (2 * L + 2) ^ 4 + L + (2 * L + 2) ^ 4
    linarith only [hS, hL, hpow, hprod]
  exact ⟨by linarith, hsource, (allocatedCutoffSamplingLog_bounds m dim hP hc hE hS).2.1⟩

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S C V Psrc)

include hnum in
theorem allocatedCutoffSampling_physical_window {X : Type*} (N q : X → ℕ)
    {K : ℕ} (hK : 2 ≤ K) (hElog : 0 ≤ Elog) (hP : 0 ≤ P)
    {τ : ℝ} (hτ : 0 < τ) (hτP : 1 / τ ≤ Real.exp P)
    (hq : ∀ z, 0 < q z) (hqP : ∀ z, (q z : ℝ) ≤ Real.exp P)
    (hsize : ∀ z, Real.exp ((allocatedCutoffSamplingLog m dim Psrc
      (normalizedSiteCutoffBound : ℝ) Elog P + K) ^ K) ≤ (N z : ℝ)) :
    ∀ z, 0 < N z ∧
      Fintype.card (Option (LayerSamplerVariables G I n B)) *
          allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ trimmedSpatialRootScale τ N q z ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale τ N q z := by
  let Q := allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
  obtain ⟨hQ2, hsourceQ, hPQ⟩ := allocatedCutoffSamplingLog_window_bounds m dim
    hnum.nonneg normalizedSiteCutoffBound.coe_nonneg hElog hP
  have hPsrcQ : Psrc ≤ Q := by
    change 2 * Psrc + 2 ≤ Q at hsourceQ
    linarith [hnum.nonneg]
  have hcount : (Fintype.card (Option (LayerSamplerVariables G I n B)) : ℝ) ≤ Real.exp Psrc := by
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    linarith [hnum.variable_count, Real.add_one_le_exp Psrc]
  have hentry := allocatedPhysicalEntryBudget_le_exp B U b S (fun _ => 0)
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) hnum.nonneg le_rfl hnum.root hnum.length
  have hentry0 : 0 ≤ allocatedPhysicalEntryBudget B U b S (fun _ => 0) :=
    zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  intro z
  have hroot := trimmedSpatialRootScale_ge_exp N q hQ2 hK hτ
    (hτP.trans (Real.exp_le_exp.mpr hPQ)) hq
    (fun t => (hqP t).trans (Real.exp_le_exp.mpr hPQ)) hsize z
  have hN : 0 < N z := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize z))
  have hrows : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ trimmedSpatialRootScale τ N q z := by
    calc
      _ ≤ Real.exp Psrc * Real.exp (Psrc + 2) :=
        mul_le_mul hcount hentry hentry0 (Real.exp_pos _).le
      _ = Real.exp (2 * Psrc + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp Q := Real.exp_le_exp.mpr hsourceQ
      _ ≤ _ := hroot
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialRootScale τ N q z :=
    hnum.profile.trans ((Real.exp_le_exp.mpr hPsrcQ).trans hroot)
  exact ⟨hN, hrows, by linarith [(Real.exp_pos Q).trans_le hroot]⟩

end Erdos3.VectorPolynomial

end

end OAI
