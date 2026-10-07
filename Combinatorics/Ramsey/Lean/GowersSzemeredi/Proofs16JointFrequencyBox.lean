import GowersSzemeredi.Proofs16JointPowerStructure
import GowersSzemeredi.Proofs16PowerCoverDenseBox
import GowersSzemeredi.Proofs16CorollaryFromInduction

/-! Large multilinear Fourier frequencies from the joint power cover.
Only the preceding structural dimensions are used; the current-dimensional
source MultiplyLinear conclusion is unnecessary for this application. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16JointFrequencyExponent (alpha : Real) (k : Nat) : Real :=
  section16JointPowerExponent (alpha / 8) (alpha / 4) (alpha / 2) k

def section16JointFrequencyDensity (alpha : Real) (k : Nat) : Real :=
  (alpha / 8) / section16JointPowerGraphBudget (alpha / 8) (alpha / 4) (alpha / 2) k

theorem section16JointPowerGraphBudget_pos {rho theta gamma : Real} (k : Nat)
    (hr : 0 < rho) (ht : 0 < theta) (hg : 0 < gamma) :
    0 < section16JointPowerGraphBudget rho theta gamma k := by
  have hR : 0 < section16PowerPieceBudget theta gamma k := by
    apply Nat.ceil_pos.mpr
    unfold multipleS
    positivity
  have hRreal : (0 : Real) < section16PowerPieceBudget theta gamma k := by exact_mod_cast hR
  have heta := section16JointPowerLoss_pos (theta := theta) (gamma := gamma) k hr
  have hs := section16PowerSliceBudget_pos k ht hg
  have hsample := section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k
    (div_pos heta (by norm_num : (0 : Real) < 4))
  have hsampleReal : (0 : Real) < section16UniformSampleCount
      (section16JointPowerLoss rho theta gamma k / 4) theta gamma k := by exact_mod_cast hsample
  unfold section16JointPowerGraphBudget section16UniformLiftGraphBudget multipleQ multipleC
  dsimp only
  positivity

theorem section16JointFrequencyExponent_pos {k : Nat} (hk : 0 < k)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    0 < section16JointFrequencyExponent alpha k :=
  section16JointPowerExponent_pos hk (by positivity) (by positivity) (by linarith)
    (by positivity) (by linarith)

theorem section16JointFrequencyDensity_pos {alpha : Real} (ha : 0 < alpha) (k : Nat) :
    0 < section16JointFrequencyDensity alpha k :=
  div_pos (by positivity) (section16JointPowerGraphBudget_pos k
    (by positivity) (by positivity) (by positivity))

/-- The corollary's Fourier-box conclusion with the actual joint-cover
parameters, requiring structural induction only through dimension k. -/
theorem section16_joint_frequency_box {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
        ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
          P.IsProper ∧ IsMultilinear mu ∧
          (N : Real) ^ section16JointFrequencyExponent alpha k ≤ P.width ∧
          section16JointFrequencyDensity alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  obtain ⟨N0, hN0⟩ := section16_joint_power_structure_of_dimension_induction hk hth
    (alpha / 4) (alpha / 2) (by positivity) (by linarith) (by positivity) (by linarith)
  let T := section16JointPowerThreshold (alpha / 8) (alpha / 4) (alpha / 2) k
  refine ⟨max N0 ⌈T⌉₊, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  have hginv : 1 ≤ (alpha / 2) ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ (by positivity) (by linarith))
  have hB : (B.card : Real) ≤ (N : Real) ^ (k + 1) := by
    exact_mod_cast (show B.card ≤ N ^ (k + 1) by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤
      (alpha / 2) ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hprofile⟩ := hN0 N ((le_max_left _ _).trans hN)
    (partialGraph B phi) hgraph (partialGraph_relationProductProperty hprod)
  rw [restrictRelation_partialGraph] at hprofile
  let C := B ∩ J
  have hCdense : alpha / 4 * (N : Real) ^ (k + 1) ≤ C.card := by
    have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ (k + 1) := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ (k + 1) by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    dsimp only [C]
    linarith only [hBmass, hJ, hsum, hunion]
  let R : Box N (k + 1) := {
    axis := fun _ => modInterval N 0 N
    commonDiff := 1
    axis_step := fun _ => rfl }
  have hRcarrier : R.carrier = Finset.univ := by
    ext x
    simp [R, Box.carrier, modInterval_zero_modulus_carrier]
  have hRproper : R.IsProper := by
    intro i
    change (modInterval N 0 N).carrier.card = N
    rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]
  have hRwidth : R.width = N := by
    apply Nat.le_antisymm
    · exact R.width_le_axis_length ⟨0, by omega⟩
    · exact Box.le_width_of_le_axis R (by omega) (fun _ => le_rfl)
  have hRcard : (R.carrier.card : Real) = (N : Real) ^ (k + 1) := by
    rw [hRcarrier, Finset.card_univ]
    simp [Point, ZMod.card]
  have hML := hprofile (alpha / 8) (by positivity) (by linarith)
  have hhalf : alpha / 4 / 2 = alpha / 8 := by ring
  rw [← hhalf] at hML
  obtain ⟨P, A, mu, hP, _, hw, hAC, hAP, hAmass, hmu, hagree⟩ :=
    hML.dense_multilinear_box (by positivity : 0 < alpha / 4) C phi R hRproper
      (by rw [hRcarrier]; exact Finset.univ_nonempty)
      (by rw [hRwidth, hhalf]; exact (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right _ _).trans hN))
      (by rw [hRcarrier]; exact Finset.subset_univ _) (by rwa [hRcard])
  have hlarge : A.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hAP hy, ?_⟩
    rw [← hagree y hy]
    exact hfreq y (Finset.mem_inter.mp (hAC hy)).1
  refine ⟨P, mu, hP, hmu, ?_, ?_⟩
  · simpa only [hRwidth, hhalf, section16JointFrequencyExponent] using hw
  · apply le_trans ?_ (Nat.cast_le.mpr hlarge)
    simpa only [hhalf, section16JointFrequencyDensity] using hAmass

end LeanProofs.GowersSzemeredi
