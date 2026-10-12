import GowersSzemeredi.Proofs16IntegerPrintedCorollary
import GowersSzemeredi.Proofs16IntegerTightCovers

/-! Corollary 16.11 extracted directly from arbitrary polynomial covers,
retaining ascending integer boxes and the exact cover-dependent bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem IntegerPolyCoverAt.restrict_function {l : Nat} {Qb Eb : Real → Real → Real → Real}
    (hth : IntegerPolyCoverAt l Qb Eb)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ (B : Finset (Point N l)) (phi : Point N l → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N l), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
          IntegerMultiplyLinearWith (Qb gamma theta) (Eb gamma theta) (partialGraph B' phi) := by
  intro N _ _ B phi hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hB : (B.card : Real) ≤ (N : Real) ^ l := by
    exact_mod_cast (show B.card ≤ N ^ l by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hcover⟩ := hth N gamma theta hg hg1 ht ht1 (partialGraph B phi) hgraph (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, ?_⟩
  · have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ l := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ l by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    linarith
  · rw [restrictRelation_partialGraph] at hcover
    exact hcover

theorem corollary_16_11_integer_of_polyCover {k : Nat} (hk : 1 ≤ k)
    (Qb Eb : Real → Real → Real → Real) (hth : IntegerPolyCoverAt k Qb Eb) (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          P.IsAscendingInteger ∧ IsMultilinear mu ∧
          (N : Real) ^ (Eb (alpha / 2) (alpha / 4) (alpha / 8)) ≤ P.width ∧
          ((alpha / 8) / Qb (alpha / 2) (alpha / 4) (alpha / 8)) * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  have hN0 := hth.restrict_function (alpha / 2) (alpha / 4)
    (by positivity) (by linarith) (by positivity) (by linarith)
  intro N _ _ f hf hnot
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  obtain ⟨C, hCB, hCmass, hML⟩ := hN0 N B phi hprod
  let R : Box N k := {
    axis := fun _ ↦ modInterval N 0 N
    commonDiff := 1
    axis_step := fun _ ↦ rfl }
  have hRcarrier : R.carrier = Finset.univ := by
    ext x
    simp [R, Box.carrier, modInterval_zero_modulus_carrier]
  have hRinteger : R.IsAscendingInteger := by
    let A (_ : Fin k) : NatAP := ⟨0, 1, N⟩
    refine ⟨1, A, Nat.one_pos, by simp only [R, Nat.cast_one], fun i => ?_⟩
    refine ⟨NatAP.isProper_of_step_pos _ Nat.one_pos, rfl, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      simpa only [A, zero_add, mul_one] using Finset.mem_range.mpr j.isLt
    · simp only [A, R, NatAP.toModAP, modInterval, Nat.cast_zero, Nat.cast_one]
  have hRwidth : R.width = N := by
    apply Nat.le_antisymm
    · exact R.width_le_axis_length ⟨0, by omega⟩
    · exact Box.le_width_of_le_axis R (by omega) (fun _ ↦ le_rfl)
  have hRcard : (R.carrier.card : Real) = (N : Real) ^ k := by
    rw [hRcarrier, Finset.card_univ]
    simp [Point, ZMod.card]
  have hCdense : alpha / 4 * R.carrier.card ≤ C.card := by
    rw [hRcard]
    linarith only [hBmass, hCmass]
  obtain ⟨P, A, mu, hP, _, hwidth, hAC, hAP, hAmass, hmu, hagree⟩ :=
    hML.dense_multilinear_box (by positivity : 0 < alpha / 4) (by linarith)
      C phi R hRinteger.toGenuine (by rw [hRcarrier]; exact Finset.univ_nonempty)
      (by rw [hRcarrier]; exact Finset.subset_univ _) hCdense
  have hhalf : alpha / 4 / 2 = alpha / 8 := by ring
  rw [hhalf] at hwidth hAmass
  have hlarge : A.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hAP hy, ?_⟩
    rw [← hagree y hy]
    exact hfreq y (hCB (hAC hy))
  refine ⟨P, mu, hP, hmu, ?_, ?_⟩
  · simpa only [hRwidth] using hwidth
  · have hm : ((alpha / 8) / Qb (alpha / 2) (alpha / 4) (alpha / 8)) * P.carrier.card ≤ A.card := by
      exact hAmass
    exact hm.trans (Nat.cast_le.mpr hlarge)


end LeanProofs.GowersSzemeredi
