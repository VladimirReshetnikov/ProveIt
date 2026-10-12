import GowersSzemeredi.Proofs16IntegerPrintedStructure
import GowersSzemeredi.Proofs16DenseMultilinearBox

/-! Genuine integer-box Corollary 16.11 follows from the genuine global
structural theorem. The printed common exponent and stronger intermediate
width are retained over every prime modulus, including the even prime. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem Theorem162IntegerAt.restrict_function {l : Nat} (hth : Theorem162IntegerAt l)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ (B : Finset (Point N l)) (phi : Point N l → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N l), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
          let r := gamma ^ (-(2 : Int)) * multipleS theta gamma l
          IntegerMultiplyLinearWith
            (fun rho => (multipleQ (r⁻¹ * rho) gamma l) ^ r)
            (fun rho => (multipleC (r⁻¹ * rho) gamma l) ^ r) (partialGraph B' phi) := by
  intro N _ _ B phi hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hB : (B.card : Real) ≤ (N : Real) ^ l := by
    exact_mod_cast (show B.card ≤ N ^ l by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hcover⟩ := hth gamma theta hg hg1 ht ht1 N (partialGraph B phi) hgraph (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, ?_⟩
  · have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ l := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ l by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    linarith
  · rw [restrictRelation_partialGraph] at hcover
    exact hcover

theorem IntegerMultiplyLinearWith.dense_multilinear_box {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {delta : Real} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (B : Finset (Point N k)) (phi : Point N k → ZMod N)
    (hML : IntegerMultiplyLinearWith Qb Eb (partialGraph B phi))
    (P : Box N k) (hP : P.HasIntegerRepresentatives) (hPne : P.carrier.Nonempty)
    (hBsub : B ⊆ P.carrier) (hBmass : delta * P.carrier.card ≤ B.card) :
    ∃ Q : Box N k, ∃ C : Finset (Point N k), ∃ mu : Point N k → ZMod N,
      Q.IsAscendingInteger ∧ Q.carrier ⊆ P.carrier ∧
      (P.width : Real) ^ (Eb (delta / 2)) ≤ Q.width ∧
      C ⊆ B ∧ C ⊆ Q.carrier ∧
      (delta / 2) / (Qb (delta / 2)) * Q.carrier.card ≤ C.card ∧
      IsMultilinear mu ∧ ∀ x ∈ C, phi x = mu x := by
  classical
  obtain ⟨M, q, H, Q, mu, hHsub, hHmass, hpart, hproper, hqbound, hwidth, hmu, hcover⟩ :=
    hML (delta / 2) (by positivity) (by linarith) P hP
  have hBHmass : delta / 2 * P.carrier.card ≤ (B ∩ H).card := by
    have hu : (B ∪ H).card ≤ P.carrier.card :=
      Finset.card_le_card (Finset.union_subset hBsub hHsub)
    have hi := Finset.card_union_add_card_inter B H
    have hiR : ((B ∪ H).card : Real) + (B ∩ H).card = B.card + H.card := by exact_mod_cast hi
    have huR : ((B ∪ H).card : Real) ≤ P.carrier.card := by exact_mod_cast hu
    nlinarith only [hBmass, hHmass, hiR, huR]
  have hBHne : (B ∩ H).Nonempty := by
    apply Finset.card_pos.mp
    have hPc : (0 : Real) < P.carrier.card := by exact_mod_cast hPne.card_pos
    have hpos := (mul_pos (div_pos hdelta (by norm_num)) hPc).trans_le hBHmass
    exact_mod_cast hpos
  obtain ⟨x, hx⟩ := hBHne
  obtain ⟨j, hj⟩ := (hpart.1 x).mp (hBsub (Finset.mem_inter.mp hx).1)
  have hpoint : (x, phi x) ∈ partialGraph B phi :=
    Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩
  obtain ⟨i, _⟩ := hcover j x hj (Finset.mem_inter.mp hx).2 (phi x) hpoint
  have hq : 0 < q := Nat.zero_lt_of_lt i.isLt
  obtain ⟨j, hjmass⟩ := exists_coordinate_filter_cell (B ∩ H) P.carrier id
    (fun j ↦ (Q j).carrier) hPne hpart
    (fun x hx ↦ hBsub (Finset.mem_inter.mp hx).1) hBHmass
  let A := (B ∩ H).filter fun x ↦ x ∈ (Q j).carrier
  have hAcover : ∀ x ∈ A, ∃ i, phi x = mu j i x := by
    intro x hx
    obtain ⟨hxBH, hxQ⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxB, hxH⟩ := Finset.mem_inter.mp hxBH
    exact hcover j x hxQ hxH (phi x) (Finset.mem_image.mpr ⟨x, hxB, rfl⟩)
  obtain ⟨i, C, hCA, hmassC, hagree⟩ := finite_graph_cover_dense_piece hq A phi (mu j)
    hAcover hqbound (by positivity : 0 ≤ delta / 2) (Nat.cast_nonneg (Q j).carrier.card) hjmass
  refine ⟨Q j, C, mu j i, hproper j, hpart.cell_subset j, hwidth j, ?_, ?_, hmassC, hmu j i, hagree⟩
  · exact fun x hx ↦ (Finset.mem_inter.mp (Finset.mem_filter.mp (hCA hx)).1).1
  · exact fun x hx ↦ (Finset.mem_filter.mp (hCA hx)).2

theorem corollary_16_11_integer_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : Theorem162IntegerAt k) (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          P.HasIntegerRepresentatives ∧ IsMultilinear mu ∧
          (N : Real) ^ section16CorollaryWidthExponent alpha k ≤ P.width ∧
          section16CorollaryExponent alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  have hN0 := hth.restrict_function (alpha / 2) (alpha / 4)
    (by positivity) (by linarith) (by positivity) (by linarith)
  intro N _ _ f hf hnot
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  obtain ⟨C, hCB, hCmass, hML⟩ := hN0 N B phi hprod
  rw [section16_corollary_iteration_identity] at hML
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
  let r := section16CorollaryIteration alpha k
  let c := multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) k
  have hr : 0 < r := by
    dsimp [r, section16CorollaryIteration, multipleS]
    positivity
  have hc : 0 < c := by
    dsimp [c, multipleC]
    positivity
  have hdensity : (alpha / 8) /
      (multipleQ (r⁻¹ * (alpha / 8)) (alpha / 2) k) ^ r =
      section16CorollaryExponent alpha k := by
    change (alpha / 8) / (c⁻¹) ^ r = (alpha / 8) * c ^ r
    rw [Real.inv_rpow hc.le, div_inv_eq_mul]
  have hlarge : A.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hAP hy, ?_⟩
    rw [← hagree y hy]
    exact hfreq y (hCB (hAC hy))
  refine ⟨P, mu, hP.toGenuine, hmu, ?_, ?_⟩
  · simpa only [hRwidth, section16CorollaryWidthExponent] using hwidth
  · have hm : section16CorollaryExponent alpha k * P.carrier.card ≤ A.card := by
      simpa only [← hdensity] using hAmass
    exact hm.trans (Nat.cast_le.mpr hlarge)


def corollary_16_11_integer_representatives : Prop :=
  ∀ (k : Nat) (alpha : Real), 1 ≤ k → 0 < alpha → alpha ≤ 1 / 2 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          P.HasIntegerRepresentatives ∧ IsMultilinear mu ∧
          (N : Real) ^ section16CorollaryExponent alpha k ≤ P.width ∧
          section16CorollaryExponent alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha

theorem corollary_16_11_integer_representatives_holds : corollary_16_11_integer_representatives := by
  intro k alpha hk ha haHalf N _ _ f hf hnot
  obtain ⟨P, mu, hP, hmu, hwidth, hmass⟩ := corollary_16_11_integer_of_dimension_induction hk
    (theorem_16_2_integer_representatives_holds k) alpha ha haHalf N f hf hnot
  refine ⟨P, mu, hP, hmu, ?_, hmass⟩
  have hn : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hn
    (section16_corollary_common_exponent_lt_width ha haHalf k).le).trans hwidth

end LeanProofs.GowersSzemeredi
