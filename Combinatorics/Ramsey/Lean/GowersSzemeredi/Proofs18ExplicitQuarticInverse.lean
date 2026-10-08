import GowersSzemeredi.Proofs18JointInverseInduction
import GowersSzemeredi.Proofs16ExplicitDimensionTwo

/-! The degree-four inverse theorem with an explicit modulus threshold.

`function_inverse_of_lower_structural_dimensions 2` turns `Theorem162At 2`
into a degree-four function discrepancy bound, but its threshold is
existential because `Theorem162At` hides its own. This module repeats the
chain with `Theorem162AtBounded`:

* spectrum restriction and common base data,
* the Lemma 16.4 extraction,
* sharp power pieces and decomposition,
* the joint power structure and frequency box,
* polynomial localization and one inverse step.

Every threshold becomes a closed expression in the structural thresholds,
the Lemma 15.6 threshold and the already explicit box-width and
localization thresholds. With `theorem_16_2_at_two_bounded` this gives the
degree-four bound with threshold `quarticInverseThreshold alpha`
(`quartic_function_inverse_explicit`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The structural threshold at the spectrum parameters of Lemma 16.6. -/
def section16SpectrumThreshold (k : Nat) (T : Real → Real → Real) (theta gamma : Real) : Real :=
  T (section16Delta (section16ThetaOne theta gamma k)) (section16ThetaOne theta gamma k / 8)

theorem Theorem162AtBounded.restrict_spectrum {k : Nat} {T : Real → Real → Real}
    (hth : Theorem162AtBounded k T)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16SpectrumThreshold k T theta gamma ≤ (N : Real) →
      ∀ B : Finset (Point N (k + 1)), ∃ J : Finset (Point N k),
        (1 - section16ThetaOne theta gamma k / 8) * (N : Real) ^ k ≤ J.card ∧
        MultiplyLinear (section16Delta (section16ThetaOne theta gamma k))
          (section16T (section16Delta (section16ThetaOne theta gamma k))
            (section16ThetaOne theta gamma k) k)
          (restrictRelation (section16SpectrumRelation B
            (section16Delta (section16ThetaOne theta gamma k))) J) := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  intro N _ _ hN B
  exact hth _ _ hd hd1 (by positivity : 0 < section16ThetaOne theta gamma k / 8)
    (by linarith : section16ThetaOne theta gamma k / 8 ≤ 1) N hN _
    (section16_spectrum_relation_card B hd) (section16_spectrum_relation_product B hd)

theorem Theorem162AtBounded.common_base_data {k : Nat} {T : Real → Real → Real}
    (hth : Theorem162AtBounded k T)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16SpectrumThreshold k T theta gamma ≤ (N : Real) →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        Section16StructuredPair theta gamma B phi →
        Nonempty (Section16CommonBaseData theta gamma B phi) := by
  classical
  intro N _ _ hN B phi hB
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection (Fact.out : N.Prime) theta gamma B phi ht ht1 hg hg1 hB
  obtain ⟨J, hJ, hspectrum⟩ := hth.restrict_spectrum theta gamma ht ht1 hg hg1 N hN B
  have hmass : section16ThetaOne theta gamma k / 8 * (N : Real) ^ k ≤ (H ∩ J).card := by
    have hcard : ((H ∪ J).card : Real) + (H ∩ J).card = H.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter H J
    have hu : ((H ∪ J).card : Real) ≤ (N : Real) ^ k := by
      exact_mod_cast (show (H ∪ J).card ≤ N ^ k by
        simpa [Point, ZMod.card] using Finset.card_le_univ (H ∪ J))
    nlinarith only [hcard, hu, hH, hJ]
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_holds N k theta gamma B phi (H ∩ J) Y phiPrime
    hmass (fun h hh => hcube h (Finset.mem_inter.mp hh).1)
    (fun h hh => hselected h (Finset.mem_inter.mp hh).1)
    (hselection.mono Finset.inter_subset_left)
  exact ⟨{
    H := H, J := J, Y := Y, phiPrime := phiPrime, x0 := x0
    Hmass := hH, intersect_mass := hmass, cube_mass := hcube, selected_mass := hselected
    selection := hselection, spectrum := hspectrum, good_mass := hgood
    identity := section16_phi_one_identity_of_common_base B phi (H ∩ J) Y x0 phiPrime hidentity }⟩

/-- The explicit threshold of the Lemma 16.4 extraction in dimension `k+1`. -/
def section16ExtractionThreshold (k : Nat) (T : Nat → Real → Real → Real)
    (theta gamma : Real) : Real :=
  max (section16FaceThreshold (k + 1) T gamma ((2 : Real) ^ (-(k + 2 : Real)) * theta))
    (lemma156ExplicitThreshold k (theta / 2) gamma)

theorem lemma_16_4_extraction_bounded (k : Nat) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l)) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16ExtractionThreshold k T theta gamma ≤ (N : Real) →
      Odd N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        RelationProductProperty gamma Gamma →
        (∃ H : Finset (Point N (k + 1)), (H.card : Real) < theta * (N : Real) ^ (k + 1) ∧
          RelationSupportedOn Gamma H) ∨
        ∃ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
          GraphContained B phi Gamma ∧ Section16StructuredPair theta gamma B phi := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  intro N _ _ hN ho Gamma hrelation
  have hNmax : max (section16FaceThreshold (k + 1) T gamma ((2 : Real) ^ (-(k + 2 : Real)) * theta))
      (lemma156ExplicitThreshold k (theta / 2) gamma) ≤ (N : Real) := hN
  by_cases hsmall : ((relationProjection Gamma).card : Real) < theta * (N : Real) ^ (k + 1)
  · exact Or.inl ⟨relationProjection Gamma, hsmall, relationProjection_supported Gamma⟩
  · obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
    have hprod := hrelation (relationProjection Gamma) phi hgraph
    obtain ⟨C, hCB, hCcard, hCfaces⟩ :=
      restrict_proper_faces_common_parameter_bounded k T hth gamma theta hg hg1 ht ht1 N
        ((le_max_left _ _).trans hNmax) (relationProjection Gamma) phi (le_of_not_gt hsmall) hprod
    obtain ⟨B, hBC, hcount, hrespect⟩ :=
      lemma_15_6_of_density_lower_all_explicit k (theta / 2) gamma ht2 ht21 hg hg1 N
        ((le_max_right _ _).trans hNmax) (Fact.out : N.Prime) ho C phi hCcard (hprod.mono hCB)
    refine Or.inr ⟨B, phi, ?_, hCfaces.mono hBC, ?_, ?_⟩
    · intro x hx
      exact hgraph x (hCB (hBC hx))
    · have heq : theta / 2 * gamma / 2 = theta * gamma / 4 := by ring
      simpa only [section16ThetaOne, heq] using hcount
    · simpa only [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat,
        inv_pow] using hrespect

/-- The explicit threshold of the sharp power pieces in dimension `k+1`. -/
def section16SharpPieceThreshold (k : Nat) (T : Nat → Real → Real → Real)
    (theta gamma : Real) : Real :=
  max 3 (max (section16ExtractionThreshold k T theta gamma)
    (section16SpectrumThreshold k (T k) theta gamma))

theorem section16_sharp_power_piece_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16SharpPieceThreshold k T theta gamma ≤ (N : Real) →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N), RelationProductProperty gamma Gamma →
        theta * (N : Real) ^ (k + 1) ≤ (relationProjection Gamma).card →
        ∃ E ⊆ Gamma, section16ThetaTwo (section16ThetaOne theta gamma k) *
            (N : Real) ^ (k + 1) ≤ E.card ∧
          Section16PowerCoverProfile theta gamma k E := by
  intro N _ _ hN Gamma hprod hlarge
  have hNmax : max 3 (max (section16ExtractionThreshold k T theta gamma)
      (section16SpectrumThreshold k (T k) theta gamma)) ≤ (N : Real) := hN
  have hN3real : (3 : Real) ≤ N := (le_max_left _ _).trans hNmax
  have hN3 : 3 ≤ N := by exact_mod_cast hN3real
  have hNs : section16ExtractionThreshold k T theta gamma ≤ (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hNmax)
  have hNc : section16SpectrumThreshold k (T k) theta gamma ≤ (N : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hNmax)
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  rcases lemma_16_4_extraction_bounded k theta gamma ht ht1 hg hg1 T hth N hNs ho Gamma hprod with
    hsmall | ⟨B, phi, hgraph, hstructured⟩
  · obtain ⟨H, hH, hsupp⟩ := hsmall
    have hsub : relationProjection Gamma ⊆ H := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hsupp z hz
    have hp : ((relationProjection Gamma).card : Real) ≤ H.card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    linarith only [hlarge, hH, hp]
  · obtain ⟨D⟩ := (hth k hk le_rfl).common_base_data theta gamma ht ht1 hg hg1 N hNc
      B phi hstructured
    refine ⟨section16TranslatedGoodGraph B phi (D.H ∩ D.J) D.Y D.x0,
      section16TranslatedGoodGraph_subset Gamma B phi _ _ _ hgraph, ?_,
      (D.power_cover_profile hstructured hk ht ht1 hg hg1).translate (appendCoordinate D.x0 0)⟩
    rw [section16TranslatedGoodGraph_card]
    exact D.good_mass

theorem section16_sharp_power_decomposition_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16SharpPieceThreshold k T theta gamma ≤ (N : Real) →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N (k + 1) × ZMod N),
          ∃ J : Finset (Point N (k + 1)),
            (∀ i, G i ⊆ Gamma ∧ Section16PowerCoverProfile theta gamma k (G i)) ∧
            (q : Real) ≤ section16CommonBasePieceBound theta gamma k ∧
            (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  intro N _ _ hN Gamma hcard hprod
  have hd : 0 < section16ThetaTwo (section16ThetaOne theta gamma k) := by
    unfold section16ThetaTwo section16ThetaOne
    positivity
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let mass := section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1)
  have hmass : 0 < mass := by dsimp [mass]; positivity
  obtain ⟨q, G, J, hG, hq, hJ, hc⟩ := section16_greedy_relation_decomposition
    (Section16PowerCoverProfile theta gamma k) theta mass hmass Gamma
    (fun Delta hDelta hlarge => section16_sharp_power_piece_bounded hk T hth theta gamma
      ht ht1 hg hg1 N hN Delta (hprod.mono hDelta) hlarge)
  refine ⟨q, G, J, hG, ?_, hJ, hc⟩
  have hbudget : (q : Real) * mass ≤
      (section16CommonBasePieceBound theta gamma k) * mass := by
    calc
      _ ≤ (Gamma.card : Real) := hq
      _ ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := hcard
      _ = _ := by dsimp [mass, section16CommonBasePieceBound]; field_simp
  exact (mul_le_mul_iff_left₀ hmass).mp hbudget

theorem section16_joint_power_structure_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16SharpPieceThreshold k T theta gamma ≤ (N : Real) →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N (k + 1)),
          (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
          Section16JointPowerCoverProfile theta gamma k (restrictRelation Gamma J) := by
  intro N _ _ hN Gamma hcard hprod
  obtain ⟨q, G, J, hG, hq, hJ, hc⟩ :=
    section16_sharp_power_decomposition_bounded hk T hth theta gamma ht ht1 hg hg1 N hN
      Gamma hcard hprod
  have h := section16_joint_power_profile_of_pieces hk ht ht1 hg hg1 G (fun i => (hG i).2) hq
  exact ⟨J, hJ, fun rho hr hr1 => (h rho hr hr1).mono hc⟩

/-- The explicit threshold of the joint frequency box. -/
def section16JointFrequencyThreshold (k : Nat) (T : Nat → Real → Real → Real)
    (alpha : Real) : Real :=
  max (section16SharpPieceThreshold k T (alpha / 4) (alpha / 2))
    (section16JointPowerThreshold (alpha / 8) (alpha / 4) (alpha / 2) k)

theorem section16_joint_frequency_box_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16JointFrequencyThreshold k T alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
        ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
          P.IsProper ∧ IsMultilinear mu ∧
          (N : Real) ^ section16JointFrequencyExponent alpha k ≤ P.width ∧
          section16JointFrequencyDensity alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  intro N _ _ hN f hf hnot
  have hNmax : max (section16SharpPieceThreshold k T (alpha / 4) (alpha / 2))
      (section16JointPowerThreshold (alpha / 8) (alpha / 4) (alpha / 2) k) ≤ (N : Real) := hN
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  have hginv : 1 ≤ (alpha / 2) ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ (by positivity) (by linarith))
  have hB : (B.card : Real) ≤ (N : Real) ^ (k + 1) := by
    exact_mod_cast (show B.card ≤ N ^ (k + 1) by
      simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤
      (alpha / 2) ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hprofile⟩ := section16_joint_power_structure_bounded hk T hth
    (alpha / 4) (alpha / 2) (by positivity) (by linarith) (by positivity) (by linarith) N
    ((le_max_left _ _).trans hNmax)
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
      (by rw [hRwidth, hhalf]; exact (le_max_right _ _).trans hNmax)
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

/-- The explicit threshold of degree `k+2` polynomial localization. -/
def jointPowerLocalizationThreshold (k : Nat) (T : Nat → Real → Real → Real)
    (alpha : Real) : Real :=
  max (section16JointFrequencyThreshold k T alpha)
    (positivePowerThreshold 4 1 (jointPowerLocalizationExponent alpha k))

theorem polynomial_localization_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], jointPowerLocalizationThreshold k T alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn (k + 2) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ jointPowerLocalizationExponent alpha k / (6 * (k + 1)) ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) (k + 1)
          (jointPowerLocalizationParameter alpha k) Q (l + 1) := by
  let e := jointPowerLocalizationExponent alpha k
  have he : 0 < e := jointPowerLocalizationExponent_pos hk ha haHalf
  intro N _ _ hN f hf hnot
  have hNmax : max (section16JointFrequencyThreshold k T alpha)
      (positivePowerThreshold 4 1 (jointPowerLocalizationExponent alpha k)) ≤ (N : Real) := hN
  have hlarge : 4 ≤ (N : Real) ^ e := by
    have hsize : positivePowerThreshold 4 1 e ≤ (N : Real) := (le_max_right _ _).trans hNmax
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he hsize
  obtain ⟨P, mu, hp, hmu, hw, hmass⟩ := section16_joint_frequency_box_bounded hk T hth alpha ha
    haHalf N ((le_max_left _ _).trans hNmax) f hf hnot
  have hwidth : (N : Real) ^ e ≤ P.width :=
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast NeZero.one_le : (1 : Real) ≤ N) (min_le_left _ _)).trans hw
  simpa [jointPowerLocalizationParameter, jointPowerLocalizationExponent, Nat.cast_add,
    add_assoc] using
    (polynomial_localization_of_dense_frequency_box (by omega) P hp f mu ha
    (section16JointFrequencyDensity_pos ha k) (min_le_right _ _) hf hmu hwidth hlarge hmass)

/-- One inverse step with the localization threshold written out. -/
theorem function_inverse_step_bounded {k : Nat} (hk : 1 ≤ k)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l))
    {alpha beta sigma Tlow : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (hbound : FunctionDiscrepancyBound (k + 1)
      ((jointPowerLocalizationParameter alpha k / 2) / (2 * (k + 3 : Nat) : Real) ^ (k + 3))
      beta sigma Tlow)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16) :
    FunctionDiscrepancyBound (k + 2) alpha
      (jointPowerLocalizationParameter alpha k * beta / 4)
      (inverseStepExponent (k + 1) (jointPowerLocalizationExponent alpha k) sigma)
      (max (shortLocalizationThreshold (k + 1) (jointPowerLocalizationExponent alpha k)
          (6 * ((k : Real) + 1)) Tlow (jointPowerLocalizationThreshold k T alpha))
        (inverseStepThreshold (k + 1) (jointPowerLocalizationParameter alpha k) beta
          (jointPowerLocalizationExponent alpha k) (6 * ((k : Real) + 1)) sigma)) := by
  have hk0 : (0 : Real) < k + 1 := by positivity
  refine hbound.of_short_polynomial_localization (Tloc := jointPowerLocalizationThreshold k T alpha)
    (c := 6 * ((k : Real) + 1))
    (jointPowerLocalizationParameter_pos ha k) hb hs hs16
    (jointPowerLocalizationExponent_pos hk ha haHalf) (by positivity) ?_
  intro N _ _ hN f hf hnot
  exact polynomial_localization_bounded hk T hth alpha ha haHalf N hN f hf hnot

/-- The structural thresholds in dimensions one and two. -/
def dimensionTwoThresholds : Nat → Real → Real → Real
  | 2 => section16DimTwoThreshold
  | _ => fun _ _ => 0

theorem dimensionTwoThresholds_bounded :
    ∀ l : Nat, 1 ≤ l → l ≤ 2 → Theorem162AtBounded l (dimensionTwoThresholds l) := by
  intro l hl hl2
  rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
  · exact lemma_16_3_bounded
  · exact theorem_16_2_at_two_bounded

/-- The explicit modulus threshold of the degree-four inverse theorem. -/
def quarticInverseThreshold (alpha : Real) : Real :=
  max (shortLocalizationThreshold (2 + 1)
      (jointPowerLocalizationExponent (structuralInverseInput alpha) 2)
      (6 * (((2 : Nat) : Real) + 1))
      (fejerCubicInverseThreshold
        (structuralInverseInput (jointStructuralInverseLowerInput alpha 2)))
      (jointPowerLocalizationThreshold 2 dimensionTwoThresholds (structuralInverseInput alpha)))
    (inverseStepThreshold (2 + 1)
      (jointPowerLocalizationParameter (structuralInverseInput alpha) 2)
      (jointStructuralInverseParameter 1 (jointStructuralInverseLowerInput alpha 2))
      (jointPowerLocalizationExponent (structuralInverseInput alpha) 2)
      (6 * (((2 : Nat) : Real) + 1))
      (jointStructuralInverseExponent 1 (jointStructuralInverseLowerInput alpha 2)))

/-- **The degree-four inverse theorem with an explicit threshold.** -/
theorem quartic_function_inverse_explicit {alpha : Real} (ha : 0 < alpha) :
    FunctionDiscrepancyBound 4 alpha
      (jointStructuralInverseParameter 2 alpha) (jointStructuralInverseExponent 2 alpha)
      (quarticInverseThreshold alpha) := by
  have hlow := jointStructuralInverseLowerInput_pos ha 2
  have hbase := fejer_cubic_function_discrepancy_bound (structuralInverseInput_pos hlow)
    ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))
  have hT : FunctionDiscrepancyBound 3 (jointStructuralInverseLowerInput alpha 2)
      (jointStructuralInverseParameter 1 (jointStructuralInverseLowerInput alpha 2))
      (jointStructuralInverseExponent 1 (jointStructuralInverseLowerInput alpha 2))
      (fejerCubicInverseThreshold
        (structuralInverseInput (jointStructuralInverseLowerInput alpha 2))) :=
    hbase.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl
  have hnext := function_inverse_step_bounded (k := 2) (by norm_num) dimensionTwoThresholds
    dimensionTwoThresholds_bounded (structuralInverseInput_pos ha) (min_le_right _ _) hT
    (jointStructuralInverseParameter_pos 1 hlow) (jointStructuralInverseExponent_pos 1 hlow)
    ((jointStructuralInverseExponent_le_one _ _).trans (by norm_num))
  exact hnext.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl

end LeanProofs.GowersSzemeredi
