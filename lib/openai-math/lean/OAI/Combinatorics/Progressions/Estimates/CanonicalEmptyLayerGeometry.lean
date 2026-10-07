import OAI.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
import OAI.Combinatorics.Progressions.Geometry.UnconditionedJointReferenceSupport
import OAI.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
import OAI.Combinatorics.Progressions.Probability.AllocatedZeroLayerLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointReference_collision {K I : Type*} [Fintype K] [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) (r s : K → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z) :
    (selectedJointReference A hA modulus T W hW hZ).mean
      (fun z => if jointIntegerPhysicalSite r (z.1.val,z.2.val) =
        jointIntegerPhysicalSite s (z.1.val,z.2.val) then 1 else 0) =
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) := by
  simp only [selectedJointReference, FiniteProbabilityWeights.mean_prod,
    jointIntegerPhysicalSite, add_right_inj]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_const
    ((selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0))

theorem selectedJointFiniteLaw_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    {M : ℝ} (hM : 0 ≤ M) (hcap : ∀ a z, D a z ≤ M) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤
        2*M*((Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L)) := by
  rw [selectedJointFiniteLaw]
  apply FiniteProbabilityWeights.reweightPositive_noninjectivity_le
    (selectedJointReference A hA modulus T W hW hZ)
    (fun z s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD) hM (fun z => hcap z.1.val z.2.val)
  · rwa [selectedJointReference_densityMass]
  · positivity
  · intro s t hst
    rw [selectedJointReference_collision]
    exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
      modulus hmodulus T hT W hW hZ hscale hL hwidth

theorem selectedJointFiniteLaw_collision_small {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (A : Finset (X → ℤ)) (hA : A.Nonempty)
    (m : ℕ) (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (selectedCollisionLog m P) ≤ N) (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (X → ℤ) → (Option K × X → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    (hcap : ∀ a z, D a z ≤ Real.exp (selectedDensityLog m P)) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := selectedJointFiniteLaw_noninjectivity_le A hA site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size m (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointReference_trimmed_complex_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(selectedJointReference (trimmedIntegerBox N R) (trimmedIntegerBox_nonempty N R hR)
      modulus T W hW hZ).complexMean
        (fun z => f (jointIntegerPhysicalSite root (z.1.val, z.2.val))) -
      𝔼 x ∈ integerBox N, f x‖ ≤ 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  rw [selectedJointReference, FiniteProbabilityWeights.complexMean_prod]
  have he (a : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simp only [jointIntegerPhysicalSite, he]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun a =>
      ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        f (a + integerPhysicalSite root z))]
  exact selectedResidue_trimmed_reference_compare root N R hR modulus T W hW hZ hwidth f hf

theorem selectedJointReference_trimmed_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, |f x| ≤ 1) :
    |(selectedJointReference (trimmedIntegerBox N R) (trimmedIntegerBox_nonempty N R hR)
      modulus T W hW hZ).mean
        (fun z => f (jointIntegerPhysicalSite root (z.1.val, z.2.val))) -
      𝔼 x ∈ integerBox N, f x| ≤ 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  have h := selectedJointReference_trimmed_complex_compare root N R hR modulus T W hW hZ
    hwidth (fun x => (f x : ℂ)) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf)
  have hr := (Complex.abs_re_le_norm _).trans h
  simpa only [Complex.sub_re, FiniteProbabilityWeights.complexMean_re,
    Complex.ofReal_re, Finset.expect, Complex.smul_re, Complex.re_sum] using hr

theorem selectedJointReference_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k, i)) :
    (selectedJointReference A hA modulus T W hW hZ).mean
      (fun z => noninjectivityIndicator
        (fun s => jointIntegerPhysicalSite (site s) (z.1.val, z.2.val))) ≤
      (Fintype.card S : ℝ)^2 * (2 * (modulus i : ℝ) / L) := by
  apply FiniteProbabilityWeights.noninjectivity_le _ _ (by positivity)
  intro s t hst
  rw [selectedJointReference_collision]
  exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
    modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

theorem zero_slot_score_mean_lower_bound {X : Type*} [Fintype X] [DecidableEq X]
    {s : ℕ} (B : PolynomialPatch X s 0) (N : X → ℕ)
    (hN : (integerBox N).Nonempty) (f : (X → ℤ) → ℝ) {a σ : ℝ}
    (hσ : 0 < σ)
    (hscore : σ ≤ 𝔼 x ∈ integerBox N,
      (f x - a) * B.value (fun i => (x i : ℝ))) :
    a + σ ≤ 𝔼 x ∈ integerBox N, f x := by
  have hc := B.value_mem_Icc (fun _ => 0)
  simp only [PolynomialPatch.value_rank_zero] at hc hscore
  rw [← Finset.expect_mul, Finset.expect_sub_distrib, Finset.expect_const hN] at hscore
  have hpos : 0 ≤ (𝔼 x ∈ integerBox N, f x) - a := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hc.1
    linarith
  have hle := mul_le_mul_of_nonneg_left hc.2 hpos
  linarith

private theorem productive_finite_samples {Ω S Y : Type*}
    [Fintype Ω] [Fintype S] [Nonempty S]
    (law : FiniteProbabilityWeights Ω) (image : Ω → S → Y)
    (f : Y → ℝ) {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (hf : ∀ y, f y ≤ 1)
    (hmarginal : ∀ r, a + 7 * σ / 8 ≤ law.mean (fun z => f (image z r)))
    (hcollision : law.mean (fun z => noninjectivityIndicator (image z)) ≤ σ / 16) :
    ∃ productive : Finset Ω, σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (image z)) ∧
      ∀ z ∈ productive, a + σ / 2 ≤ 𝔼 r : S, f (image z r) := by
  let score := fun z => 𝔼 r : S, (f (image z r) - a)
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    dsimp only [score]
    apply Finset.expect_le Finset.univ_nonempty
    intro r _
    linarith [hf (image z r)]
  have hbad : law.mass bad ≤ σ / 16 := by
    have he : law.mass bad = law.mean (fun z => noninjectivityIndicator (image z)) := by
      rw [← law.mean_indicator]
      congr 1
      funext z
      by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
    rw [he]
    exact hcollision
  have hmeanScore : 7 * σ / 8 ≤ law.mean score := by
    have he := law.mean_comm (FiniteProbabilityWeights.uniform S)
      (fun z r => f (image z r) - a)
    simp only [FiniteProbabilityWeights.uniform_mean] at he
    change law.mean score = _ at he
    rw [he]
    apply Finset.le_expect Finset.univ_nonempty
    intro r _
    rw [law.mean_sub, law.mean_const]
    linarith [hmarginal r]
  let productive := Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z)
  refine ⟨productive, ?_, ?_, ?_⟩
  · have h := law.productive_mass_lower_bound score bad (a := σ / 2)
      (by positivity) hscore
    change _ ≤ law.mass productive at h
    linarith
  · intro z hz
    have h := (Finset.mem_filter.mp hz).2.1
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using h
  · intro z hz
    have h := (Finset.mem_filter.mp hz).2.2
    simp only [score, Finset.expect_sub_distrib, Fintype.expect_const] at h
    linarith

namespace BooleanCubeKernel

theorem exists_unconditioned_productive_family
    {K X S : Type*} [Fintype K] [Fintype X] [DecidableEq X]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (N R : X → ℕ) (hR : ∀ i, 2 * R i < N i)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    (modulus : X → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L a σ : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (hfit : ∀ r j, physicalSiteWidth (site r) W j ≤ (R j : ℝ))
    (ha : 0 ≤ a) (hσ : 0 < σ)
    (hboundary : 2 * (∑ j, 2 * (R j : ℝ) / N j) ≤ σ / 8)
    (hcollision : (Fintype.card S : ℝ)^2 * (2 * (modulus i : ℝ) / L) ≤ σ / 16)
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) modulus T W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective
        (fun r => jointIntegerPhysicalSite (site r) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤
        𝔼 r : S, f (jointIntegerPhysicalSite (site r) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ r,
        jointIntegerPhysicalSite (site r) (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : K → ℤ)
    modulus hmodulus T hT W hW hscale
  refine ⟨hZ, ?_⟩
  intro law
  let image := fun (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) r =>
    jointIntegerPhysicalSite (site r) (z.1.val,z.2.val)
  have hmarginal (r : S) : a + 7 * σ / 8 ≤ law.mean (fun z => f (image z r)) := by
    have h := selectedJointReference_trimmed_compare (site r) N R hR modulus T W hW hZ
      (hfit r) f (fun x _ => abs_le.mpr ⟨by linarith [(hf x).1], (hf x).2⟩)
    have hlo := (abs_le.mp h).1
    change -_ ≤ law.mean (fun z => f (image z r)) - _ at hlo
    linarith
  have hbad := selectedJointReference_noninjectivity_le (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) site hsite i modulus hmodulus T hT W hW hZ
    hscale hL hwidth
  obtain ⟨productive, hmass, hinj, hlocal⟩ := productive_finite_samples law image f ha hσ
    (fun x => (hf x).2) hmarginal (hbad.trans hcollision)
  refine ⟨productive, hmass, hinj, hlocal, ?_⟩
  intro z r
  exact jointIntegerPhysicalSite_mem_box (site r) N R (fun j => (hR j).le) W (hfit r) z

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def unconditionedResidueSiteBound {K : Type*} [Fintype K] (P : K → ℕ) : ℝ :=
  ∑ k, (P k : ℝ)

noncomputable def unconditionedCollisionWidth {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] (σ : ℝ) : ℝ :=
  32 * (Fintype.card (∀ k, ZMod (P k)) : ℝ) ^ 2 / σ

theorem residueBoxIntegerPoint_sum_abs_le {K : Type*} [Fintype K]
    (P : K → ℕ) [∀ k, NeZero (P k)] (u : ∀ k, ZMod (P k)) :
    (∑ k, |(residueBoxIntegerPoint P u k : ℝ)|) ≤ unconditionedResidueSiteBound P := by
  apply Finset.sum_le_sum
  intro k _
  change |((u k).val : ℝ)| ≤ (P k : ℝ)
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (ZMod.val_lt (u k)).le

theorem unconditionedCollisionWidth_pos {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] {σ : ℝ} (hσ : 0 < σ) :
    0 < unconditionedCollisionWidth P σ := by
  have hc : 0 < (Fintype.card (∀ k, ZMod (P k)) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ∀ k, ZMod (P k))
  unfold unconditionedCollisionWidth
  positivity

theorem unconditionedCollisionWidth_collision {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] {σ : ℝ} (hσ : 0 < σ) :
    (Fintype.card (∀ k, ZMod (P k)) : ℝ) ^ 2 * (2 / unconditionedCollisionWidth P σ) = σ / 16 := by
  have hc : (Fintype.card (∀ k, ZMod (P k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ∀ k, ZMod (P k))
  unfold unconditionedCollisionWidth
  field_simp
  ring

namespace BooleanCubeKernel

theorem exists_concrete_unconditioned_productive_family
    {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (P : K → ℕ) [∀ k, NeZero (P k)] (i : X)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) (unconditionedResidueSiteBound P) τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤ 𝔼 u : ∀ k, ZMod (P k),
        f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) (unconditionedResidueSiteBound P) τ N
  let R := spatialTrimMargin τ N
  have hB : 0 ≤ unconditionedResidueSiteBound P := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  obtain ⟨_, _, hW, hscale, hwidth, hR, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hB hσ hσ1 N hN
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1
  have hsite : Function.Injective (residueBoxIntegerPoint P) := by
    intro u v he
    funext k
    apply ZMod.val_injective
    have hk := congrFun he k
    change ((u k).val : ℤ) = ((v k).val : ℤ) at hk
    exact_mod_cast hk
  have hfit (u : ∀ k, ZMod (P k)) (j : X) : physicalSiteWidth (residueBoxIntegerPoint P u) W j ≤ (R j : ℝ) :=
    spatialTrimMargin_fits hB hτ.le (residueBoxIntegerPoint P u)
      (residueBoxIntegerPoint_sum_abs_le P u) N j
  obtain ⟨hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_productive_family N R hR (residueBoxIntegerPoint P) hsite i
      (fun _ : X => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _) W hW hscale
      (unconditionedCollisionWidth_pos P hσ) (fun k => hwidth (some k, i)) hfit ha hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using (unconditionedCollisionWidth_collision P hσ).le)
      f hf hmean
  exact ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_expect {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, relativeBoxInput N f x) = (𝔼 x ∈ integerBox N, f x) := by
  apply Finset.expect_congr rfl
  intro x hx
  exact relativeBoxInput_eq N f (by simpa using hx)

theorem relativePatch_zeroStage_mean_lower_bound
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (f : (X → ℤ) → ℝ)
    (patch : PolynomialPatch X s d) {a surplus : ℝ}
    (hsurplus : 0 < surplus)
    (hstage : relativePatchDistinctWeights patch ≤ 0)
    (hscore : surplus ≤ relativePatchBoxScore N f a patch) :
    d = 0 ∧ a + surplus ≤ (𝔼 x ∈ integerBox N, relativeBoxInput N f x) := by
  have hd : d = 0 := (relativePatchDistinctWeights_eq_zero_iff patch).mp (Nat.eq_zero_of_le_zero hstage)
  refine ⟨hd, ?_⟩
  subst d
  rw [relativeBoxInput_expect]
  have hbox : (integerBox N).Nonempty := by
    refine ⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩
    intro i
    exact ⟨le_refl _, by exact_mod_cast hN i⟩
  exact zero_slot_score_mean_lower_bound patch N hbox f hsurplus hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem unconditioned_base_impossibility
    {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (P : K → ℕ) [∀ j, NeZero (P j)] (i : X) {k s : ℕ} (hk : 2 ≤ k)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (hN : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ)
      (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree (Function.support f) k)
    (B : PolynomialPatch X s 0)
    (hscore : σ ≤ 𝔼 x ∈ integerBox N,
      (f x - a) * B.value (fun j => (x j : ℝ)))
    (habsolute : ∀ g : (∀ j, ZMod (P j)) → ℝ,
      (∀ u, g u ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree (residueBoxIntegerPoint P '' Function.support g) k →
      a ≤ (𝔼 u, g u) → False) : False := by
  have hmean := zero_slot_score_mean_lower_bound B N hbox f hσ hscore
  have hσ1 : σ ≤ 1 := by
    have hcap : (𝔼 x ∈ integerBox N, f x) ≤ 1 :=
      Finset.expect_le hbox (fun x _ => (hf x).2)
    linarith
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, _⟩ :=
    BooleanCubeKernel.exists_concrete_unconditioned_productive_family P i ha hσ hσ1
      N hN f hf hmean
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨z, hz⟩ := hne
  apply habsolute
    (fun u => f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
      (z.1.val,z.2.val))) (fun _ => hf _)
    (BooleanCubeKernel.joint_residue_sample_progression_free f hfree hk P
      (z.1.val,z.2.val) (hinj z hz))
  exact (by linarith : a ≤ a + σ / 2).trans (hlocal z hz)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

def zeroLayerVariablesEquiv : LayerSamplerVariables G I n B ≃ G where
  toFun := fun k => match k with
    | .inl g => g
    | .inr a => Fin.elim0 a.1.1
  invFun := Sum.inl
  left_inv := by
    intro k
    cases k with
    | inl g => rfl
    | inr a => exact Fin.elim0 a.1.1
  right_inv := fun _ => rfl

@[simp] theorem zeroLayerVariablesEquiv_inl (g : G) :
    zeroLayerVariablesEquiv B (Sum.inl g) = g := rfl

@[simp] theorem zeroLayerVariablesEquiv_symm (g : G) :
    (zeroLayerVariablesEquiv B).symm g = Sum.inl g := rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

def zeroLayerSamplerScale (S : ℕ) (hS : 0 < S) :
    LayerSamplerScale (G := G) B U b R σ where
  value := S
  positive := hS
  width := fun j => Fin.elim0 j
  gap := fun j => Fin.elim0 j

theorem zeroLayerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G :=
  Fintype.card_congr (zeroLayerVariablesEquiv B)

variable (S : LayerSamplerScale (G := G) B U b R σ)

@[simp] theorem allocatedExternalCandidateSides_zero_layers
    (k : LayerSamplerVariables G I n B) :
    allocatedExternalCandidateSides B U b S k = S.value := by
  cases k with
  | inl g => rfl
  | inr a => exact Fin.elim0 a.1.1

theorem allocatedExternalCandidateSides_zero_layers_fun :
    allocatedExternalCandidateSides B U b S =
      fun _ : LayerSamplerVariables G I n B => S.value :=
  funext (allocatedExternalCandidateSides_zero_layers B U b S)

theorem allocatedExternalCandidateRootBudget_zero_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [zeroLayerVariables_card]

theorem allocatedExternalCandidateWidths_zero_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N := by
  funext z
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_zero_layers]
  rcases z with ⟨_ | k, x⟩
  · rfl
  · cases k with
    | inl g => rfl
    | inr a => exact Fin.elim0 a.1.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

def emptyLayerVariablesEquiv : LayerSamplerVariables G I n B ≃ G where
  toFun := fun k => match k with
    | .inl g => g
    | .inr a => Sum.elim isEmptyElim isEmptyElim a.1.2
  invFun := Sum.inl
  left_inv := by
    intro k
    cases k with
    | inl g => rfl
    | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2
  right_inv := fun _ => rfl

@[simp] theorem emptyLayerVariablesEquiv_inl (g : G) :
    emptyLayerVariablesEquiv B (Sum.inl g) = g := rfl

@[simp] theorem emptyLayerVariablesEquiv_symm (g : G) :
    (emptyLayerVariablesEquiv B).symm g = Sum.inl g := rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

theorem emptyLayerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G :=
  Fintype.card_congr (emptyLayerVariablesEquiv B)

variable (S : LayerSamplerScale (G := G) B U b R σ)

@[simp] theorem allocatedExternalCandidateSides_empty_layers
    (k : LayerSamplerVariables G I n B) :
    allocatedExternalCandidateSides B U b S k = S.value := by
  cases k with
  | inl g => rfl
  | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2

theorem allocatedExternalCandidateSides_empty_layers_fun :
    allocatedExternalCandidateSides B U b S =
      fun _ : LayerSamplerVariables G I n B => S.value :=
  funext (allocatedExternalCandidateSides_empty_layers B U b S)

theorem allocatedExternalCandidateRootBudget_empty_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [emptyLayerVariables_card]

theorem allocatedExternalCandidateWidths_empty_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N := by
  funext z
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_empty_layers]
  rcases z with ⟨_ | k, x⟩
  · rfl
  · cases k with
    | inl g => rfl
    | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2

theorem allocatedExternalCandidateWidths_empty_layers_narrowing
    (N : X → ℕ) (τ ξ ξ' : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      allocatedExternalCandidateWidths B U b S N τ ξ' := by
  rw [allocatedExternalCandidateWidths_empty_layers,
    allocatedExternalCandidateWidths_empty_layers]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateSides_sum_zero_layers :
    unconditionedResidueSiteBound (allocatedExternalCandidateSides B U b S) =
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
  simp only [unconditionedResidueSiteBound, allocatedExternalCandidateSides_zero_layers,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem allocatedExternalCandidateWidths_eq_scalar_zero_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        (unconditionedResidueSiteBound (allocatedExternalCandidateSides B U b S)) τ N := by
  rw [allocatedExternalCandidateSides_sum_zero_layers, zeroLayerVariables_card,
    allocatedExternalCandidateWidths_zero_layers]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def scalarNativeDimension (s : ℕ) : ℕ := (s + 1) * (s + 3)

theorem scalarNativeDimension_pos (s : ℕ) : 0 < scalarNativeDimension s := by
  unfold scalarNativeDimension
  positivity

theorem scalarNativeDimension_capacity {r s : ℕ} (hrs : r ≤ s) :
    (r + 1) * (r + 3) ≤ scalarNativeDimension s := by
  exact Nat.mul_le_mul (Nat.add_le_add_right hrs 1) (Nat.add_le_add_right hrs 3)

theorem scalarNativeDimension_selection_bound {r s : ℕ} (hrs : r ≤ s) :
    r + 1 ≤ scalarNativeDimension s := by
  exact (Nat.le_mul_of_pos_right (r + 1) (by omega : 0 < r + 3)).trans
    (scalarNativeDimension_capacity hrs)

def scalarNativeSelection {r s : ℕ} (hrs : r ≤ s) :
    Fin (r + 1) ↪ Fin (scalarNativeDimension s) where
  toFun a := ⟨a.val, a.isLt.trans_le (scalarNativeDimension_selection_bound hrs)⟩
  inj' := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin (scalarNativeDimension s) => z.val) hab)

@[simp] theorem scalarNativeSelection_val {r s : ℕ} (hrs : r ≤ s) (a : Fin (r + 1)) :
    (scalarNativeSelection hrs a).val = a.val := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev I (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev J (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev Q (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev n (q : ℕ) (_ : Fin q) : ℕ := 0

abbrev B (q : ℕ) (_ : LayerSamplerAxis (I q) (n q)) : Type := PEmpty

noncomputable def U (q : ℕ) (j : Fin q) : Submodule ℝ (J q j → ℝ) := ⊥

noncomputable def b (q : ℕ) (j : Fin q) :
    Basis (Fin (n q j)) ℝ (euclideanSubspace (U q j))ᗮ :=
  Basis.empty _

theorem hb (q : ℕ) (j : Fin q) :
    span ℤ (Set.range (b q j)) = projectedIntegerLattice (euclideanSubspace (U q j)) :=
  Subsingleton.elim _ _

noncomputable def o (q : ℕ) (j : Fin q) :
    OrthonormalBasis (I q j) ℝ (euclideanSubspace (U q j)) :=
  (Basis.empty _).toOrthonormalBasis ⟨fun i => isEmptyElim i,
    fun i => isEmptyElim i⟩

noncomputable def bW (q : ℕ) (j : Fin q) :
    Basis (Q q j) ℤ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) :=
  Basis.empty _

instance lattice_full (q : ℕ) (j : Fin q) :
    IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) := by
  constructor
  exact Subsingleton.elim _ _

noncomputable def poly (q : ℕ) (X : Type*) (j : Fin q) :
    VectorPolynomial X ℝ (J q j → ℝ) := 0

theorem poly_mem (q : ℕ) (X : Type*) (j : Fin q) (α : X →₀ ℕ) :
    coefficients (poly q X j) α ∈ U q j := by
  have hzero : coefficients (poly q X j) α = 0 := Subsingleton.elim _ _
  rw [hzero]
  exact Submodule.zero_mem _

theorem poly_degree (q : ℕ) (X : Type*) (j : Fin q) :
    DegreeLE (fun _ => 1) (j.val + 1) (poly q X j) := by
  intro α _
  exact Subsingleton.elim _ _

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
