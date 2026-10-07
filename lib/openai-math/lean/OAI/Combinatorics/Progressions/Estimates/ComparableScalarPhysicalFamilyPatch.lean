import OAI.Combinatorics.Progressions.Dynamics.RelativeScalarNetPassageBudget
import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
import OAI.Combinatorics.Progressions.Nilpotent.RelativeScalarNiltestConclusion

namespace OAI

section

namespace Erdos3

theorem comparableScalarSlice_early_room (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {p P0 : ℝ} (hp : 2 ≤ p)
    (hP0 : 3 * (8 * (((r * d : ℕ) : ℝ) + 1) * (p + 1)) + 10 ≤ P0) :
    p + 4 * (r : ℝ) + 4 ≤ P0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrd : (r : ℝ) ≤ ((r * d : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    nlinarith
  have hm : 0 ≤ (((r * d : ℕ) : ℝ) - r) * (p + 1) :=
    mul_nonneg (sub_nonneg.mpr hrd) (by linarith)
  nlinarith

theorem comparableScalarSlice_extra_caps (r : ℕ)
    {p P0 density : ℝ} (hp : 0 ≤ p) (hdensity : 0 < density)
    (hinv : density⁻¹ ≤ Real.exp p) (hroom : p + 4 * (r : ℝ) + 4 ≤ P0) :
    2 * (r : ℝ) ≤ Real.exp P0 ∧
    (density / 2)⁻¹ ≤ Real.exp P0 ∧
    4 * (r : ℝ) / density ≤ Real.exp P0 ∧
    (⌈2 / density⌉₊ : ℝ) ≤ Real.exp P0 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hone : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hcap : 4 * Real.exp p ≤ Real.exp P0 := by
    calc
      _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right h4 (Real.exp_pos p).le
      _ = Real.exp (4 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (show 2 * (r : ℝ) ≤ Real.exp (2 * r) by
      linarith [Real.add_one_le_exp (2 * (r : ℝ))]).trans
    exact Real.exp_le_exp.mpr (by linarith)
  · have he : (density / 2)⁻¹ = 2 * density⁻¹ := by field_simp
    rw [he]
    exact (mul_le_mul_of_nonneg_left hinv (by norm_num)).trans
      ((by nlinarith [Real.exp_pos p] : 2 * Real.exp p ≤ 4 * Real.exp p).trans hcap)
  · rw [div_eq_mul_inv]
    calc
      _ ≤ (4 * (r : ℝ)) * Real.exp p := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ Real.exp (4 * r) * Real.exp p := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 * (r : ℝ))]) (Real.exp_pos p).le
      _ = Real.exp (4 * r + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 / density by positivity)).le
    rw [div_eq_mul_inv] at hceil
    have hx := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    exact (show (⌈2 / density⌉₊ : ℝ) ≤ 4 * Real.exp p by
      simpa only [div_eq_mul_inv] using (show (⌈2 * density⁻¹⌉₊ : ℝ) ≤ 4 * Real.exp p by
        linarith)).trans hcap

theorem comparableScalarSlice_long_scale {p budget density : ℝ}
    (hdensity : Real.exp (-p) ≤ density) (hbudget : p + 4 ≤ budget) :
    4 ≤ density * Real.exp budget := by
  have hpos : 0 < density := (Real.exp_pos (-p)).trans_le hdensity
  calc
    4 ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp (-p) * Real.exp (p + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ density * Real.exp budget := mul_le_mul hdensity (Real.exp_le_exp.mpr hbudget)
      (Real.exp_nonneg _) hpos.le

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section
attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox

theorem exists_indexed_comparableScalarSliceGeometryTransfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ density : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    ((r*d : ℕ) : ℝ) ≤ Real.exp P0 → 2 * (r : ℝ) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < density → (density / 2)⁻¹ ≤ Real.exp P0 →
    4 * (r : ℝ) / density ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant (r*d) τ ≤ Real.exp P0 →
    4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option K × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → (q : ℝ) ≤ Real.exp P0 → 4 ≤ density * L →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : K, (0 : ℤ) < S.length j),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  let E := Classical.choose (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)
  have hE : 2 ≤ E := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)).1
  refine ⟨E, hE, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ density
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hratioP0 hprofile
    hdensity hdensityP0 hwidthP0 hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget
    g hg L parameters hlo hhi q S hq hqP0 hlong hlength N hN hunit Wsite width margin
  have data := indexedComparableScalarGeometryData d r hd hr hK hP0 hbudget0 hDP0 hprofile hσ hσ1 hτP0
    parameters hlo hhi N hN
  let : Nonempty K := Fintype.card_pos_iff.mp (by omega)
  have hratio : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  obtain ⟨hparam, hparMin, hparSide, hparWidth, hwidthRatio, hrelative, hleft, hright⟩ :=
    S.comparableScalarSliceParameterBox_bounds hq data.hL hdensity hratio hlong hhi hlength
  refine ⟨data.hwidth, data.hmargin, data.hZ, hparam, ?_⟩
  intro h hh hupper
  have hPone : (1 : ℝ) ≤ Real.exp P0 := Real.one_le_exp_iff.mpr hP0
  have hdD : d ≤ r*d := by have hh := Nat.mul_le_mul_right d hr; omega
  have hdP0 : (d : ℝ) ≤ Real.exp P0 :=
    (show (d : ℝ) ≤ ((r*d : ℕ) : ℝ) by exact_mod_cast hdD).trans hDP0
  have hK0 : 0 ≤ canonicalJointFrameWindowConstant (r*d) τ :=
    (by norm_num : (0 : ℝ) ≤ 2).trans
      (canonicalJointFrameWindowConstant_two_le (r*d) data.hτ data.hτ1)
  have htail := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)).2 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2
    hnTarget (by simpa only [hK] using hd) (by simpa only [hK] using hdP0) hprofile
    g hg (Classical.choice (inferInstance : Nonempty K)) q (fun j => (S.start j : ℤ)) 0
    (fun j => (S.length j : ℤ)) hparam hq hqP0
    L (2 * (r : ℝ)) 1 1 (canonicalJointFrameWindowConstant (r*d) τ)
    (density / 2) (4 * (r : ℝ) / density)
    (by linarith) (by norm_num) (by norm_num) hK0 (by positivity) (by positivity)
    hratioP0 hPone hPone hKP0 hdensityP0 hwidthP0
    0 N (fun i => 2 * (N i : ℝ)) (fun _ => le_rfl)
    (fun i => by nlinarith only [Nat.cast_nonneg (α := ℝ) (N i)]) hunit h hh hupper
    ⌈(r : ℝ) * L⌉₊ (density * L / 2) hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright width data.hwidth data.hZ margin data.hmargin data.hloss data.hroot
    (fun z => by simpa only [residueProfileWidth, Nat.cast_one, div_one]
      using data.hscale (some z.1,z.2)) hframeDim 0
    data.sourceGeometry.1
    (by simpa only [Fintype.mem_piFinset, Pi.zero_apply, width, Wsite, τ, L]
      using data.sourceGeometry.2.1)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.1 j i)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.2 j i)
    (by simpa only [hK] using hbudget) le_rfl
    (by simpa only [hK] using data.physicalSize)
  have hdec : (fun a b : K => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq K) := Subsingleton.elim _ _
  rw [hdec] at htail
  exact htail

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section

local instance comparableUnconditionedScalarSliceFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def ComparableUnconditionedScalarSliceTransferStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → q ≤ ⌈2 / density⌉₊ →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < S.length j),
    budget ≤ (p + F) ^ F ∧
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_comparable_unconditioned_scalar_slice_transfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableUnconditionedScalarSliceTransferStatement.{u,v} s d r epsilon := by
  unfold ComparableUnconditionedScalarSliceTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_comparableScalarSliceGeometryTransfer.{u,v} s d r hd hr
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_comparableScalarSelectedBudget E d r hE hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv
    g hg target budget L parameters hlo hhi q S hq hqCap hlength N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  have hsel := hselect (Fintype.card I) hp hn hσ hσinv
  have hpTarget := hsel.1
  have htarget := hsel.2.1
  have hnTarget := hsel.2.2.1
  have hframeDim := hsel.2.2.2.1
  have hP0 := hsel.2.2.2.2.1
  have htargetP0 := hsel.2.2.2.2.2.1
  have hepsP0 := hsel.2.2.2.2.2.2.1
  have hprofile := hsel.2.2.2.2.2.2.2.1
  have hDP0 := hsel.2.2.2.2.2.2.2.2.1
  have hdP0 := hsel.2.2.2.2.2.2.2.2.2.1
  have hrPlusOneP0 := hsel.2.2.2.2.2.2.2.2.2.2.1
  have htwoP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.1
  have hτP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudget0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hthreshold := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNlog := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudgetFinal := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hframeDim' : 4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, target] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option (Fin d) × I) = (d + 1) * Fintype.card I := by simp
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((r * d : ℕ) + 4 : ℝ) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  have hroom := comparableScalarSlice_early_room d r hd hr hp htargetP0
  obtain ⟨hratioP0, hdensityP0, hwidthP0, hqP0⟩ :=
    comparableScalarSlice_extra_caps r (by linarith : 0 ≤ p) hdensity hdensityInv hroom
  have hdensityLower : Real.exp (-p) ≤ density := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ hdensity (Real.exp_pos p)).mp hdensityInv
  have htBig : p + 4 ≤ target := by
    have hrd : (0 : ℝ) ≤ ((r*d : ℕ) : ℝ) := Nat.cast_nonneg _
    change p + 4 ≤ 8 * (((r*d : ℕ) : ℝ) + 1) * (p + 1)
    nlinarith
  have hpow : target + 2 ≤ budget := by
    change target + 2 ≤ (target + 2) ^ C
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ target + 2) (by omega : 1 ≤ C))
  have hlong : 4 ≤ density * L :=
    comparableScalarSlice_long_scale hdensityLower (htBig.trans (by linarith))
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom (I := I) (V := V) nilmanifold target epsilon P0 level budget σ density
      htarget hepsilon hepsilon1 hP0 htargetP0 hepsP0
      ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hDP0 hratioP0 hprofile hdensity hdensityP0 hwidthP0
      hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi q S hq
      ((Nat.cast_le.mpr hqCap).trans hqP0) hlong hlength N hNphysical hunit
  exact ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def IndexedComparableUnconditionedScalarSliceTransferStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → q ≤ ⌈2 / density⌉₊ →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : K, (0 : ℤ) < S.length j),
    budget ≤ (p + F) ^ F ∧
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_indexed_comparable_unconditioned_scalar_slice_transfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    IndexedComparableUnconditionedScalarSliceTransferStatement.{u,v,w} s d r epsilon := by
  unfold IndexedComparableUnconditionedScalarSliceTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_indexed_comparableScalarSliceGeometryTransfer.{u,v,w} s d r hd hr
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_comparableScalarSelectedBudget E d r hE hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv
    g hg target budget L parameters hlo hhi q S hq hqCap hlength N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  have hsel := hselect (Fintype.card I) hp hn hσ hσinv
  have hpTarget := hsel.1
  have htarget := hsel.2.1
  have hnTarget := hsel.2.2.1
  have hframeDim := hsel.2.2.2.1
  have hP0 := hsel.2.2.2.2.1
  have htargetP0 := hsel.2.2.2.2.2.1
  have hepsP0 := hsel.2.2.2.2.2.2.1
  have hprofile := hsel.2.2.2.2.2.2.2.1
  have hDP0 := hsel.2.2.2.2.2.2.2.2.1
  have hdP0 := hsel.2.2.2.2.2.2.2.2.2.1
  have hrPlusOneP0 := hsel.2.2.2.2.2.2.2.2.2.2.1
  have htwoP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.1
  have hτP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudget0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hthreshold := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNlog := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudgetFinal := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hframeDim' : 4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, hK, Nat.cast_mul, target] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option K × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option K × I) = (d + 1) * Fintype.card I := by simp [hK]
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((r * d : ℕ) + 4 : ℝ) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  have hroom := comparableScalarSlice_early_room d r hd hr hp htargetP0
  obtain ⟨hratioP0, hdensityP0, hwidthP0, hqP0⟩ :=
    comparableScalarSlice_extra_caps r (by linarith : 0 ≤ p) hdensity hdensityInv hroom
  have hdensityLower : Real.exp (-p) ≤ density := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ hdensity (Real.exp_pos p)).mp hdensityInv
  have htBig : p + 4 ≤ target := by
    have hrd : (0 : ℝ) ≤ ((r*d : ℕ) : ℝ) := Nat.cast_nonneg _
    change p + 4 ≤ 8 * (((r*d : ℕ) : ℝ) + 1) * (p + 1)
    nlinarith
  have hpow : target + 2 ≤ budget := by
    change target + 2 ≤ (target + 2) ^ C
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ target + 2) (by omega : 1 ≤ C))
  have hlong : 4 ≤ density * L :=
    comparableScalarSlice_long_scale hdensityLower (htBig.trans (by linarith))
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom hK (I := I) (V := V) nilmanifold target epsilon P0 level budget σ density
      htarget hepsilon hepsilon1 hP0 htargetP0 hepsP0
      ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hDP0 hratioP0 hprofile hdensity hdensityP0 hwidthP0
      hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi q S hq
      ((Nat.cast_le.mpr hqCap).trans hqP0) hlong hlength N hNphysical hunit
  exact ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

local instance comparableScalarSharedSliceFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def ComparableScalarSharedSliceTailStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ {κ : Type w} [Fintype κ] [Nonempty κ]
      (stride : κ → ℕ) (S : ∀ c, ResidueBoxSlice parameters (stride c)),
      (∀ c, 0 < stride c) → (∀ c, stride c ≤ ⌈2 / density⌉₊) →
      (∀ c j, density * L / 2 ≤ ((S c).length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ c j, (0 : ℤ) < (S c).length j),
    budget ≤ (p + F) ^ F ∧
    ∀ (c : κ) (h : (I → ℤ) → ℂ),
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => ((S c).length j : ℤ)) (hparam c)).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_comparable_scalar_shared_slice_tail (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ComparableScalarSharedSliceTailStatement.{u,v,w} s d r epsilon := by
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_comparable_unconditioned_scalar_slice_transfer.{u,v} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv
    hlevel hlevel2 hdensity hdensityInv g hg target budget L parameters hlo hhi
    κ _ _ stride S hq hqCap hlength N hN hunit τ Wsite width margin
  have hfamily (c : κ) := htransfer nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2
    hdensity hdensityInv g hg parameters hlo hhi (stride c) (S c) (hq c) (hqCap c)
    (hlength c) N hN hunit
  choose hwidth hmargin hZ hparam hbudget htail using hfamily
  let c0 : κ := Classical.choice inferInstance
  refine ⟨hwidth c0, hmargin c0, hZ c0, hparam, hbudget c0, ?_⟩
  intro c h hh hnoincrement
  exact htail c h hh hnoincrement

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance comparableRetainedFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_comparable_scalar_retained_slice_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ C F : ℕ, 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {p σ Λ density accuracy gain : ℝ},
    2 ≤ p → (Fintype.card I : ℝ) ≤ p →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-p) ≤ (1 - τ) * Λ →
    0 < density → density ≤ 1 → density⁻¹ ≤ Real.exp p →
    0 < accuracy → accuracy ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE p → relativePatchComplexity P ≤ p →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    let Q := ⌈2 / density⌉₊
    let K := denseResidueMeshCap d density accuracy (r : ℝ)
    Real.exp (-target) < gain - accuracy / 2 →
    16 * ((d : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ parameters : Fin d → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) * Real.exp (-target) <
        outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        gain ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨heps, heps1⟩ := relativeScalarPassageSlack_bounds hτ hτhalf
  obtain ⟨_, C, F, _, hC, hF, hscalar⟩ :=
    exists_comparable_scalar_shared_slice_tail.{u,v,0} s d r hd hr heps heps1
  refine ⟨C, F, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d₀ rank nilmanifold p σ Λ density accuracy gain hp hn
    hσ hσ1 hσinv hΛ hlevel hdensity hdensity1 hdensityInv haccuracy haccuracy1
    P g hg hP hgval target budget L Q K hgap hmesh parameters hlo hhi N hN f hf
    trim Wsite width margin
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨stride, slices, hlen, hstride, hlength, hnet⟩ :=
    exists_denseResidueScalarScore_net (Fin d) hdensity hdensity1 haccuracy haccuracy1
      (show (1 : ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by omega))
      L (by simpa only [Fintype.card_fin] using hmesh) parameters (fun j => ⟨hlo j, hhi j⟩)
  have hlevel2 : (1 - τ) * Λ ≤ 2 := by nlinarith [hΛ.1, hΛ.2]
  have hunit (x : I → ℤ) (_hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      (g.eval x).im = 0 ∧ 0 ≤ (g.eval x).re ∧ (g.eval x).re ≤ 1 := by
    rw [hgval]
    exact ⟨Complex.ofReal_im _, by simpa only [Complex.ofReal_re, Set.mem_Icc] using P.value_mem_Icc _⟩
  obtain ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩ :=
    hscalar nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv g hg
      parameters hlo hhi stride slices (fun c => (hstride c).1) (fun c => (hstride c).2)
      hlength N hN hunit
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hmass hinside hretained
  let h : (I → ℤ) → ℂ := fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)
  have hgf : g.eval = fun x => (P.value (fun i => (x i : ℝ)) : ℂ) := funext hgval
  have hh (x : I → ℤ) (hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      0 ≤ (h x).re ∧ (h x).re ≤ 1 := by
    change 0 ≤ f x * P.value _ ∧ f x * P.value _ ≤ 1
    refine ⟨mul_nonneg (hf x hx).1 (P.value_mem_Icc _).1, ?_⟩
    calc
      f x * P.value _ ≤ 1 * P.value _ :=
        mul_le_mul_of_nonneg_right (hf x hx).2 (P.value_mem_Icc _).1
      _ ≤ 1 := by simpa only [one_mul] using (P.value_mem_Icc _).2
  obtain ⟨c, lo, H, M, a, hM, hbox, hcost, hne, _, hscore⟩ :=
    exists_residue_slice_of_rectangular_scalar_family outer
      (fun z i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) 0 N
      (fun _ => h) (fun _ => g.eval) (fun _ => relativeScalarPassageSlack τ)
      (fun _ => (1 - τ) * Λ) (fun _ => budget) stride
      (fun c j => ((slices c).start j : ℤ)) (fun _ => 0)
      (fun c j => ((slices c).length j : ℤ)) hparam target
      (fun c hupper => by
        simpa only [rectangularScalarDiscrepancy, outer, margin, width, Wsite, trim, target, Pi.zero_def]
          using htail c h hh hupper)
      retained (by simpa only [Fintype.card_fin] using hmass) (by
        intro z hz
        obtain ⟨q, hq, S, hS, hdense, hscore⟩ := hretained z hz
        obtain ⟨c, hc⟩ := hnet P f 0 N
          (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)
          (hinside z hz) hf hτ hτhalf hΛ q hq S hS hdense hscore
        refine ⟨c, hgap.trans_le ?_⟩
        simpa only [h, hgf] using hc)
  have hpTarget : p ≤ target := by
    dsimp [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r * d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hpow := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2) ^ C
    linarith
  have hresult := relativePatchSliceConclusion_of_scalarNiltest nilmanifold N f P g h hgval
    (fun x => by simp only [h, hgval, Complex.ofReal_mul])
    lo H M a ((1 - τ) * Λ) budget hM hbox hne hcost
    (hP.trans (hpTarget.trans htargetBudget)) hscore
  exact hresult.mono le_rfl hbudgetFinal

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance comparableEarlyRetainedFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices unconditionedSpatialTrimFraction
  selectedResidueSmoothWeight RelativePatchSliceConclusion
  FiniteProbabilityWeights.eventProbability

theorem exists_comparable_scalar_early_retained_slice_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ parameters : Fin d → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      Real.exp (-b) ≤ outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        Real.exp (-b) ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, hE, hnumeric⟩ := exists_relativeScalarNetPassage_power_budget d r (by omega)
  obtain ⟨C, F, hC, hF, hscalar⟩ :=
    exists_comparable_scalar_retained_slice_patch.{u,v} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters hlo hhi N hN f hf trim Wsite width margin
  obtain ⟨hp, hbp, _hcard, hmass, hgap, hlevel, hdensityInv, _hQ,
      _hhalf, _hratio, _hwidth, hmesh, _hlong⟩ := hnumeric b density hb hdensity hdensity1
  have hbp' : b ≤ p := by linarith
  have hn' : (Fintype.card I : ℝ) ≤ p := hn.trans hbp'
  have hσinv' : σ⁻¹ ≤ Real.exp p := hσinv.trans (Real.exp_le_exp.mpr hbp')
  have hdensity0 : 0 < density := (Real.exp_pos (-b)).trans_le hdensity
  have haccuracy1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpTarget : p ≤ target := by
    dsimp only [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r*d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hh := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2)^C
    linarith
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar nilmanifold hp hn' hσ hσ1 hσinv' hΛ (hlevel Λ τ hΛlower hτhalf)
      hdensity0 hdensity1 hdensityInv (Real.exp_pos (-b)) haccuracy1
      P g (hg.mono hbp') (hP.trans hbp') hgeval hgap
      (hmesh budget (hpTarget.trans htargetBudget)) parameters hlo hhi N hN f hf
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hretained hinside hscore
  apply hpassage retained
  · simpa only [DenseResidueSliceNetCode.card, Fintype.card_fin,
      outer, margin, width, Wsite, trim] using hmass.trans_le hretained
  · exact hinside
  · exact hscore

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance comparablePhysicalFamilyFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card trimmedSpatialWidths spatialTrimMargin
  rectangularWeightIndices unconditionedSpatialTrimFraction selectedResidueSmoothWeight
  RelativePatchSliceConclusion FiniteProbabilityWeights.eventProbability

theorem exists_comparable_scalar_physical_family_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [_decI : DecidableEq I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ) [∀ j, NeZero (parameters j)],
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := unconditionedResidueSiteBound parameters
    let width := trimmedSpatialWidths (K := Fin d) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ (retained : Finset (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1))
      (localLaw : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) →
        FiniteProbabilityWeights (integerBox parameters)),
      Real.exp (-b) ≤ outer.mass retained →
      (∀ z ∈ retained, ∀ u : ∀ j, ZMod (parameters j),
        jointIntegerPhysicalSite (residueBoxIntegerPoint parameters u) (z.1.val,z.2.val) ∈
          integerBox N) →
      (∀ z ∈ retained, ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        localLaw z = S.fullSliceLaw hlen) →
      (∀ z ∈ retained, Real.exp (-b) ≤ (localLaw z).mean (fun u =>
        (f (jointIntegerPhysicalSite u.val (z.1.val,z.2.val)) - Λ) *
          P.value (fun i => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, C, F, hE, hC, hF, hscalar⟩ :=
    exists_comparable_scalar_early_retained_slice_patch.{u,v} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro I V _ decI _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters _ hlo hhi N hN f hf trim Wsite width margin
  have hdec : decI = Classical.decEq I := Subsingleton.elim _ _
  subst decI
  have hzero : translatedIntegerBox (0 : I → ℤ) N = integerBox N := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hf' : ∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [hzero] using hf
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar nilmanifold hb hn hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
      parameters hlo hhi N hN f hf'
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained localLaw hmass hinside hslice hscore
  apply hpassage (fun z => z ∈ retained)
  · change Real.exp (-b) ≤ outer.eventProbability (fun z => z ∈ retained)
    rw [FiniteProbabilityWeights.eventProbability_mem]
    exact hmass
  · intro z hz u
    rw [hzero]
    exact smoothAffineSample_inside_of_residue_sites parameters N (z.1.val,z.2.val)
      (hinside z hz) u
  · intro z hz
    obtain ⟨q, hq, S, hlen, hdense, hlaw⟩ := hslice z hz
    refine ⟨q, hq, S, hlen, hdense, ?_⟩
    have h := hscore z hz
    rw [hlaw] at h
    simpa only [smoothAffineSample_jointIntegerFrame] using h

end
end Erdos3

end

end OAI
