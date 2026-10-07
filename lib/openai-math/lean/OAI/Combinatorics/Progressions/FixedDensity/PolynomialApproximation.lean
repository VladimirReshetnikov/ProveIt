import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.ContinuousMap.Weierstrass
import OAI.Combinatorics.Progressions.FixedDensity.Energy

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped Pointwise

noncomputable def finitePairing
    {Ω : Type*} [Fintype Ω] (f q : Ω → ℝ) : ℝ :=
  mean (fun x => f x * q x)

theorem finitePairing_add_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f + g) q =
      finitePairing f q + finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_add_right
    {Ω : Type*} [Fintype Ω]
    (f q r : Ω → ℝ) :
    finitePairing f (q + r) =
      finitePairing f q + finitePairing f r := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_sub_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f - g) q =
      finitePairing f q - finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring

theorem finitePairing_sub_right
    {Ω : Type*} [Fintype Ω]
    (f q r : Ω → ℝ) :
    finitePairing f (q - r) =
      finitePairing f q - finitePairing f r := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring

theorem finitePairing_smul_left
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing (c • f) q = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finitePairing_smul_right
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing f (c • q) = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finitePairing_comm
    {Ω : Type*} [Fintype Ω]
    (f q : Ω → ℝ) :
    finitePairing f q = finitePairing q f := by
  apply congrArg mean
  funext x
  exact mul_comm _ _

theorem finitePairing_mono_left
    {Ω : Type*} [Fintype Ω]
    {f g q : Ω → ℝ}
    (hfg : ∀ x, f x ≤ g x) (hq : ∀ x, 0 ≤ q x) :
    finitePairing f q ≤ finitePairing g q :=
  mean_mono fun x => mul_le_mul_of_nonneg_right (hfg x) (hq x)

theorem finitePairing_mono_right
    {Ω : Type*} [Fintype Ω]
    {f q r : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hqr : ∀ x, q x ≤ r x) :
    finitePairing f q ≤ finitePairing f r :=
  mean_mono fun x => mul_le_mul_of_nonneg_left (hqr x) (hf x)

def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1

theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2

theorem isUnitBounded_zero {Ω : Type*} :
    IsUnitBounded (fun _ : Ω => (0 : ℝ)) :=
  ⟨fun _ => le_rfl, fun _ => zero_le_one⟩

theorem isUnitBounded_one {Ω : Type*} :
    IsUnitBounded (fun _ : Ω => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, fun _ => le_rfl⟩

def unitCubeSet (Ω : Type*) : Set (Ω → ℝ) :=
  {g | IsUnitBounded g}

theorem unitCubeSet_eq_Icc (Ω : Type*) :
    unitCubeSet Ω =
      Set.Icc (fun _ : Ω => (0 : ℝ)) (fun _ => 1) := by
  ext g
  simp [unitCubeSet, IsUnitBounded, Set.mem_Icc, Pi.le_def]

theorem unitCubeSet_convex (Ω : Type*) :
    Convex ℝ (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact convex_Icc _ _

theorem unitCubeSet_compact (Ω : Type*) :
    IsCompact (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact isCompact_Icc

theorem unitCubeSet_closed (Ω : Type*) :
    IsClosed (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact isClosed_Icc

theorem unitCubeSet_nonempty (Ω : Type*) :
    (unitCubeSet Ω).Nonempty :=
  ⟨fun _ => 0, isUnitBounded_zero⟩

noncomputable def finitePairingLinearMap
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := finitePairing f q
  map_add' f g := finitePairing_add_left f g q
  map_smul' c f := by
    simpa [smul_eq_mul] using finitePairing_smul_left c f q

noncomputable def finitePairingCLM
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] ℝ :=
  (finitePairingLinearMap q).toContinuousLinearMap

@[simp]
theorem finitePairingCLM_apply
    {Ω : Type*} [Fintype Ω] (q f : Ω → ℝ) :
    finitePairingCLM q f = finitePairing f q :=
  rfl

noncomputable def finiteTestProfile
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] (τ → ℝ) :=
  ContinuousLinearMap.pi (fun t => finitePairingCLM (q t))

@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl

def profileErrorSet (τ : Type*) (ε : ℝ) : Set (τ → ℝ) :=
  Set.Icc (fun _ : τ => -ε) (fun _ => ε)

theorem mem_profileErrorSet_iff
    {τ : Type*} {ε : ℝ} {e : τ → ℝ} :
    e ∈ profileErrorSet τ ε ↔ ∀ t, |e t| ≤ ε := by
  constructor
  · rintro ⟨hlower, hupper⟩ t
    exact abs_le.mpr ⟨hlower t, hupper t⟩
  · intro h
    exact
      ⟨fun t => (abs_le.mp (h t)).1,
        fun t => (abs_le.mp (h t)).2⟩

theorem profileErrorSet_convex (τ : Type*) (ε : ℝ) :
    Convex ℝ (profileErrorSet τ ε) :=
  convex_Icc _ _

theorem profileErrorSet_compact
    (τ : Type*) (ε : ℝ) :
    IsCompact (profileErrorSet τ ε) :=
  isCompact_Icc

theorem profileErrorSet_closed (τ : Type*) (ε : ℝ) :
    IsClosed (profileErrorSet τ ε) :=
  isClosed_Icc

theorem profileErrorSet_nonempty
    (τ : Type*) {ε : ℝ} (hε : 0 ≤ ε) :
    (profileErrorSet τ ε).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [mem_profileErrorSet_iff]
  intro t
  simpa using hε

noncomputable def denseModelProfileSet
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) : Set (τ → ℝ) :=
  finiteTestProfile q '' unitCubeSet Ω + profileErrorSet τ ε

theorem denseModelProfileSet_convex
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    Convex ℝ (denseModelProfileSet Ω τ q ε) := by
  change Convex ℝ
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    (unitCubeSet_convex Ω).linear_image
      (finiteTestProfile q).toLinearMap |>.add
        (profileErrorSet_convex τ ε)

theorem denseModelProfileSet_compact
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsCompact (denseModelProfileSet Ω τ q ε) := by
  change IsCompact
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    ((unitCubeSet_compact Ω).image
      (finiteTestProfile q).continuous).add
        (profileErrorSet_compact τ ε)

theorem denseModelProfileSet_closed
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsClosed (denseModelProfileSet Ω τ q ε) :=
  (denseModelProfileSet_compact Ω τ q ε).isClosed

theorem denseModelProfileSet_nonempty
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (denseModelProfileSet Ω τ q ε).Nonempty :=
  by
    change
      (finiteTestProfile q '' unitCubeSet Ω +
        profileErrorSet τ ε).Nonempty
    exact
      ((unitCubeSet_nonempty Ω).image
        (finiteTestProfile q)).add
          (profileErrorSet_nonempty τ hε)

def HasFiniteDenseModel
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ g : Ω → ℝ, IsUnitBounded g ∧
    ∀ t, |finitePairing (f - g) (q t)| ≤ ε

theorem hasFiniteDenseModel_iff_profile_mem
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) :
    HasFiniteDenseModel q f ε ↔
      finiteTestProfile q f ∈
        denseModelProfileSet Ω τ q ε := by
  constructor
  · rintro ⟨g, hg, hmatch⟩
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    refine ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      finiteTestProfile q (f - g), ?_, ?_⟩
    · rw [mem_profileErrorSet_iff]
      intro t
      exact hmatch t
    · ext t
      simp only [Pi.add_apply, finiteTestProfile_apply]
      rw [finitePairing_sub_left]
      ring
  · intro hmem
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε at hmem
    rcases hmem with ⟨p, ⟨g, hg, rfl⟩, e, he, hsum⟩
    refine ⟨g, hg, ?_⟩
    rw [mem_profileErrorSet_iff] at he
    intro t
    have ht := congrFun hsum t
    simp only [Pi.add_apply, finiteTestProfile_apply] at ht
    rw [finitePairing_sub_left]
    rw [← ht]
    simpa using he t

theorem exists_finiteDenseModel_separator
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : ¬HasFiniteDenseModel q f ε) :
    ∃ L : StrongDual ℝ (τ → ℝ), L ≠ 0 ∧
      ∀ (g : Ω → ℝ), IsUnitBounded g →
        ∀ e ∈ profileErrorSet τ ε,
          L (finiteTestProfile q g + e) <
            L (finiteTestProfile q f) := by
  have hnotmem :
      finiteTestProfile q f ∉
        denseModelProfileSet Ω τ q ε := by
    simpa [hasFiniteDenseModel_iff_profile_mem] using hfail
  obtain ⟨L, u, hleft, hright⟩ :=
    geometric_hahn_banach_closed_point
      (denseModelProfileSet_convex Ω τ q ε)
      (denseModelProfileSet_closed Ω τ q ε)
      hnotmem
  have hLne : L ≠ 0 := by
    obtain ⟨s, hs⟩ :=
      denseModelProfileSet_nonempty Ω τ q hε
    intro hzero
    have hslt := hleft s hs
    rw [hzero] at hslt hright
    simp only [zero_apply] at hslt hright
    linarith
  refine ⟨L, hLne, ?_⟩
  intro g hg e he
  have hmem :
      finiteTestProfile q g + e ∈
        denseModelProfileSet Ω τ q ε := by
    change
      finiteTestProfile q g + e ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    exact ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      e, he, rfl⟩
  exact (hleft _ hmem).trans hright

noncomputable def dualCoefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (t : τ) : ℝ := by
  classical
  exact L (Pi.single t 1)

theorem dual_apply_eq_sum_coefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (v : τ → ℝ) :
    L v = ∑ t, dualCoefficient L t * v t := by
  classical
  calc
    L v =
        L (∑ t, (v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      rw [← pi_eq_sum_univ' v]
    _ = ∑ t,
        L ((v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      exact map_sum L _ _
    _ = ∑ t, dualCoefficient L t * v t := by
      apply Fintype.sum_congr
      intro t
      rw [map_smul]
      simp [dualCoefficient, mul_comm]

noncomputable def coefficientL1
    {τ : Type*} [Fintype τ] (c : τ → ℝ) : ℝ :=
  ∑ t, |c t|

theorem coefficientL1_nonneg
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    0 ≤ coefficientL1 c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem coefficientL1_eq_zero_iff
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    coefficientL1 c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext t
    have ht : |c t| = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => abs_nonneg (c i))).mp h t
            (Finset.mem_univ t)
    exact abs_eq_zero.mp ht
  · rintro rfl
    simp [coefficientL1]

theorem coefficientL1_smul
    {τ : Type*} [Fintype τ] (a : ℝ) (c : τ → ℝ) :
    coefficientL1 (a • c) = |a| * coefficientL1 c := by
  classical
  simp [coefficientL1, abs_mul, Finset.mul_sum]

theorem coefficientL1_dualCoefficient_pos
    {τ : Type*} [Fintype τ]
    {L : StrongDual ℝ (τ → ℝ)} (hL : L ≠ 0) :
    0 < coefficientL1 (dualCoefficient L) := by
  classical
  have hexists : ∃ t, dualCoefficient L t ≠ 0 := by
    by_contra h
    push Not at h
    apply hL
    ext v
    rw [dual_apply_eq_sum_coefficient]
    simp [h]
  obtain ⟨t, ht⟩ := hexists
  unfold coefficientL1
  exact Finset.sum_pos'
    (fun i _ => abs_nonneg (dualCoefficient L i))
    ⟨t, Finset.mem_univ t, abs_pos.mpr ht⟩

noncomputable def finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) : Ω → ℝ :=
  ∑ t, c t • q t

@[simp]
theorem finiteTestCombination_zero
    {Ω τ : Type*} [Fintype τ] (q : τ → Ω → ℝ) :
    finiteTestCombination q 0 = 0 := by
  classical
  ext x
  simp [finiteTestCombination]

theorem finiteTestCombination_smul_coeff
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (a : ℝ) (c : τ → ℝ) :
    finiteTestCombination q (a • c) =
      a • finiteTestCombination q c := by
  classical
  ext x
  simp [finiteTestCombination, Finset.mul_sum, mul_assoc]

theorem finitePairing_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f (finiteTestCombination q c) =
      ∑ t, c t * finitePairing f (q t) := by
  rw [finiteTestCombination]
  unfold finitePairing mean
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Fintype.sum_congr
  intro t
  calc
    (Finset.univ.expect fun x => f x * (c t * q t x)) =
        Finset.univ.expect (fun x => c t * (f x * q t x)) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = c t *
        Finset.univ.expect (fun x => f x * q t x) := by
      exact (Finset.mul_expect Finset.univ
        (fun x => f x * q t x) (c t)).symm

theorem dual_profile_eq_pairing_combination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ))
    (q : τ → Ω → ℝ) (f : Ω → ℝ) :
    L (finiteTestProfile q f) =
      finitePairing f
        (finiteTestCombination q (dualCoefficient L)) := by
  rw [dual_apply_eq_sum_coefficient,
    finitePairing_finiteTestCombination]
  apply Fintype.sum_congr
  intro t
  rw [finiteTestProfile_apply]

noncomputable def dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) : τ → ℝ :=
  fun t => ε *
    ((SignType.sign (dualCoefficient L t) : SignType) : ℝ)

theorem dualErrorVector_mem
    {τ : Type*} [Fintype τ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (L : StrongDual ℝ (τ → ℝ)) :
    dualErrorVector ε L ∈ profileErrorSet τ ε := by
  rw [mem_profileErrorSet_iff]
  intro t
  rw [dualErrorVector, abs_mul, abs_of_nonneg hε]
  have hsign :
      |((SignType.sign (dualCoefficient L t) : SignType) : ℝ)| ≤ 1 := by
    rw [sign_apply]
    split_ifs <;> norm_num
  simpa using mul_le_mul_of_nonneg_left hsign hε

theorem dual_apply_dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) :
    L (dualErrorVector ε L) =
      ε * coefficientL1 (dualCoefficient L) := by
  rw [dual_apply_eq_sum_coefficient]
  calc
    (∑ t, dualCoefficient L t * dualErrorVector ε L t) =
        ∑ t, ε * |dualCoefficient L t| := by
      apply Fintype.sum_congr
      intro t
      rw [dualErrorVector]
      rw [← self_mul_sign (dualCoefficient L t)]
      ring
    _ = ε * coefficientL1 (dualCoefficient L) := by
      rw [coefficientL1, Finset.mul_sum]

def positivePart {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => max (q x) 0

@[simp]
theorem positivePart_apply
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positivePart q x = max (q x) 0 :=
  rfl

theorem positivePart_nonneg
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    0 ≤ positivePart q x :=
  le_max_right _ _

theorem le_positivePart
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    q x ≤ positivePart q x :=
  le_max_left _ _

@[simp]
theorem positivePart_of_nonneg
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : 0 ≤ q x) :
    positivePart q x = q x :=
  max_eq_left hx

@[simp]
theorem positivePart_of_nonpos
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : q x ≤ 0) :
    positivePart q x = 0 :=
  max_eq_right hx

@[simp]
theorem positivePart_zero {Ω : Type*} :
    positivePart (0 : Ω → ℝ) = 0 := by
  ext x
  simp [positivePart]

theorem positivePart_smul_of_nonneg
    {Ω : Type*} {a : ℝ} (ha : 0 ≤ a) (q : Ω → ℝ) :
    positivePart (a • q) = a • positivePart q := by
  ext x
  simp only [positivePart, Pi.smul_apply, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ ha, mul_zero]

noncomputable def positiveSupportIndicator
    {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => if 0 ≤ q x then 1 else 0

theorem positiveSupportIndicator_unitBounded
    {Ω : Type*} (q : Ω → ℝ) :
    IsUnitBounded (positiveSupportIndicator q) := by
  constructor <;> intro x <;>
    simp only [positiveSupportIndicator] <;>
    split <;> norm_num

@[simp]
theorem positiveSupportIndicator_mul
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positiveSupportIndicator q x * q x =
      positivePart q x := by
  by_cases hx : 0 ≤ q x
  · simp [positiveSupportIndicator, positivePart, hx]
  · have hx' : q x ≤ 0 := le_of_not_ge hx
    simp [positiveSupportIndicator, positivePart, hx, hx']

theorem finitePairing_positiveSupportIndicator
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (positiveSupportIndicator q) q =
      mean (positivePart q) := by
  apply congrArg mean
  funext x
  exact positiveSupportIndicator_mul q x

theorem finitePairing_le_mean_positivePart
    {Ω : Type*} [Fintype Ω]
    {g q : Ω → ℝ} (hg : IsUnitBounded g) :
    finitePairing g q ≤ mean (positivePart q) := by
  apply mean_mono
  intro x
  by_cases hx : 0 ≤ q x
  · rw [positivePart_of_nonneg hx]
    exact mul_le_of_le_one_left hx (hg.le_one x)
  · rw [positivePart_of_nonpos (le_of_not_ge hx)]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hg.nonneg x) (le_of_not_ge hx)

theorem finitePairing_le_majorant_positivePart
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x) :
    finitePairing f q ≤ finitePairing ν (positivePart q) := by
  apply mean_mono
  intro x
  by_cases hx : 0 ≤ q x
  · rw [positivePart_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right (hfν x) hx
  · rw [positivePart_of_nonpos (le_of_not_ge hx), mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hf0 x) (le_of_not_ge hx)

@[simp]
theorem finitePairing_one_left
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (fun _ : Ω => (1 : ℝ)) q = mean q := by
  simp [finitePairing]

theorem majorant_positivePart_correlation_of_separates_unitCube
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ} {δ : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hsep :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g q + δ < finitePairing f q) :
    δ < finitePairing (ν - fun _ => 1) (positivePart q) := by
  have hsupport := hsep (positiveSupportIndicator q)
    (positiveSupportIndicator_unitBounded q)
  rw [finitePairing_positiveSupportIndicator] at hsupport
  have hmajorant :
      finitePairing f q ≤ finitePairing ν (positivePart q) :=
    finitePairing_le_majorant_positivePart
      (q := q) hf0 hfν
  rw [finitePairing_sub_left, finitePairing_one_left]
  linarith

def HasPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ,
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤
      ε * coefficientL1 c

def HasNormalizedPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ, coefficientL1 c = 1 →
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤ ε

theorem hasPositivePartCorrelationBound_of_normalized
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ)
    (h :
      HasNormalizedPositivePartCorrelationBound q ν ε) :
    HasPositivePartCorrelationBound q ν ε := by
  intro c
  by_cases hc : coefficientL1 c = 0
  · have hc0 : c = 0 :=
      (coefficientL1_eq_zero_iff c).mp hc
    subst c
    rw [hc]
    simp [finitePairing, positivePart]
  · have hcpos : 0 < coefficientL1 c :=
      lt_of_le_of_ne (coefficientL1_nonneg c) (Ne.symm hc)
    let A := coefficientL1 c
    let c' : τ → ℝ := A⁻¹ • c
    have hApos : 0 < A := hcpos
    have hc'L1 : coefficientL1 c' = 1 := by
      change coefficientL1 (A⁻¹ • c) = 1
      rw [coefficientL1_smul, abs_of_pos (inv_pos.mpr hApos)]
      exact inv_mul_cancel₀ hApos.ne'
    have hnormalized := h c' hc'L1
    have hcombination :
        finiteTestCombination q c' =
          A⁻¹ • finiteTestCombination q c := by
      exact finiteTestCombination_smul_coeff q A⁻¹ c
    rw [hcombination,
      positivePart_smul_of_nonneg (inv_nonneg.mpr hApos.le),
      finitePairing_smul_right] at hnormalized
    have hmul :=
      mul_le_mul_of_nonneg_left hnormalized hApos.le
    rw [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] at hmul
    simpa [A, mul_comm] using hmul

theorem hasFiniteDenseModel_of_positivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {f ν : Ω → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo : HasPositivePartCorrelationBound q ν ε) :
    HasFiniteDenseModel q f ε := by
  by_contra hfail
  obtain ⟨L, _hL, hsep⟩ :=
    exists_finiteDenseModel_separator q f hε hfail
  have hsepPair :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g
            (finiteTestCombination q (dualCoefficient L)) +
              ε * coefficientL1 (dualCoefficient L) <
          finitePairing f
            (finiteTestCombination q (dualCoefficient L)) := by
    intro g hg
    have h := hsep g hg (dualErrorVector ε L)
      (dualErrorVector_mem hε L)
    rw [map_add, dual_profile_eq_pairing_combination,
      dual_apply_dualErrorVector,
      dual_profile_eq_pairing_combination] at h
    exact h
  have hpositive :=
    majorant_positivePart_correlation_of_separates_unitCube
      hf0 hfν hsepPair
  exact (not_lt_of_ge (hpseudo (dualCoefficient L))) hpositive

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def testMonomial
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) : Ω → ℝ :=
  fun x => ∏ i, q (s i) x

@[simp]
theorem testMonomial_apply
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) (x : Ω) :
    testMonomial q s x = ∏ i, q (s i) x :=
  rfl

noncomputable def polynomialCoefficientL1 (p : ℝ[X]) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

theorem polynomialCoefficientL1_nonneg (p : ℝ[X]) :
    0 ≤ polynomialCoefficientL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

theorem finitePairing_finset_sum_right
    {Ω κ : Type*} [Fintype Ω]
    (f : Ω → ℝ) (s : Finset κ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i ∈ s, q i x) =
      ∑ i ∈ s, finitePairing f (q i) := by
  classical
  unfold finitePairing mean
  calc
    (𝔼 x, f x * ∑ i ∈ s, q i x) =
        𝔼 x, ∑ i ∈ s, f x * q i x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, 𝔼 x, f x * q i x := by
      exact Finset.expect_sum_comm Finset.univ s _

theorem finitePairing_fintype_sum_right
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (f : Ω → ℝ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i, q i x) =
      ∑ i, finitePairing f (q i) := by
  simpa using finitePairing_finset_sum_right f Finset.univ q

theorem finiteTestCombination_pow_eq_sum_monomials
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ)
    (n : ℕ) (x : Ω) :
    (finiteTestCombination q c x) ^ n =
      ∑ s : Fin n → τ,
        (∏ i, c (s i)) * testMonomial q s x := by
  classical
  rw [finiteTestCombination_apply, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.prod_mul_distrib]
  rfl

theorem polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (p : ℝ[X]) (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    p.eval (finiteTestCombination q c x) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            testMonomial q s x := by
  classical
  rw [Polynomial.eval_eq_sum]
  change
    (∑ n ∈ p.support,
      p.coeff n * (finiteTestCombination q c x) ^ n) = _
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteTestCombination_pow_eq_sum_monomials,
    Finset.mul_sum]
  apply Fintype.sum_congr
  intro s
  ring

theorem finitePairing_polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (p : ℝ[X])
    (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f
        (fun x => p.eval (finiteTestCombination q c x)) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing f (testMonomial q s) := by
  classical
  have heval :
      (fun x => p.eval (finiteTestCombination q c x)) =
        fun x => ∑ n ∈ p.support,
          ∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              testMonomial q s x := by
    funext x
    exact polynomial_eval_finiteTestCombination p q c x
  rw [heval, finitePairing_finset_sum_right]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finitePairing_fintype_sum_right]
  apply Fintype.sum_congr
  intro s
  change
    finitePairing f
        ((p.coeff n * ∏ i, c (s i)) • testMonomial q s) =
      _
  exact
    finitePairing_smul_right
      (p.coeff n * ∏ i, c (s i)) f (testMonomial q s)

theorem sum_abs_coefficientMonomial
    {τ : Type*} [Fintype τ]
    (c : τ → ℝ) (n : ℕ) :
    ∑ s : Fin n → τ, |∏ i, c (s i)| =
      coefficientL1 c ^ n := by
  classical
  unfold coefficientL1
  rw [Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.abs_prod]

def HasMonomialCorrelationBound
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ)
    (d : ℕ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d → ∀ s : Fin n → τ,
    |finitePairing (ν - fun _ => 1) (testMonomial q s)| ≤ η

theorem abs_finitePairing_polynomial_eval_le
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    {η : ℝ} (p : ℝ[X]) (c : τ → ℝ)
    (hc : coefficientL1 c = 1)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    |finitePairing (ν - fun _ => 1)
        (fun x => p.eval (finiteTestCombination q c x))| ≤
      polynomialCoefficientL1 p * η := by
  classical
  rw [finitePairing_polynomial_eval_finiteTestCombination]
  calc
    |∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing (ν - fun _ => 1)
              (testMonomial q s)| ≤
        ∑ n ∈ p.support,
          |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * η := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| ≤
            ∑ s : Fin n → τ,
              |(p.coeff n * ∏ i, c (s i)) *
                finitePairing (ν - fun _ => 1)
                  (testMonomial q s)| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s : Fin n → τ,
              |p.coeff n| * |∏ i, c (s i)| * η := by
          apply Finset.sum_le_sum
          intro s hs
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hmono n
              (Polynomial.le_natDegree_of_mem_supp n hn) s)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |p.coeff n| *
              (∑ s : Fin n → τ, |∏ i, c (s i)|) * η := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = |p.coeff n| * η := by
          rw [sum_abs_coefficientMonomial, hc, one_pow, mul_one]
    _ = polynomialCoefficientL1 p * η := by
      rw [polynomialCoefficientL1, Finset.sum_mul]

def IsUnitBoundedTestFamily
    {Ω τ : Type*} (q : τ → Ω → ℝ) : Prop :=
  ∀ t, IsUnitBounded (q t)

theorem abs_finiteTestCombination_le_coefficientL1
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    (c : τ → ℝ) (x : Ω) :
    |finiteTestCombination q c x| ≤ coefficientL1 c := by
  classical
  rw [finiteTestCombination_apply]
  calc
    |∑ t, c t * q t x| ≤ ∑ t, |c t * q t x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, |c t| := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have habs : |q t x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [(hq t).nonneg x]
        · exact (hq t).le_one x
      exact mul_le_of_le_one_right (abs_nonneg (c t)) habs
    _ = coefficientL1 c := by
      rfl

theorem finiteTestCombination_mem_unitInterval
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    finiteTestCombination q c x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, ← abs_le]
  simpa [hc] using
    abs_finiteTestCombination_le_coefficientL1 hq c x

def ApproximatesPositivePartOnUnitInterval
    (p : ℝ[X]) (δ : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |p.eval x - max x 0| ≤ δ

theorem exists_polynomial_approximating_positivePart
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℝ[X], ApproximatesPositivePartOnUnitInterval p δ := by
  have hcontinuous :
      ContinuousOn (fun x : ℝ => max x 0)
        (Set.Icc (-1 : ℝ) 1) :=
    (continuous_id.max continuous_const).continuousOn
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      (-1 : ℝ) 1 (fun x : ℝ => max x 0)
      hcontinuous δ hδ
  exact ⟨p, fun x hx => (hp x hx).le⟩

theorem polynomial_eval_approximates_positivePart_combination
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ : ℝ}
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    |p.eval (finiteTestCombination q c x) -
        positivePart (finiteTestCombination q c) x| ≤ δ := by
  exact hp _ (finiteTestCombination_mem_unitInterval hq hc x)

theorem abs_finitePairing_le_mul_mean_abs
    {Ω : Type*} [Fintype Ω]
    (f e : Ω → ℝ) {δ : ℝ}
    (he : ∀ x, |e x| ≤ δ) :
    |finitePairing f e| ≤ δ * mean (fun x => |f x|) := by
  calc
    |finitePairing f e| ≤ mean (fun x => |f x * e x|) := by
      unfold finitePairing mean
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x => δ * |f x|) := by
      apply mean_mono
      intro x
      rw [abs_mul]
      have hmul :=
        mul_le_mul_of_nonneg_left (he x) (abs_nonneg (f x))
      simpa [mul_comm] using hmul
    _ = δ * mean (fun x => |f x|) :=
      mean_smul δ _

noncomputable def centeredAbsoluteMean
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) : ℝ :=
  mean fun x => |ν x - 1|

theorem centeredAbsoluteMean_nonneg
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) :
    0 ≤ centeredAbsoluteMean ν :=
  mean_nonneg fun _ => abs_nonneg _

theorem centeredAbsoluteMean_le_mean_add_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    centeredAbsoluteMean ν ≤ mean ν + 1 := by
  unfold centeredAbsoluteMean
  calc
    mean (fun x => |ν x - 1|) ≤
        mean (fun x => ν x + 1) := by
      apply mean_mono
      intro x
      rw [abs_le]
      constructor <;> linarith [hν x]
    _ = mean ν + mean (fun _ : Ω => (1 : ℝ)) :=
      mean_add _ _
    _ = mean ν + 1 := by
      rw [mean_const]

theorem hasNormalizedPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasNormalizedPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) := by
  intro c hc
  let Q := finiteTestCombination q c
  let P : Ω → ℝ := fun x => p.eval (Q x)
  have hpoly :
      finitePairing (ν - fun _ => 1) P ≤
        polynomialCoefficientL1 p * η := by
    exact le_trans (le_abs_self _) <|
      abs_finitePairing_polynomial_eval_le p c hc hmono
  have hpoint :
      ∀ x, |positivePart Q x - P x| ≤ δ := by
    intro x
    have hx :=
      polynomial_eval_approximates_positivePart_combination
        hq hp hc x
    simpa [Q, P, abs_sub_comm] using hx
  have herr0 :
      |finitePairing (ν - fun _ => 1)
        (positivePart Q - P)| ≤
          δ * centeredAbsoluteMean ν := by
    have hbase :=
      abs_finitePairing_le_mul_mean_abs
        (ν - fun _ => 1) (positivePart Q - P)
        (by
          intro x
          simpa using hpoint x)
    have hcentered :
        (fun x =>
          |(ν - (fun _ : Ω => (1 : ℝ))) x|) =
          (fun x => |ν x - 1|) := by
      funext x
      rfl
    rw [hcentered] at hbase
    exact hbase
  have herr :
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤ δ * M := by
    calc
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤
          |finitePairing (ν - fun _ => 1)
            (positivePart Q - P)| :=
        le_abs_self _
      _ ≤ δ * centeredAbsoluteMean ν := herr0
      _ ≤ δ * M :=
        mul_le_mul_of_nonneg_left hM hδ
  have hsplit :
      finitePairing (ν - fun _ => 1) (positivePart Q) =
        finitePairing (ν - fun _ => 1) P +
          finitePairing (ν - fun _ => 1)
            (positivePart Q - P) := by
    rw [← finitePairing_add_right]
    congr 1
    funext x
    simp
  rw [hsplit]
  exact add_le_add hpoly herr

theorem hasPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) :=
  hasPositivePartCorrelationBound_of_normalized q ν _
    (hasNormalizedPositivePartCorrelationBound_of_polynomial
      hq hδ hp hM hmono)

end Erdos3.FixedDensity

end

end OAI
