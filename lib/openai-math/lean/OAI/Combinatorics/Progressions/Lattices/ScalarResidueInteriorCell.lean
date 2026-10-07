import Mathlib.Data.Int.Interval
import OAI.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
import OAI.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def paddedIntegerPoint {I : Type*} (L P : ℕ) (x : I → Fin P) : I → ℤ :=
  fun i => (x i).val - L

theorem paddedIntegerPoint_injective {I : Type*} (L P : ℕ) :
    Function.Injective (paddedIntegerPoint (I := I) L P) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp only [paddedIntegerPoint] at hi
  omega

theorem paddedIntegerPoint_covers {I : Type*} {L P : ℕ} (hP : 2 * L ≤ P)
    (k : I → ℤ) (hk : ∀ i, -(L : ℤ) ≤ k i ∧ k i < L) :
    ∃ x : I → Fin P, paddedIntegerPoint L P x = k := by
  let x : I → Fin P := fun i => ⟨(k i + L).toNat, by
    have := hk i
    omega⟩
  refine ⟨x, ?_⟩
  funext i
  have := hk i
  dsimp only [paddedIntegerPoint, x]
  omega

theorem sum_eq_sum_of_cover_and_support {X Y V : Type*} [Fintype X]
    [DecidableEq Y] [AddCommMonoid V] (S : Finset Y) (e : X → Y)
    (he : Function.Injective e) (hcover : ∀ y ∈ S, ∃ x, e x = y)
    (F : Y → V) (hsupport : ∀ y, y ∉ S → F y = 0) :
    (∑ y ∈ S, F y) = ∑ x, F (e x) := by
  classical
  have hsub : S ⊆ Finset.univ.image e := by
    intro y hy
    obtain ⟨x, hx⟩ := hcover y hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
  calc
    _ = ∑ y ∈ Finset.univ.image e, F y :=
      Finset.sum_subset hsub (fun y _ hy => hsupport y hy)
    _ = _ := Finset.sum_image (fun _ _ _ _ h => he h)

theorem expect_eq_card_ratio_mul_expect {X Y : Type*} [Fintype X] [Nonempty X]
    [DecidableEq Y] (S : Finset Y) (e : X → Y) (he : Function.Injective e)
    (hcover : ∀ y ∈ S, ∃ x, e x = y) (F : Y → ℂ)
    (hsupport : ∀ y, y ∉ S → F y = 0) :
    (𝔼 y ∈ S, F y) = ((Fintype.card X : ℂ) / S.card) * 𝔼 x, F (e x) := by
  have hc : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    sum_eq_sum_of_cover_and_support S e he hcover F hsupport]
  field_simp

end Erdos3

end

section

namespace Erdos3

noncomputable def residueCellLength (δ : ℝ) (L M : ℕ) : ℕ := ⌊δ * L / M⌋₊

def residueCellCount (L N : ℕ) : ℕ := 2 * L / N + 1

theorem residueCellCount_pos (L N : ℕ) : 0 < residueCellCount L N := by
  exact Nat.succ_pos _

theorem residueCellCount_padding {L N : ℕ} (hN : 0 < N) (hNL : N ≤ L) :
    2 * L ≤ residueCellCount L N * N ∧ residueCellCount L N * N ≤ 3 * L := by
  have hdiv := Nat.div_add_mod (2 * L) N
  have hmod := Nat.mod_lt (2 * L) hN
  unfold residueCellCount
  constructor
  · calc
      2 * L = N * (2 * L / N) + 2 * L % N := hdiv.symm
      _ ≤ N * (2 * L / N) + N := Nat.add_le_add_left hmod.le _
      _ = (2 * L / N + 1) * N := by ring
  · have hprod : N * (2 * L / N) ≤ 2 * L := by omega
    calc
      (2 * L / N + 1) * N = N * (2 * L / N) + N := by ring
      _ ≤ 2 * L + N := Nat.add_le_add_right hprod _
      _ ≤ 3 * L := by omega

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

theorem residueCellLength_stride_mesh {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) {m : ℕ} (hm : m ≤ M) :
    |(m : ℝ) / L| * residueCellLength δ L M ≤ δ := by
  rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) / L)]
  apply le_trans _ (residueCellLength_bounds hδ hδ1 hL hM hlarge).2.2.2
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)) (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def scalarResidueGridPoint {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (k : Option I → ℤ) : Option I → ℤ := fun i => (r i).val + (m i : ℤ)*k i

noncomputable def scalarResidueGridOffset {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => -((r i).val : ℝ) / m i

noncomputable def scalarResidueGridScale {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (L : ℝ) / m i

theorem scalarResidueGridScale_pos {I : Type*} {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (hm : ∀ i, 0 < m i) (i : Option I) : 0 < scalarResidueGridScale L m i := by
  unfold scalarResidueGridScale
  exact div_pos (by exact_mod_cast hL) (by exact_mod_cast hm i)

theorem scalarResidueGrid_normalized {I : Type*} [Fintype I] {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) (k : Option I → ℤ) :
    rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k =
      fun i => (scalarResidueGridPoint m r k i : ℝ) / L := by
  funext i
  have hmi : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
  simp only [rectangularLatticePoint, scalarResidueGridOffset, scalarResidueGridScale,
    scalarResidueGridPoint, Int.cast_add, Int.cast_natCast, Int.cast_mul]
  field_simp
  ring

theorem integerScalarCube_iff_normalized {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (z : Option I → ℤ) :
    IntegerScalarCube L z ↔ (fun i => (z i : ℝ) / L) ∈ halfOpenScalarCubeDomain I := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have he (t : Finset I) : scalarCubeValue (fun i => (z i : ℝ) / L) t = (integerScalarCubeValue z t : ℝ) / L := by
    simp only [scalarCubeValue_formula, integerScalarCubeValue, Int.cast_add, Int.cast_sum, add_div, Finset.sum_div]
  constructor
  · intro hz t
    rw [he]
    constructor
    · exact div_nonneg (by exact_mod_cast (hz t).1) hLp.le
    · exact (div_lt_one hLp).mpr (by exact_mod_cast (hz t).2)
  · intro hz t
    have ht := hz t
    rw [he] at ht
    constructor
    · have hh : (0 : ℝ) ≤ (integerScalarCubeValue z t : ℝ) := by
        simpa only [zero_mul] using (le_div_iff₀ hLp).mp ht.1
      exact_mod_cast hh
    · exact_mod_cast (div_lt_one hLp).mp ht.2

theorem scalarResidueGridPoint_residue {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (k : Option I → ℤ) (i : Option I) :
    (scalarResidueGridPoint m r k i : ZMod (m i)) = r i := by
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp [scalarResidueGridPoint]

theorem scalarResidueGridPoint_injective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) : Function.Injective (scalarResidueGridPoint m r) := by
  intro k l h
  funext i
  have hh := congrFun h i
  have hmi : (m i : ℤ) ≠ 0 := by exact_mod_cast (hm i).ne'
  exact mul_left_cancel₀ hmi (add_left_cancel hh)

theorem scalarResidueGridPoint_surjective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (z : Option I → ℤ)
    (hz : ∀ i, (z i : ZMod (m i)) = r i) : ∃ k, scalarResidueGridPoint m r k = z := by
  have hi (i : Option I) : ∃ k : ℤ, z i = (r i).val + (m i : ℤ)*k := by
    let : NeZero (m i) := ⟨(hm i).ne'⟩
    have he : (((r i).val : ℤ) : ZMod (m i)) = (z i : ZMod (m i)) := by simpa using (hz i).symm
    obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (z i) (m i)).mp he
    exact ⟨k, by linarith⟩
  choose k hk using hi
  exact ⟨k, funext (fun i => (hk i).symm)⟩

noncomputable def scalarCubeResidueGridEquiv (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) :
    ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) ≃
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let F : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) →
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := fun k => by
    have hk := (mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k.val).mp k.property
    rw [scalarResidueGrid_normalized hL m r hm] at hk
    have hc := (integerScalarCube_iff_normalized hL _).mpr hk
    let z : IntegerScalarCubeBox I L := fun i => ⟨scalarResidueGridPoint m r k.val i,
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hc i).1.le, (integerScalarCube_coordinates hc i).2⟩⟩
    exact ⟨z, Finset.mem_inter.mpr ⟨(mem_integerScalarCubeSet L z).mpr hc,
      (mem_scalarCubeResidueSet L m r z).mpr (scalarResidueGridPoint_residue m r hm k.val)⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro k l h
    apply Subtype.ext
    apply scalarResidueGridPoint_injective m r hm
    exact funext (fun i => congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h)
  · intro z
    obtain ⟨k,hk⟩ := scalarResidueGridPoint_surjective m r hm (fun i => (z.val i : ℤ))
      ((mem_scalarCubeResidueSet L m r z.val).mp (Finset.mem_inter.mp z.property).2)
    have hc := (mem_integerScalarCubeSet L z.val).mp (Finset.mem_inter.mp z.property).1
    have hmem : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) := by
      rw [mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm), scalarResidueGrid_normalized hL m r hm, hk]
      exact (integerScalarCube_iff_normalized hL _).mp hc
    refine ⟨⟨k,hmem⟩, ?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun hk i

theorem scalarCubeResidueGridEquiv_apply (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) (i : Option I) :
    (((scalarCubeResidueGridEquiv I L hL m r hm k).val i : ℤ)) = scalarResidueGridPoint m r k.val i := rfl

theorem scalarCubeResidueWeights_grid_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (φ : (Option I → ℝ) → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
      (fun z => φ (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  rw [scalarCubeResidueWeights_mean]
  let e := scalarCubeResidueGridEquiv I L hL m r hm
  have he (k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :
      rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val =
        fun i => ((e k).val i : ℝ) / L := by
    rw [scalarResidueGrid_normalized hL m r hm]
    funext i
    rfl
  calc
    _ = 𝔼 k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val) := by
      symm
      exact Fintype.expect_equiv e _ _ (fun k => congrArg φ (he k))
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
      congr 1
      exact Finset.sum_coe_sort _ (fun k =>
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

theorem scalarCubeResidueWeights_grid_complexMean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (F : (Option I → ℝ) → ℂ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => F (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        F (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re, Complex.re_expect]
    exact scalarCubeResidueWeights_grid_mean I L M hL m r hm hmM hsize (fun x => (F x).re)
  · rw [FiniteProbabilityWeights.complexMean_im, Complex.im_expect]
    exact scalarCubeResidueWeights_grid_mean I L M hL m r hm hmM hsize (fun x => (F x).im)

end Erdos3

end

section

namespace Erdos3

theorem residue_index_bounds {L m : ℕ} (hm : 0 < m) (r : ZMod m) (k : ℤ)
    (hk : -(L : ℤ) < (r.val : ℤ) + m * k ∧ (r.val : ℤ) + m * k < L) :
    -(L : ℤ) ≤ k ∧ k < L := by
  let : NeZero m := ⟨hm.ne'⟩
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hr : (r.val : ℤ) < m := by exact_mod_cast ZMod.val_lt r
  have hr0 : (0 : ℤ) ≤ r.val := by positivity
  constructor
  · by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show k ≤ -(L : ℤ) - 1 by omega) (by positivity : (0 : ℤ) ≤ m)
    have hsize := mul_le_mul_of_nonneg_right hm' (by positivity : (0 : ℤ) ≤ L)
    nlinarith [hk.1]
  · by_contra! h
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℤ) ≤ m)
    have hsize := mul_le_mul_of_nonneg_right hm' (by positivity : (0 : ℤ) ≤ L)
    nlinarith [hk.2]

theorem scalarCubeResidueGrid_index_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (k : Option I → ℤ)
    (hk : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) :
    ∀ i, -(L : ℤ) ≤ k i ∧ k i < L := by
  have hx := (mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k).mp hk
  rw [scalarResidueGrid_normalized hL m r hm] at hx
  have hc := (integerScalarCube_iff_normalized hL _).mpr hx
  intro i
  exact residue_index_bounds (hm i) (r i) (k i) (integerScalarCube_coordinates hc i)

theorem scalarCubeResidueGrid_padded_cover {I : Type*} [Fintype I] [DecidableEq I]
    {L P : ℕ} (hL : 0 < L) (hP : 2 * L ≤ P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (k : Option I → ℤ)
    (hk : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) :
    ∃ x : Option I → Fin P, paddedIntegerPoint L P x = k :=
  paddedIntegerPoint_covers hP k (scalarCubeResidueGrid_index_bounds hL m r hm k hk)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeResidueWeights_riemann (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I))
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
        (fun z => φ (fun i => (z i : ℝ) / L)) - ∫ x, φ x ∂scalarCubeMeasure I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) * ((M : ℝ)/L) := by
  rw [scalarCubeResidueWeights_grid_mean]
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hML : M ≤ L := by nlinarith
  have hδ : (0 : ℝ) ≤ (M : ℝ)/L := by positivity
  have hδ1 : (M : ℝ)/L ≤ 1 := (div_le_one hLp).mpr (by exact_mod_cast hML)
  have hS := scalarResidueGridScale_pos hL m hm
  have hmesh (i : Option I) : 1 / scalarResidueGridScale L m i ≤ (M : ℝ)/L := by
    simp only [scalarResidueGridScale, one_div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmM i) hLp.le
  have hpos := scalarCubeGridHistogram_mass_pos I (scalarResidueGridOffset m r) _ hS hδ hδ1 hmesh hsmall
  exact (scalarCubeGrid_comparison I _ _ hS hδ hδ1 hmesh hpos φ hφ hB hb).trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

noncomputable def paddedResidueOffset {I : Type*} (L : ℕ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => ((r i).val - (m i : ℝ) * L) / L

noncomputable def paddedResidueStep {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (m i : ℝ) / L

theorem paddedResidueCoordinates_eq {I : Type*} [Fintype I] {L P : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (x : Option I → Fin P) :
    rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m)
      (paddedIntegerPoint L P x) =
      fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val := by
  rw [scalarResidueGrid_normalized hL m r hm]
  funext i
  simp only [scalarResidueGridPoint, paddedIntegerPoint, paddedResidueOffset,
    paddedResidueStep, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  ring

theorem scalarCubeResidueGrid_card (I : Type*) [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) :
    (scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)).card =
      ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (scalarCubeResidueGridEquiv I L hL m r hm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarCubeResidueCutoffBudget (I : Type*) [Fintype I] [DecidableEq I]
    (A r : ℝ≥0) (L M : ℕ) : ℝ :=
  scalarCubeBoundaryConstant I * r +
    (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
      scalarCubeCutoffLipschitzConstant I A r) * ((M : ℝ) / L)

theorem scalarCubeResidueCutoff_loss (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {r : ℝ≥0} (hr : 0 < r) :
    (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => 1 - inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ))
        scalarCubeFace (fun i => (z i : ℝ) / L)) ≤
      scalarCubeResidueCutoffBudget I A r L M := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace
  have hLip : LipschitzWith (scalarCubeCutoffLipschitzConstant I A r)
      (fun x => 1 - b x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show (1 - b x) - (1 - b y) = b y - b x by ring, abs_sub_comm]
    exact (scalarCubeBoundaryCutoff_lipschitz I A hA hr).dist_le_mul x y
  have hbound (x : Option I → ℝ) : ‖1 - b x‖ ≤ 1 := by
    have h := inequalityBoundaryCutoff_range (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace x
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
    linarith [h.1]
  have hquad := scalarCubeResidueWeights_riemann I L M hL m res hm hmM hsize hsmall
    (fun x => 1 - b x) hLip zero_le_one hbound
  have hcont := scalarCubeBoundaryCutoff_mass_loss I (show (0 : ℝ) < r from hr)
  have hu := (le_abs_self _).trans hquad
  dsimp only [scalarCubeResidueCutoffBudget]
  dsimp only [b] at hu
  linarith

theorem scalarCubeResidueCutoff_bias (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {r : ℝ≥0} (hr : 0 < r) (F : IntegerScalarCubeBox I L → ℂ)
    (hF : ∀ z, ‖F z‖ ≤ 1) {ζ : ℝ}
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean F‖) :
    ζ - scalarCubeResidueCutoffBudget I A r L M ≤
      ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
        (fun z => (inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ))
          scalarCubeFace (fun i => (z i : ℝ) / L) : ℂ) * F z)‖ :=
  FiniteProbabilityWeights.cutoff_bias_lower _ _ F
    (fun _ => inequalityBoundaryCutoff_range _ _ _) hF hbias
    (scalarCubeResidueCutoff_loss I L M hL m res hm hmM hsize hsmall A hA hr)

end Erdos3

end

section

namespace Erdos3

noncomputable def paddedResidueDensityFactor (I : Type*) [Fintype I] (L P : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : ℝ :=
  (P : ℝ) ^ (Fintype.card I + 1) /
    ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card

noncomputable def paddedResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  2 ^ (Fintype.card I + 1) * scalarCubeResidueDensityCap I M

theorem scalarCubeResidue_card_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  have hcap := scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none))
  have h := scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  rw [integerScalarCubeReference, FiniteProbabilityWeights.uniform_mass] at h
  by_contra! hz
  have hzero : ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card = 0 := by omega
  rw [hzero, Nat.cast_zero, zero_div] at h
  exact (not_le_of_gt (inv_pos.mpr hcap)) h

theorem paddedResidueDensityFactor_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 0 < P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < paddedResidueDensityFactor I L P m r := by
  apply div_pos (pow_pos (by exact_mod_cast hP) _)
  exact_mod_cast scalarCubeResidue_card_pos I L M hL m r hm hmM hsize

theorem paddedResidueDensityFactor_le (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : P ≤ 4 * L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    paddedResidueDensityFactor I L P m r ≤ paddedResidueDensityCap I M := by
  let S := (integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r
  have hS : (0 : ℝ) < S.card := by
    exact_mod_cast scalarCubeResidue_card_pos I L M hL m r hm hmM hsize
  have hcap := scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none))
  have hbase : (0 : ℝ) < (2 * (L : ℝ)) ^ (Fintype.card I + 1) := by positivity
  have h := scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  rw [integerScalarCubeReference, FiniteProbabilityWeights.uniform_mass,
    integerScalarCubeBox_card] at h
  push_cast at h
  have hmass : (2 * (L : ℝ)) ^ (Fintype.card I + 1) ≤
      S.card * scalarCubeResidueDensityCap I M := by
    have hh : 1 / scalarCubeResidueDensityCap I M ≤
        (S.card : ℝ) / (2 * (L : ℝ)) ^ (Fintype.card I + 1) := by
      simpa only [one_div, S] using h
    simpa only [one_mul] using (div_le_div_iff₀ hcap hbase).mp hh
  apply (div_le_iff₀ hS).mpr
  calc
    (P : ℝ) ^ (Fintype.card I + 1) ≤ (2 * (2 * (L : ℝ))) ^ (Fintype.card I + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg P)
        (by exact_mod_cast (show P ≤ 2 * (2 * L) by omega)) _
    _ = 2 ^ (Fintype.card I + 1) * (2 * (L : ℝ)) ^ (Fintype.card I + 1) := mul_pow _ _ _
    _ ≤ 2 ^ (Fintype.card I + 1) * (S.card * scalarCubeResidueDensityCap I M) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = paddedResidueDensityCap I M * S.card := by unfold paddedResidueDensityCap; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_padded_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 2 * L ≤ P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (hw : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (F : (Option I → ℝ) → ℂ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L)) =
      𝔼 x : Option I → Fin P,
        ((paddedResidueDensityFactor I L P m r *
          w (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) : ℝ) : ℂ) *
        F (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) := by
  have hPpos : 0 < P := by omega
  let : Nonempty (Fin P) := ⟨⟨0, hPpos⟩⟩
  let S := scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)
  let f := fun k => (w (rectangularLatticePoint (scalarResidueGridOffset m r)
    (scalarResidueGridScale L m) k) : ℂ) *
    F (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k)
  have hsupport (k) (hk : k ∉ S) : f k = 0 := by
    have hz : w (rectangularLatticePoint (scalarResidueGridOffset m r)
        (scalarResidueGridScale L m) k) = 0 := by
      by_contra h
      exact hk ((mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k).mpr (hw h))
    simp only [f, hz, Complex.ofReal_zero, zero_mul]
  rw [scalarCubeResidueWeights_grid_complexMean I L M hL m r hm hmM hsize
    (fun y => (w y : ℂ) * F y)]
  change (𝔼 k ∈ S, f k) = _
  rw [expect_eq_card_ratio_mul_expect S (paddedIntegerPoint L P)
    (paddedIntegerPoint_injective L P)
    (scalarCubeResidueGrid_padded_cover hL hP m r hm) f hsupport]
  have hfactor : (Fintype.card (Option I → Fin P) : ℂ) / S.card =
      (paddedResidueDensityFactor I L P m r : ℂ) := by
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, S,
      scalarCubeResidueGrid_card I hL m r hm, paddedResidueDensityFactor,
      Nat.cast_pow, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [hfactor, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _
  dsimp only [f]
  rw [paddedResidueCoordinates_eq hL m r hm x, Complex.ofReal_mul, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_padded_bias (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 2 * L ≤ P) (hPupper : P ≤ 4 * L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (hw : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (F : (Option I → ℝ) → ℂ) {ζ : ℝ}
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    ζ / paddedResidueDensityCap I M ≤
      ‖𝔼 x : Option I → Fin P,
        (w (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) : ℂ) *
        F (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val)‖ := by
  have hcap : 0 < paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap
    exact mul_pos (by positivity)
      (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))
  have hfactor := paddedResidueDensityFactor_pos I L M P hL (by omega) m r hm hmM hsize
  have hle := paddedResidueDensityFactor_le I L M P hL hPupper m r hm hmM hsize
  have hlaw := scalarCubeResidueWeights_padded_mean I L M P hL hP m r hm hmM hsize w hw F
  simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_expect] at hlaw
  rw [hlaw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hfactor.le] at hbias
  apply (div_le_iff₀ hcap).mpr
  exact hbias.trans ((mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans_eq (mul_comm _ _))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeResidue_exists_interior_cell (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {r : ℝ≥0} (hr : 0 < r)
    {δ η ζ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hlarge : 2 * (M : ℝ) ≤ δ * L)
    (hmargin : ((Fintype.card I : ℝ) + 1) * δ < r)
    (herror : scalarCubeResidueCutoffBudget I A r L M +
      paddedResidueDensityCap I M * (scalarCubeCutoffLipschitzConstant I A r * δ + η) ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
      (fun z => F (fun i => (z i : ℝ) / L))‖) :
    ∃ N K : ℕ, 0 < N ∧ N ≤ L ∧ δ * L / (2 * M) ≤ (N : ℝ) ∧ 0 < K ∧
      ∃ k : Option I → Fin K,
        (∀ t : Option I → Fin N,
          (fun i => progressionCellCorner (fun _ => N) (paddedResidueOffset L m res)
            (paddedResidueStep L m) k i + paddedResidueStep L m i * (t i).val) ∈ scalarCubeDomain I) ∧
        η ≤ ‖𝔼 t : Option I → Fin N,
          F (fun i => progressionCellCorner (fun _ => N) (paddedResidueOffset L m res)
            (paddedResidueStep L m) k i + paddedResidueStep L m i * (t i).val)‖ := by
  let N := residueCellLength δ L M
  let K := residueCellCount L N
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hN := residueCellLength_bounds hδ hδ1 hL hM hlarge
  have hK : 0 < K := residueCellCount_pos L N
  have hP : 2 * L ≤ K * N ∧ K * N ≤ 3 * L := residueCellCount_padding hN.1 hN.2.1
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace
  let Q := scalarCubeCutoffLipschitzConstant I A r
  let B := paddedResidueDensityCap I M
  have hB : 0 < B := by
    exact mul_pos (by positivity) (scalarCubeResidueDensityCap_pos I M hM)
  have hb : Function.support b ⊆ halfOpenScalarCubeDomain I := by
    intro x hx
    exact scalarCubeDomain_subset_halfOpen I
      (scalarCubeBoundaryCutoff_tsupport_domain I (show (0 : ℝ) < r from hr) (subset_closure hx))
  have hcut := scalarCubeResidueCutoff_bias I L M hL m res hm hmM hsize hsmall A hA hr
    (fun z => F (fun i => (z i : ℝ) / L)) (fun z => hF _) hbias
  have hpad := scalarCubeResidueWeights_padded_bias I L M (K * N) hL hP.1
    (by omega) m res hm hmM hsize b hb F hcut
  have hthreshold : Q * δ + η ≤ (ζ - scalarCubeResidueCutoffBudget I A r L M) / B := by
    apply (le_div_iff₀ hB).mpr
    dsimp only [Q, B]
    nlinarith
  have hpad' := hthreshold.trans hpad
  obtain ⟨k, hinside, hphase⟩ := exists_interior_progression_cell
    (fun _ : Option I => K) (fun _ => N) (fun _ => hK) (fun _ => hN.1)
    (paddedResidueOffset L m res) (paddedResidueStep L m) b (scalarCubeDomain I)
    (scalarCubeBoundaryCutoff_lipschitz I A hA hr) hδ.le zero_lt_one
    (show (Q : ℝ) * δ < Q * δ + η by linarith)
    (fun i => residueCellLength_stride_mesh hδ hδ1 hL hM hlarge (hmM i))
    (fun x => inequalityBoundaryCutoff_range _ _ x)
    (scalarCube_cutoff_safe (show (0 : ℝ) < r from hr) hmargin b Set.Subset.rfl)
    (fun x => F (fun i => paddedResidueOffset L m res i + paddedResidueStep L m i * (x i).val))
    (fun x => hF _) hpad'
  refine ⟨N, K, hN.1, hN.2.1, hN.2.2.1, hK, k, hinside, ?_⟩
  have he (t : Option I → Fin N) := finiteRectangleRefinement_affine
    (fun _ : Option I => K) (fun _ => N) (paddedResidueOffset L m res) (paddedResidueStep L m) k t
  simp only [he, Q, add_sub_cancel_left, div_one] at hphase
  exact hphase

end Erdos3

end

end OAI
