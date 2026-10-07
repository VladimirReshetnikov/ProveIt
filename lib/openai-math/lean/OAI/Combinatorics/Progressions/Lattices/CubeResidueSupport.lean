import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.DeterminantCutoffScale
import OAI.Combinatorics.Progressions.Estimates.FiniteProductDomination
import OAI.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeDomain
import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
import OAI.Combinatorics.Progressions.Probability.BoxCokernelProbability

namespace OAI


namespace Erdos3

open scoped BigOperators

def integerScalarCubeValue {I : Type*} [Fintype I] (x : Option I → ℤ) (t : Finset I) : ℤ :=
  x none + ∑ i ∈ t, x (some i)

def IntegerScalarCube {I : Type*} [Fintype I] (L : ℕ) (x : Option I → ℤ) : Prop :=
  ∀ t : Finset I, 0 ≤ integerScalarCubeValue x t ∧ integerScalarCubeValue x t < L

abbrev IntegerScalarCubeBox (I : Type*) (L : ℕ) :=
  Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)

noncomputable def integerScalarCubeSet (I : Type*) [Fintype I] (L : ℕ) :
    Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => IntegerScalarCube L (fun i => (x i : ℤ)))

theorem mem_integerScalarCubeSet {I : Type*} [Fintype I] (L : ℕ)
    (x : IntegerScalarCubeBox I L) :
    x ∈ integerScalarCubeSet I L ↔ IntegerScalarCube L (fun i => (x i : ℤ)) := by
  classical
  simp [integerScalarCubeSet]

theorem integerScalarCube_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} {x : Option I → ℤ} (hx : IntegerScalarCube L x) (i : Option I) :
    -(L : ℤ) < x i ∧ x i < L := by
  have h0 := hx ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
  cases i with
  | none => omega
  | some i =>
    have h1 := hx {i}
    simp only [integerScalarCubeValue, Finset.sum_singleton] at h1
    omega

theorem integerScalarCubeValue_cast {I : Type*} [Fintype I] [DecidableEq I]
    (x : Option I → ℤ) (t : Finset I) :
    scalarCubeValue (fun i => (x i : ℝ)) t = (integerScalarCubeValue x t : ℝ) := by
  simp [scalarCubeValue, integerScalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]

theorem integerScalarCube_small_positive {I : Type*} [Fintype I] {L H : ℕ}
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) (x : Option I → Fin H) :
    IntegerScalarCube L (fun i => ((x i).val : ℤ)) := by
  intro t
  have ht : t.card ≤ Fintype.card I := Finset.card_le_univ t
  have hx (i : Option I) : (0 : ℤ) ≤ (x i).val ∧ ((x i).val : ℤ) ≤ (H : ℤ) - 1 := by
    exact ⟨Nat.cast_nonneg _, by have := (x i).isLt; omega⟩
  have hsum0 : (0 : ℤ) ≤ ∑ i ∈ t, ((x (some i)).val : ℤ) :=
    Finset.sum_nonneg (fun i _ => (hx (some i)).1)
  have hsum : (∑ i ∈ t, ((x (some i)).val : ℤ)) ≤ (t.card : ℤ) * ((H : ℤ) - 1) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i (_ : i ∈ t) => (hx (some i)).2))
  have hHL' : ((Fintype.card I : ℤ) + 1) * H ≤ L := by exact_mod_cast hHL
  have ht' : (t.card : ℤ) ≤ Fintype.card I := by exact_mod_cast ht
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  dsimp [integerScalarCubeValue]
  constructor
  · exact add_nonneg (hx none).1 hsum0
  · have h0 := (hx none).2
    have hmul := mul_le_mul_of_nonneg_right ht' (sub_nonneg.mpr hH')
    nlinarith [show (0 : ℤ) ≤ Fintype.card I from Nat.cast_nonneg _]

end Erdos3


namespace Erdos3

def integerScalarCubeBoxZero (I : Type*) (L : ℕ) (hL : 0 < L) : IntegerScalarCubeBox I L :=
  fun _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast hL⟩⟩

theorem integerScalarCubeSet_nonempty (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeSet I L).Nonempty := by
  refine ⟨integerScalarCubeBoxZero I L hL, (mem_integerScalarCubeSet L _).mpr ?_⟩
  intro t
  simp only [integerScalarCubeValue, integerScalarCubeBoxZero, Finset.sum_const_zero, add_zero]
  exact ⟨le_rfl, by exact_mod_cast hL⟩

theorem integerScalarCubeBox_card (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) :
    Fintype.card (IntegerScalarCubeBox I L) = (2 * L) ^ (Fintype.card I + 1) := by
  change Fintype.card (Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)) = _
  rw [Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Int.card_Ico]
  congr 1
  omega

theorem integerScalarCubeSet_card_lower (I : Type*) [Fintype I] [DecidableEq I] (L H : ℕ)
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) :
    H ^ (Fintype.card I + 1) ≤ (integerScalarCubeSet I L).card := by
  classical
  have hHL' : H ≤ L := by nlinarith
  let point (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((x i).val : ℤ), Finset.mem_Ico.mpr ⟨by omega, by have := (x i).isLt; omega⟩⟩
  have hpoint (x : Option I → Fin H) : point x ∈ integerScalarCubeSet I L :=
    (mem_integerScalarCubeSet L _).mpr (integerScalarCube_small_positive hH hHL x)
  let e : (Option I → Fin H) → ↥(integerScalarCubeSet I L) := fun x => ⟨point x, hpoint x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥(integerScalarCubeSet I L) => (z.val i : ℤ)) h
    change ((x i).val : ℤ) = ((y i).val : ℤ) at hi
    exact_mod_cast hi
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc

theorem nat_div_half_lower {L n : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    L ≤ 2 * n * (L / n) := by
  have hd : 0 < L / n := Nat.div_pos hL hn
  have hm := Nat.mod_lt L hn
  have he := Nat.div_add_mod L n
  nlinarith


theorem integerScalarCube_iff_supported (q L : ℕ) (x : Option (Fin q) → ℤ) :
    IntegerScalarCube L x ↔ ∀ ω : Fin q → Bool,
      x none + cubeShift (fun i => x (some i)) ω ∈ Set.Ico (0 : ℤ) (L : ℤ) := by
  classical
  constructor
  · intro h ω
    have hx := h (Finset.univ.filter (fun i => ω i))
    simpa only [integerScalarCubeValue, Finset.sum_filter, cubeShift, Set.mem_Ico] using hx
  · intro h t
    have hx := h (fun i => decide (i ∈ t))
    simpa [integerScalarCubeValue, cubeShift] using hx

noncomputable def integerScalarCubeEquiv (q L : ℕ) :
    ↥(integerScalarCubeSet (Fin q) L) ≃ SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := ⟨(fun i => (x.val (some i) : ℤ), (x.val none : ℤ)),
    (integerScalarCube_iff_supported q L _).mp ((mem_integerScalarCubeSet L _).mp x.property)⟩
  invFun p := by
    let v : Option (Fin q) → ℤ := fun | none => p.val.2 | some i => p.val.1 i
    have hv : IntegerScalarCube L v := (integerScalarCube_iff_supported q L v).mpr p.property
    let x : IntegerScalarCubeBox (Fin q) L := fun i =>
      ⟨v i, Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hv i).1.le,
        (integerScalarCube_coordinates hv i).2⟩⟩
    exact ⟨x, (mem_integerScalarCubeSet L x).mpr hv⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl


noncomputable def integerScalarCubeReference (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform _

theorem integerScalarCubeReference_mass (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) =
      ((integerScalarCubeSet I L).card : ℝ) / Fintype.card (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  unfold integerScalarCubeReference
  exact FiniteProbabilityWeights.uniform_mass _

theorem integerScalarCubeReference_mass_pos (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    0 < (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
  exact div_pos (by exact_mod_cast (integerScalarCubeSet_nonempty I L hL).card_pos)
    (by positivity)

noncomputable def integerScalarCubeDensityCap (I : Type*) [Fintype I] : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) : ℝ) ^ (Fintype.card I + 1)

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity

theorem integerScalarCubeReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) :
    (integerScalarCubeDensityCap I)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  let n := Fintype.card I + 1
  let H := L / n
  have hn : 0 < n := by dsimp [n]; omega
  have hH : 0 < H := Nat.div_pos hsize hn
  have hHL : n * H ≤ L := Nat.mul_div_le L n
  have hc := integerScalarCubeSet_card_lower I L H hH hHL
  have hfloor : (L : ℝ) ≤ 2 * (n : ℝ) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hratio : 1 / (4 * (n : ℝ)) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    _ = (1 / (4 * (n : ℝ))) ^ n := by
      simp only [integerScalarCubeDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

noncomputable def integerScalarCubeWeights (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeReference I L hL).condition (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL)

theorem integerScalarCubeWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (x : IntegerScalarCubeBox I L) :
    (integerScalarCubeWeights I L hL).weight x ≤
      integerScalarCubeDensityCap I * (Fintype.card (IntegerScalarCubeBox I L) : ℝ)⁻¹ := by
  classical
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_weight_le (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) ((integerScalarCubeDensityCap I)⁻¹)
    (inv_pos.mpr (integerScalarCubeDensityCap_pos I))
    (integerScalarCubeReference_mass_lower I L hL hsize) x
  simpa only [integerScalarCubeWeights, integerScalarCubeReference, inv_inv] using h


noncomputable def scalarCubeResidueSet (I : Type*) [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => ∀ i, ((x i : ℤ) : ZMod (m i)) = r i)

theorem mem_scalarCubeResidueSet {I : Type*} [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (x : IntegerScalarCubeBox I L) :
    x ∈ scalarCubeResidueSet I L m r ↔ ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  simp only [scalarCubeResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem scalarResiduePoint_bound (m H : ℕ) (hm : 0 < m) (r : ZMod m) (x : Fin H) :
    r.val + m * x.val < m * H := by
  let : NeZero m := ⟨hm.ne'⟩
  have hr := ZMod.val_lt r
  have hx := x.isLt
  nlinarith

theorem scalarResiduePoint_cast (m : ℕ) (hm : 0 < m) (r : ZMod m) (x : ℕ) :
    ((r.val + m * x : ℕ) : ZMod m) = r := by
  let : NeZero m := ⟨hm.ne'⟩
  simp

theorem scalarCubeResidueSet_card_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M H : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hH : 0 < H)
    (hbudget : (Fintype.card I + 1) * (M * H) ≤ L) :
    H ^ (Fintype.card I + 1) ≤ ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  classical
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hML : M * H ≤ L := by nlinarith
  let point (x : Option I → Fin H) (i : Option I) : Fin (M * H) :=
    ⟨(r i).val + m i * (x i).val,
      (scalarResiduePoint_bound (m i) H (hm i) (r i) (x i)).trans_le (Nat.mul_le_mul_right H (hmM i))⟩
  let tuple (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((point x i).val : ℤ), Finset.mem_Ico.mpr
      ⟨by omega, by have := (point x i).isLt; omega⟩⟩
  have hmem (x : Option I → Fin H) :
      tuple x ∈ (integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_integerScalarCubeSet L _).mpr
        (integerScalarCube_small_positive (Nat.mul_pos hM hH) hbudget (point x))
    · apply (mem_scalarCubeResidueSet L m r _).mpr
      intro i
      change ((((r i).val + m i * (x i).val : ℕ) : ℤ) : ZMod (m i)) = r i
      simpa only [Int.cast_natCast] using scalarResiduePoint_cast (m i) (hm i) (r i) (x i).val
  let e : (Option I → Fin H) → ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) :=
    fun x => ⟨tuple x, hmem x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h
    change (((r i).val + m i * (x i).val : ℕ) : ℤ) = (((r i).val + m i * (y i).val : ℕ) : ℤ) at hi
    have hi' : (r i).val + m i * (x i).val = (r i).val + m i * (y i).val := by exact_mod_cast hi
    exact mul_left_cancel₀ (hm i).ne' (Nat.add_left_cancel hi')
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc


open scoped BigOperators Classical

theorem integerScalarCubeWeights_root_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {H : ℕ} (hH : 0 < H) (z : IntegerScalarCubeBox α H)
    (hz : (integerScalarCubeWeights α H hH).weight z ≠ 0) :
    0 ≤ (z none : ℤ) ∧ (z none : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
  have hmem : z ∈ integerScalarCubeSet α H := by
    by_contra hn
    apply hz
    simp only [integerScalarCubeWeights, FiniteProbabilityWeights.condition,
      hn, ite_false, zero_div]
  have hr := ((mem_integerScalarCubeSet H z).mp hmem) ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hr
  exact ⟨hr.1, by omega⟩

theorem integerScalarCubePi_root_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ (z g none : ℤ) ∧ (z g none : ℤ) ≤ ((H g - 1 : ℕ) : ℤ) := by
  apply integerScalarCubeWeights_root_bounds (hH g) (z g)
  change (∏ g, (integerScalarCubeWeights Empty (H g) (hH g)).weight (z g)) ≠ 0 at hz
  exact Finset.prod_ne_zero_iff.mp hz g (Finset.mem_univ g)

theorem integerScalarCubePi_root_real_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ ((z g none : ℤ) : ℝ) ∧ ((z g none : ℤ) : ℝ) ≤ ((H g - 1 : ℕ) : ℝ) := by
  have hb := integerScalarCubePi_root_bounds H hH z hz g
  exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩

theorem affineKernelEndpoint_error {H S step z : ℝ} (lower : ℝ)
    (hH : 0 < H) (hS : 0 < S) (hz0 : 0 ≤ z) (hzH : z ≤ H - 1)
    (hstep : 0 ≤ step) (hwidth : step * (H - 1) ≤ S) :
    |(lower + step * z) / S - (lower + step * (H - 1) * (z / H)) / S| ≤ 1 / H := by
  have he : (lower + step * z) / S - (lower + step * (H - 1) * (z / H)) / S =
      (step * z / S) / H := by
    field_simp
    ring
  rw [he, abs_of_nonneg (div_nonneg (div_nonneg (mul_nonneg hstep hz0) hS.le) hH.le)]
  apply div_le_div_of_nonneg_right _ hH.le
  apply (div_le_one hS).mpr
  exact (mul_le_mul_of_nonneg_left hzH hstep).trans hwidth

theorem affineKernelEndpoint_error_nat {H : ℕ} {S step z : ℝ} (lower : ℝ)
    (hH : 0 < H) (hS : 0 < S) (hz0 : 0 ≤ z) (hzH : z ≤ ((H - 1 : ℕ) : ℝ))
    (hstep : 0 ≤ step) (hwidth : step * ((H - 1 : ℕ) : ℝ) ≤ S) :
    |(lower + step * z) / S -
      (lower + step * ((H - 1 : ℕ) : ℝ) * (z / H)) / S| ≤ 1 / H := by
  have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one]
  rw [hcast] at hzH hwidth ⊢
  exact affineKernelEndpoint_error lower (Nat.cast_pos.mpr hH) hS hz0 hzH hstep hwidth

end Erdos3


namespace Erdos3

def scalarCubeDifferenceMatrix {I J : Type*} {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) : Matrix I J ℤ :=
  sampledColumnMatrix (fun _j y i => (y (some i) : ℤ)) x

def scalarCubeLargeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  (∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
    B < integerCokernelExponent (scalarCubeDifferenceMatrix x).mulVecLin.range

theorem scalarCube_largeCokernel_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (L B : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) (hB : 0 < B)
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (scalarCubeLargeCokernelEvent B) ≤
      (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^
        Fintype.card J / (B : ℝ) := by
  let R := (Fintype.card I).factorial * L ^ Fintype.card I
  have hbound := boxCokernel_probability_le
    (I := I) (J := J) (K := Option I) Option.some (Option.some_injective I)
    (fun _ => -(L : ℤ)) (fun _ => (L : ℤ)) (fun _ => by omega)
    (fun _ => integerScalarCubeWeights I L hL) B R hB
    (integerScalarCubeDensityCap I) ((Fintype.card I).factorial : ℝ)
    (integerScalarCubeDensityCap_pos I).le (Nat.cast_nonneg _) hJ
    (fun _ x => integerScalarCubeWeights_weight_le I L hL hsize x) (fun _ => ?_)
  · apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hbound
    intro x hx
    apply nonzeroMinor_largeCokernelEvent _ x B L _ hx.1 hx.2
    intro i j
    have h := Finset.mem_Ico.mp (x j (some i)).property
    have ha : |(x j (some i) : ℤ)| ≤ (L : ℤ) := abs_le.mpr ⟨h.1, h.2.le⟩
    have hn : (((x j (some i) : ℤ).natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hn
  · have h := nat_monomial_root_le (Fintype.card I) (Fintype.card I).factorial L
      Fintype.card_pos (Nat.factorial_pos _)
    apply h.trans
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Fintype.card I).factorial from Nat.cast_nonneg _]


open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

theorem integerScalarCubeWeights_supported_mean (q L : ℕ) (hL : 0 < L)
    (f : ((Fin q → ℤ) × ℤ) → ℝ) :
    (integerScalarCubeWeights (Fin q) L hL).mean
        (fun x => f (fun i => (x (some i) : ℤ), (x none : ℤ))) =
      𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)), f p.val := by
  rw [integerScalarCubeWeights_mean]
  exact Fintype.expect_equiv (integerScalarCubeEquiv q L) _ _ (fun _ => rfl)

end Erdos3


namespace Erdos3

noncomputable def scalarCubeResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) * (M : ℝ)) ^ (Fintype.card I + 1)

theorem scalarCubeResidueDensityCap_pos (I : Type*) [Fintype I] (M : ℕ) (hM : 0 < M) :
    0 < scalarCubeResidueDensityCap I M := by
  unfold scalarCubeResidueDensityCap
  positivity

theorem scalarCubeResidueReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass
        ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let n := Fintype.card I + 1
  let H := L / (n * M)
  have hn : 0 < n := by dsimp [n]; omega
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hH : 0 < H := Nat.div_pos hsize (Nat.mul_pos hn hM)
  have hHL : n * (M * H) ≤ L := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le L (n * M)
  have hc := scalarCubeResidueSet_card_lower I L M H m r hm hmM hH hHL
  have hfloor : (L : ℝ) ≤ 2 * ((n : ℝ) * M) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower (Nat.mul_pos hn hM) hsize
  have hratio : 1 / (4 * (n : ℝ) * M) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  calc
    _ = (1 / (4 * (n : ℝ) * M)) ^ n := by
      simp only [scalarCubeResidueDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      unfold integerScalarCubeReference
      rw [FiniteProbabilityWeights.uniform_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem scalarCubeResidue_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) := by
  exact (scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize).trans
    (FiniteProbabilityWeights.mass_inter_le_condition_mass _ _ _ _)

theorem scalarCubeResidue_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) :=
  (inv_pos.mpr (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))).trans_le
    (scalarCubeResidue_mass_lower I L M hL m r hm hmM hsize)


open scoped BigOperators

noncomputable def scalarCubeResidueWeights (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeWeights I L hL).condition (scalarCubeResidueSet I L m r)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize)

theorem scalarCubeResidueWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) (f : IntegerScalarCubeBox I L → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean f =
      𝔼 x : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r), f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_condition_mean _ _
    (integerScalarCubeReference_mass_pos I L hL)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize) f

theorem scalarCubeResidueWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) (x : IntegerScalarCubeBox I L) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x ≤
      scalarCubeResidueDensityCap I M * (integerScalarCubeWeights I L hL).weight x := by
  have hcap := scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none))
  have h := FiniteProbabilityWeights.condition_weight_le _ _
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize)
    (scalarCubeResidueDensityCap I M)⁻¹ (inv_pos.mpr hcap)
    (scalarCubeResidue_mass_lower I L M hL m r hm hmM hsize) x
  simpa only [scalarCubeResidueWeights, inv_inv] using h

theorem scalarCubeResidue_pi_eventProbability_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (L M : ℕ) (hL : 0 < L) (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) (E : (J → IntegerScalarCubeBox I L) → Prop) :
    (FiniteProbabilityWeights.pi (fun j =>
      scalarCubeResidueWeights I L M hL (m j) (r j) (hm j) (hmM j) hsize)).eventProbability E ≤
      (scalarCubeResidueDensityCap I M) ^ Fintype.card J *
        (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability E := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    FiniteProbabilityWeights.pi_eventProbability_le
      (fun j => scalarCubeResidueWeights I L M hL (m j) (r j) (hm j) (hmM j) hsize)
      (fun _ : J => integerScalarCubeWeights I L hL) (fun _ => scalarCubeResidueDensityCap I M)
      (fun j x => scalarCubeResidueWeights_weight_le I L M hL (m j) (r j) (hm j) (hmM j) hsize x) E

end Erdos3


namespace Erdos3

theorem scalarCubeResidueWeights_support (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I+1)*M ≤ L)
    (x : IntegerScalarCubeBox I L)
    (hx : (scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x ≠ 0) :
    ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  apply (mem_scalarCubeResidueSet L m r x).mp
  by_contra hnot
  apply hx
  simp only [scalarCubeResidueWeights, FiniteProbabilityWeights.condition, hnot, ite_false, zero_div]

theorem scalarCubeResiduePi_support {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j)
    (x : ∀ j, IntegerScalarCubeBox I (L j))
    (hx : (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).weight x ≠ 0) :
    ∀ j i, ((x j i : ℤ) : ZMod (m j i)) = r j i := by
  intro j
  apply scalarCubeResidueWeights_support I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j) (x j)
  intro hz
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) hz

theorem scalarCubeResiduePi_condition {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j) :
    FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j)) =
      (FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights I (L j) (hL j))).condition
        (FiniteProbabilityWeights.piRestrictionSet (fun j => scalarCubeResidueSet I (L j) (m j) (r j)))
        (FiniteProbabilityWeights.piRestriction_mass_pos _ _
          (fun j => scalarCubeResidue_mass_pos I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j))) :=
  FiniteProbabilityWeights.pi_condition _ _ _

end Erdos3

end OAI
