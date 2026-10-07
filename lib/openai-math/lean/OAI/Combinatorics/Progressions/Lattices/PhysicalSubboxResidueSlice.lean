/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CubeTranslation
import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
import OAI.Combinatorics.Progressions.Estimates.PhysicalSliceCost
import OAI.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
import OAI.Combinatorics.Progressions.Lattices.BoxResiduePartition
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBox (T : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i ↦ Finset.Ico (0 : ℤ) (T i))

@[simp] theorem mem_integerBox (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ integerBox T ↔ ∀ i, 0 ≤ x i ∧ x i < T i := by
  simp [integerBox, Fintype.mem_piFinset]

abbrev BoxAmbient (T : ι → ℕ) := ∀ i, ZMod (4 * T i)

def boxReduction (T : ι → ℕ) : (ι → ℤ) →+ BoxAmbient T where
  toFun x i := x i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem boxReduction_apply (T : ι → ℕ) (x : ι → ℤ) (i : ι) :
    boxReduction T x i = (x i : ZMod (4 * T i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem int_eq_of_zmod_eq_of_bounds {m : ℕ} {a b : ℤ}
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) (he : (a : ZMod m) = (b : ZMod m)) :
    a = b := by
  have hm := (ZMod.intCast_eq_intCast_iff' a b m).mp he
  simpa only [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] using hm

theorem boxReduction_reflectsPairSums (T : ι → ℕ) :
    ReflectsPairSums (boxReduction T) (integerBox T : Set (ι → ℤ)) := by
  intro a ha b hb c hc d hd he
  have ha' := (mem_integerBox T a).mp ha
  have hb' := (mem_integerBox T b).mp hb
  have hc' := (mem_integerBox T c).mp hc
  have hd' := (mem_integerBox T d).mp hd
  funext i
  change a i + b i = c i + d i
  apply int_eq_of_zmod_eq_of_bounds (m := 4 * T i)
  · have h1 := ha' i
    have h2 := hb' i
    constructor <;> push_cast <;> omega
  · have h1 := hc' i
    have h2 := hd' i
    constructor <;> push_cast <;> omega
  · have hi := congrFun he i
    simpa only [Pi.add_apply, boxReduction_apply, Int.cast_add] using hi

theorem boxReduction_injOn (T : ι → ℕ) :
    Set.InjOn (boxReduction T) (integerBox T : Set (ι → ℤ)) :=
  (boxReduction_reflectsPairSums T).injOn

noncomputable def integerBoxCubeEquiv (T : ι → ℕ) (j : ℕ) :
    SupportedCube j (integerBox T : Set (ι → ℤ)) ≃
      SupportedCube j (boxReduction T '' (integerBox T : Set (ι → ℤ))) :=
  supportedCubeEquiv (boxReduction_reflectsPairSums T) j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_zmod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox (fun _ : ι => N), f x) =
      𝔼 t : ι → ZMod N, f (fun i => ((t i).val : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).val_lt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply ZMod.val_injective N
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox (fun _ : ι => N) x).mp hx
    refine ⟨(fun i => (x i : ZMod N)), Finset.mem_univ _, ?_⟩
    funext i
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_subtype_mean_eq_fin {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (F : (X → ℤ) → ℝ) :
    (𝔼 u : ↥(integerBox N), F u.val) =
      (𝔼 u : (∀ i, Fin (N i)), F (fun i => ((u i).val : ℤ))) := by
  classical
  symm
  let lift : (∀ i, Fin (N i)) → ↥(integerBox N) := fun u =>
    ⟨(fun i => ((u i).val : ℤ)), (mem_integerBox N _).mpr (fun i =>
      ⟨by positivity, by exact_mod_cast (u i).isLt⟩)⟩
  apply Finset.expect_nbij lift
  · intro u _
    exact Finset.mem_univ _
  · intro u _
    rfl
  · intro u _ v _ huv
    funext i
    apply Fin.ext
    have h := congrFun (congrArg Subtype.val huv) i
    change ((u i).val : ℤ) = ((v i).val : ℤ) at h
    exact_mod_cast h
  · intro u _
    have hu := (mem_integerBox N u.val).mp u.property
    let v : ∀ i, Fin (N i) := fun i => ⟨(u.val i).toNat, by
      have hi := hu i
      omega⟩
    refine ⟨v, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext i
    exact Int.toNat_of_nonneg (hu i).1

end Erdos3

end

section

namespace Erdos3

def integerCyclicMap (N : ℕ) : ℤ →+ ZMod N := Int.castAddHom (ZMod N)

theorem integerInterval_reflectsPairSums (N : ℕ) (a b : ℤ)
    (hdiam : 2 * (b - a - 1) < (N : ℤ)) :
    ReflectsPairSums (integerCyclicMap N) (Finset.Ico a b : Set ℤ) := by
  intro x hx y hy z hz t ht he
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have hz' := Finset.mem_Ico.mp hz
  have ht' := Finset.mem_Ico.mp ht
  have hxy : 0 ≤ x + y - 2 * a ∧ x + y - 2 * a < N := by omega
  have hzt : 0 ≤ z + t - 2 * a ∧ z + t - 2 * a < N := by omega
  have he' : ((x + y - 2 * a : ℤ) : ZMod N) = ((z + t - 2 * a : ℤ) : ZMod N) := by
    change (x : ZMod N) + y = (z : ZMod N) + t at he
    push_cast
    exact congrArg (fun v : ZMod N => v - 2 * (a : ZMod N)) he
  have hh := int_eq_of_zmod_eq_of_bounds hxy hzt he'
  omega

theorem integerInterval_image_cyclicInterval (N : ℕ) (a : ℤ) (L : ℕ) :
    (Finset.Ico a (a + L)).image (integerCyclicMap N) = cyclicInterval (a : ZMod N) L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_Ico.mp hy
    refine Finset.mem_image.mpr ⟨(y - a).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · change (a : ZMod N) + ((y - a).toNat : ZMod N) = (y : ZMod N)
      have he : (((y - a).toNat : ℕ) : ℤ) = y - a := Int.toNat_of_nonneg (by omega)
      rw [← Int.cast_natCast, he]
      push_cast
      ring
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨a + k, Finset.mem_Ico.mpr ?_, ?_⟩
    · have hk' := Finset.mem_range.mp hk
      omega
    · change ((a + k : ℤ) : ZMod N) = (a : ZMod N) + k
      push_cast
      rfl

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBoxCubeCount (T : ι → ℕ) (j : ℕ) : ℕ :=
  Nat.card (SupportedCube j (integerBox T : Set (ι → ℤ)))

noncomputable def integerBoxGowersNorm (T : ι → ℕ) (j : ℕ) (f : (ι → ℤ) → ℂ) : ℝ :=
  finiteSupportGowersNorm j (integerBox T) f

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem integerBox_nonempty : (integerBox T).Nonempty := by
  refine ⟨0, (mem_integerBox T 0).mpr ?_⟩
  intro i
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < T i
  exact ⟨le_rfl, by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (T i))⟩

theorem integerBoxCubeCount_eq_groupCubeCount (j : ℕ) :
    integerBoxCubeCount T j = groupCubeCount j ((integerBox T).image (boxReduction T)) :=
  card_supportedCube_image (boxReduction_reflectsPairSums T) j

theorem integerBoxCubeCount_pos (j : ℕ) : 0 < integerBoxCubeCount T j := by
  rw [integerBoxCubeCount_eq_groupCubeCount]
  exact groupCubeCount_pos j ((integerBox_nonempty T).image (boxReduction T))

theorem integerBoxGowersNorm_one (j : ℕ) :
    integerBoxGowersNorm T j (fun _ ↦ 1) = 1 :=
  finiteSupportGowersNorm_one j (integerBox_nonempty T)

theorem integerBoxGowersNorm_eq_restricted (j : ℕ) (f : (ι → ℤ) → ℂ) :
    integerBoxGowersNorm T (j + 1) f =
      restrictedGowersNorm (j + 1) ((integerBox T).image (boxReduction T))
        (imageExtension (boxReduction T) (integerBox T) f) :=
  finiteSupportGowersNorm_eq_restricted (boxReduction_reflectsPairSums T) j f

theorem integerBoxGowersNorm_ambient_comparison (j : ℕ) (f : (ι → ℤ) → ℂ) :
    gowersNorm (j + 1) (imageExtension (boxReduction T) (integerBox T) f) ^ (2 ^ (j + 1)) =
      ((integerBoxCubeCount T (j + 1) : ℝ) / (Fintype.card (BoxAmbient T) : ℝ) ^ (j + 2)) *
        integerBoxGowersNorm T (j + 1) f ^ (2 ^ (j + 1)) :=
  finiteSupportGowersNorm_ambient_comparison (boxReduction_reflectsPairSums T) j f

theorem integerBoxGowersNorm_add (j : ℕ) (f g : (ι → ℤ) → ℂ) :
    integerBoxGowersNorm T (j + 1) (fun x ↦ f x + g x) ≤
      integerBoxGowersNorm T (j + 1) f + integerBoxGowersNorm T (j + 1) g :=
  finiteSupportGowersNorm_add_of_embedding (boxReduction_reflectsPairSums T) j f g

theorem integerBoxGowersNorm_degree_one (f : (ι → ℤ) → ℂ) :
    integerBoxGowersNorm T 1 f = ‖𝔼 x ∈ integerBox T, f x‖ :=
  finiteSupportGowersNorm_degree_one_of_embedding (boxReduction_reflectsPairSums T)
    (integerBox_nonempty T) f

theorem integerBoxGowersNorm_pow_tsum (j : ℕ) (f : (ι → ℤ) → ℂ) :
    integerBoxGowersNorm T (j + 1) f ^ (2 ^ (j + 1)) =
      (∑' p : (Fin (j + 1) → (ι → ℤ)) × (ι → ℤ),
        mixedCubeProduct (fun _ ↦ restrictTo (integerBox T) f) p.1 p.2).re /
          integerBoxCubeCount T (j + 1) := by
  rw [integerBoxGowersNorm_eq_restricted,
    restrictedGowersNorm_imageExtension_pow (boxReduction_reflectsPairSums T),
    supportedCubeSum_eq_tsum]
  rfl

theorem integerBox_mixed_cauchy_schwarz (j : ℕ)
    (F : (Fin (j + 1) → Bool) → (ι → ℤ) → ℂ) :
    ‖supportedCubeSum (j + 1) (integerBox T : Set (ι → ℤ)) F‖ /
        integerBoxCubeCount T (j + 1) ≤
      ∏ ω, integerBoxGowersNorm T (j + 1) (F ω) :=
  norm_supportedCubeSum_le_of_embedding (boxReduction_reflectsPairSums T) j F

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_integerBox (T : ι → ℕ) : (integerBox T).card = ∏ i, T i := by
  simp [integerBox]

def smallCubeSide (T : ι → ℕ) (j : ℕ) (i : ι) : ℕ := (T i - 1) / (j + 1) + 1

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem small_increments_supported (j : ℕ) (x : ι → ℤ)
    (hx : x ∈ integerBox (smallCubeSide T j)) (ds : Fin j → (ι → ℤ))
    (hds : ∀ k, ds k ∈ integerBox (smallCubeSide T j)) (ω : Fin j → Bool) :
    x + cubeShift ds ω ∈ integerBox T := by
  apply (mem_integerBox T _).mpr
  intro i
  let m := (T i - 1) / (j + 1)
  have hxi : 0 ≤ x i ∧ x i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp hx i
    change 0 ≤ x i ∧ x i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hdi (k : Fin j) : 0 ≤ ds k i ∧ ds k i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp (hds k) i
    change 0 ≤ ds k i ∧ ds k i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hlo : 0 ≤ ∑ k, if ω k then ds k i else (0 : ℤ) := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact (hdi k).1
    · exact le_rfl
  have hhi : (∑ k, if ω k then ds k i else (0 : ℤ)) ≤ (j : ℤ) * m := by
    calc
      _ ≤ ∑ _k : Fin j, (m : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        split_ifs
        · exact (hdi k).2
        · exact Int.natCast_nonneg _
      _ = _ := by simp
  have hm : ((j : ℤ) + 1) * (m : ℤ) < T i := by
    have hmul := Nat.mul_div_le (T i - 1) (j + 1)
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    have hlt : (j + 1) * m < T i := hmul.trans_lt (Nat.sub_lt hT (by omega))
    exact_mod_cast hlt
  simp only [Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply]
  constructor <;> nlinarith [hxi.1, hxi.2]

noncomputable def smallBoxCubeMap (j : ℕ) :
    ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) →
      SupportedCube j (integerBox T : Set (ι → ℤ)) :=
  fun p ↦ ⟨(fun k ↦ (p.1 k).val, p.2.val),
    small_increments_supported T j p.2.val p.2.property
      (fun k ↦ (p.1 k).val) (fun k ↦ (p.1 k).property)⟩

theorem smallBoxCubeMap_injective (j : ℕ) : Function.Injective (smallBoxCubeMap T j) := by
  intro p q he
  apply Prod.ext
  · funext k
    apply Subtype.ext
    exact congrArg (fun r ↦ r.val.1 k) he
  · apply Subtype.ext
    exact congrArg (fun r ↦ r.val.2) he

theorem small_box_card_pow_le_cubeCount (j : ℕ) :
    (integerBox (smallCubeSide T j)).card ^ (j + 1) ≤ integerBoxCubeCount T j := by
  have h := Nat.card_le_card_of_injective (smallBoxCubeMap T j) (smallBoxCubeMap_injective T j)
  change Nat.card ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) ≤
    integerBoxCubeCount T j at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_fin, pow_succ] using h

theorem card_integerBox_le_small_box (j : ℕ) :
    (integerBox T).card ≤ (j + 1) ^ Fintype.card ι * (integerBox (smallCubeSide T j)).card := by
  have hi (i : ι) : T i ≤ (j + 1) * smallCubeSide T j i := by
    have h := Nat.lt_mul_div_succ (T i - 1) (Nat.succ_pos j)
    change T i - 1 < (j + 1) * ((T i - 1) / (j + 1) + 1) at h
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    change T i ≤ (j + 1) * ((T i - 1) / (j + 1) + 1)
    omega
  calc
    _ = ∏ i, T i := card_integerBox T
    _ ≤ ∏ i, (j + 1) * smallCubeSide T j i :=
      Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hi i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]; simp [card_integerBox]

theorem integerBoxCubeCount_lower (j : ℕ) :
    (integerBox T).card ^ (j + 1) ≤
      (j + 1) ^ (Fintype.card ι * (j + 1)) * integerBoxCubeCount T j := by
  have h := Nat.pow_le_pow_left (card_integerBox_le_small_box T j) (j + 1)
  rw [mul_pow, ← pow_mul] at h
  exact h.trans (Nat.mul_le_mul_left _ (small_box_card_pow_le_cubeCount T j))

omit [∀ i, NeZero (T i)] in
theorem integerBoxCubeCount_upper (j : ℕ) :
    integerBoxCubeCount T j ≤ (integerBox T).card ^ (j + 1) :=
  card_supportedCube_le j (integerBox T)

theorem integerBoxCubeCount_bounds (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) ≤ integerBoxCubeCount T j ∧
      (integerBoxCubeCount T j : ℝ) ≤ ((integerBox T).card : ℝ) ^ (j + 1) := by
  constructor
  · have h : ((integerBox T).card : ℝ) ^ (j + 1) ≤
        (((j + 1 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 1))) * integerBoxCubeCount T j := by
      exact_mod_cast integerBoxCubeCount_lower T j
    have he : ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) =
        ((integerBox T).card : ℝ) ^ (j + 1) /
          ((j : ℝ) + 1) ^ (Fintype.card ι * (j + 1)) := by
      rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm (j + 1) (Fintype.card ι)]
      ring
    rw [he]
    apply (div_le_iff₀ (pow_pos (by positivity : 0 < (j : ℝ) + 1) _)).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  · exact_mod_cast integerBoxCubeCount_upper T j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def integerBoxTestExtension {X : Type*} (N : X → ℕ)
    (test : (X → ℝ) → ℂ) (y : X → ℝ) : ℂ :=
  if ∀ x, 0 ≤ y x ∧ y x < (N x : ℝ) then test y else 0

theorem integerBoxTestExtension_integer {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (test : (X → ℝ) → ℂ) (u : X → ℤ) :
    integerBoxTestExtension N test (fun x => (u x : ℝ)) =
      if u ∈ integerBox N then test (fun x => (u x : ℝ)) else 0 := by
  have hc : (∀ x, 0 ≤ (u x : ℝ) ∧ (u x : ℝ) < (N x : ℝ)) ↔ u ∈ integerBox N := by
    rw [mem_integerBox]
    constructor
    · intro h x
      exact_mod_cast h x
    · intro h x
      exact_mod_cast h x
  simp only [integerBoxTestExtension, hc]

theorem integerBoxTestExtension_norm_le_one {X : Type*} (N : X → ℕ)
    (test : (X → ℝ) → ℂ) (htest : ∀ y, ‖test y‖ ≤ 1) (y : X → ℝ) :
    ‖integerBoxTestExtension N test y‖ ≤ 1 := by
  unfold integerBoxTestExtension
  split_ifs
  · exact htest y
  · simp

theorem integerBoxTestExtension_of_mem {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (test : (X → ℝ) → ℂ) (u : X → ℤ) (hu : u ∈ integerBox N) :
    integerBoxTestExtension N test (fun x => (u x : ℝ)) = test (fun x => (u x : ℝ)) := by
  rw [integerBoxTestExtension_integer, ite_eq_left hu]

theorem integerBoxTestExtension_of_not_mem {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (test : (X → ℝ) → ℂ) (u : X → ℤ) (hu : u ∉ integerBox N) :
    integerBoxTestExtension N test (fun x => (u x : ℝ)) = 0 := by
  rw [integerBoxTestExtension_integer, ite_eq_right hu]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) : Finset (ι → ℤ) :=
  translateSupport a (integerBox T)

theorem mem_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ translatedIntegerBox a T ↔ ∀ i, a i ≤ x i ∧ x i < a i + T i := by
  rw [translatedIntegerBox, mem_translateSupport, mem_integerBox]
  apply forall_congr'
  intro i
  change (0 ≤ x i - a i ∧ x i - a i < T i) ↔ _
  omega

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem translatedIntegerBox_nonempty (a : ι → ℤ) : (translatedIntegerBox a T).Nonempty :=
  (integerBox_nonempty T).image (fun x ↦ a + x)

omit [∀ i, NeZero (T i)] in
theorem translatedIntegerBox_reflectsPairSums (a : ι → ℤ) :
    ReflectsPairSums (boxReduction T) (translatedIntegerBox a T : Set (ι → ℤ)) :=
  (boxReduction_reflectsPairSums T).translate a

omit [∀ i, NeZero (T i)] in
theorem translatedIntegerBox_norm_eq (a : ι → ℤ) (j : ℕ) (f : (ι → ℤ) → ℂ) :
    finiteSupportGowersNorm j (translatedIntegerBox a T) f =
      integerBoxGowersNorm T j (fun x ↦ f (a + x)) :=
  finiteSupportGowersNorm_translate j (integerBox T) a f

theorem translatedIntegerBox_norm_degree_one (a : ι → ℤ) (f : (ι → ℤ) → ℂ) :
    finiteSupportGowersNorm 1 (translatedIntegerBox a T) f =
      ‖𝔼 x ∈ translatedIntegerBox a T, f x‖ :=
  finiteSupportGowersNorm_degree_one_of_embedding (translatedIntegerBox_reflectsPairSums T a)
    (translatedIntegerBox_nonempty T a) f

theorem translatedIntegerBox_cubeCount_bounds (a : ι → ℤ) (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) ≤
          Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) ∧
      (Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) : ℝ) ≤
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) := by
  simpa only [translatedIntegerBox, card_translateSupport, card_supportedCube_translate,
    integerBoxCubeCount] using integerBoxCubeCount_bounds T j

theorem integerBox_weighted_derivative (a : ι → ℤ) (j : ℕ) (f : (ι → ℤ) → ℂ) :
    (Nat.card (SupportedCube (j + 2) (translatedIntegerBox a T : Set (ι → ℤ))) : ℝ) *
        finiteSupportGowersNorm (j + 2) (translatedIntegerBox a T) f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport (translatedIntegerBox a T),
        (Nat.card (SupportedCube (j + 1)
          (derivativeSupport (translatedIntegerBox a T) h : Set (ι → ℤ))) : ℝ) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport (translatedIntegerBox a T) h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) :=
  finiteSupportGowersNorm_derivative_mul_count (translatedIntegerBox_reflectsPairSums T a)
    (translatedIntegerBox_nonempty T a) j f

theorem integerBox_sum_derivative_weights (a : ι → ℤ) (j : ℕ) :
    (∑ h ∈ cubeDifferenceSupport (translatedIntegerBox a T),
      (Nat.card (SupportedCube j (derivativeSupport (translatedIntegerBox a T) h : Set (ι → ℤ))) : ℝ) /
        Nat.card (SupportedCube (j + 1) (translatedIntegerBox a T : Set (ι → ℤ)))) = 1 :=
  sum_supportedCube_weights j (translatedIntegerBox_nonempty T a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def trimmedIntegerBox (N R : I → ℕ) : Finset (I → ℤ) :=
  (integerBox (fun i => N i - 2 * R i)).image (fun x => (fun i => (R i : ℤ)) + x)

theorem card_trimmedIntegerBox (N R : I → ℕ) :
    (trimmedIntegerBox N R).card = ∏ i, (N i - 2 * R i) := by
  rw [trimmedIntegerBox, Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h),
    card_integerBox]

theorem trimmedIntegerBox_nonempty (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i) :
    (trimmedIntegerBox N R).Nonempty := by
  apply Finset.Nonempty.image
  refine ⟨0, (mem_integerBox _ _).mpr ?_⟩
  intro i
  have h : 0 < N i - 2 * R i := Nat.sub_pos_of_lt (hR i)
  simpa using h

theorem trimmedIntegerBox_add_mem (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    {x : I → ℤ} (hx : x ∈ trimmedIntegerBox N R) (y : I → ℤ)
    (hy : ∀ i, |y i| ≤ (R i : ℤ)) : x + y ∈ integerBox N := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hi := (mem_integerBox _ _).mp ha i
  have hyi := abs_le.mp (hy i)
  have hRi := hR i
  simp only [Pi.add_apply]
  omega

theorem trimmedIntegerBox_card_deficit (N R : I → ℕ)
    (hN : ∀ i, 0 < N i) (hR : ∀ i, 2 * R i ≤ N i) :
    1 - ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card ≤
      ∑ i, 2 * (R i : ℝ) / N i := by
  have hNR (i : I) : 0 < (N i : ℝ) := by exact_mod_cast hN i
  have he (i : I) : 2 * (R i : ℝ) / N i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (hNR i)).mpr
      exact_mod_cast hR i
  have hi (i : I) : 1 - 2 * (R i : ℝ) / N i = ((N i - 2 * R i : ℕ) : ℝ) / N i := by
    rw [Nat.cast_sub (hR i)]
    push_cast
    field_simp [ne_of_gt (hNR i)]
  have hp := one_sub_sum_le_positive_prod Finset.univ
    (fun i => ((N i - 2 * R i : ℕ) : ℝ) / N i) (fun i => 2 * (R i : ℝ) / N i)
    (fun i _ => by positivity) (fun i _ => he i) (fun i _ => (hi i).le)
  rw [card_trimmedIntegerBox, card_integerBox, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]
  linarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeSupport_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (h : ι → ℤ) :
    derivativeSupport (translatedIntegerBox a T) h =
      translatedIntegerBox (fun i => a i + max 0 (-h i)) (fun i => ((T i : ℤ) - |h i|).toNat) := by
  ext x
  simp only [derivativeSupport, Finset.mem_filter, mem_translatedIntegerBox, Pi.add_apply,
    ← forall_and]
  apply forall_congr'
  intro i
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi, max_eq_left (by omega : -h i ≤ 0)]
    omega
  · rw [abs_of_neg (by omega : h i < 0), max_eq_right (by omega : 0 ≤ -h i)]
    omega

theorem box_overlap_length_pos (a : ι → ℤ) (T : ι → ℕ) {h : ι → ℤ}
    (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T)) (i : ι) :
    0 < ((T i : ℤ) - |h i|).toNat := by
  obtain ⟨x, hx⟩ := (mem_cubeDifferenceSupport _ h).mp hh
  obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
  have hx' := (mem_translatedIntegerBox a T x).mp hx i
  have hxh' := (mem_translatedIntegerBox a T (x + h)).mp hxh i
  simp only [Pi.add_apply] at hxh'
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi]
    omega
  · rw [abs_of_neg (by omega : h i < 0)]
    omega

theorem box_differenceSupport_subset (a : ι → ℤ) (T : ι → ℕ) :
    cubeDifferenceSupport (translatedIntegerBox a T) ⊆
      translatedIntegerBox (fun i => -(T i : ℤ)) (fun i => 2 * T i) := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  apply (mem_translatedIntegerBox _ _ _).mpr
  intro i
  have hx' := (mem_translatedIntegerBox a T p.1).mp hx i
  have hy' := (mem_translatedIntegerBox a T p.2).mp hy i
  simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem card_box_differenceSupport_le (a : ι → ℤ) (T : ι → ℕ) :
    (cubeDifferenceSupport (translatedIntegerBox a T)).card ≤
      2 ^ Fintype.card ι * (translatedIntegerBox a T).card := by
  apply (Finset.card_le_card (box_differenceSupport_subset a T)).trans_eq
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def translatedIntegerBoxEquivPi {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) :
    ↥(translatedIntegerBox a N) ≃ ∀ i, ↥(Finset.Ico (a i) (a i + N i)) := by
  let e : ↥(translatedIntegerBox a N) ≃
      {x : I → ℤ // ∀ i, x i ∈ Finset.Ico (a i) (a i + N i)} :=
    Equiv.subtypeEquivRight (fun x => by simp only [mem_translatedIntegerBox, Finset.mem_Ico])
  exact e.trans Equiv.subtypePiEquivPi

@[simp] theorem translatedIntegerBoxEquivPi_val {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (x : ↥(translatedIntegerBox a N)) (i : I) :
    ((translatedIntegerBoxEquivPi a N x) i).val = x.val i := rfl

noncomputable def integerResidueBoxEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i) :
    ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i))) ≃ IntegerResidueBox a b r v :=
  (translatedIntegerBoxEquivPi _ _).trans
    (Equiv.piCongrRight fun i => residueIntervalEquiv (a i) (b i) (r i) (v i) (hr i))

@[simp] theorem integerResidueBoxEquiv_val {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i)
    (x : ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i)))) (i : I) :
    ((integerResidueBoxEquiv a b r v hr x) i).val = v i + r i * x.val i := rfl

theorem integerResidueBox_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i) (f : (I → ℤ) → ℂ) :
    (𝔼 x : IntegerResidueBox a b r v, f (fun i => (x i).val)) =
      𝔼 x ∈ translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
        (fun i => residueIndexLength (a i) (b i) (r i) (v i)), f (fun i => v i + r i * x i) := by
  let B := translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
    (fun i => residueIndexLength (a i) (b i) (r i) (v i))
  have h := Fintype.expect_equiv (integerResidueBoxEquiv a b r v hr)
    (fun x => f (fun i => v i + r i * x.val i))
    (fun x => f (fun i => (x i).val)) (fun _ => rfl)
  let g : (I → ℤ) → ℂ := fun x => f (fun i => v i + r i * x i)
  have hcoe : (𝔼 x : ↥B, g x.val) = 𝔼 x ∈ B, g x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact h.symm.trans hcoe

theorem integerResidueBox_lengths_pos {I : Type*} (a b r v : I → ℤ)
    (hr : ∀ i, 0 < r i) (hbox : Nonempty (IntegerResidueBox a b r v)) :
    ∀ i, 0 < residueIndexLength (a i) (b i) (r i) (v i) := by
  obtain ⟨x⟩ := hbox
  intro i
  rw [residueIndexLength_eq_card (a i) (b i) (r i) (v i) (hr i)]
  exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩

end Erdos3

end

section

namespace Erdos3

private noncomputable def physicalResidueCoordinateEquiv
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M) :
    Fin (residueIndexLength lo hi M a) ≃
      ↥(Finset.filter (fun x => x ≡ a [ZMOD (M : ℤ)]) (Finset.Ico lo hi)) :=
  (integerIntervalEquivFin (residueIndexLower lo M a)
    (residueIndexLength lo hi M a)).symm.trans
      (residueIntervalEquiv lo hi M a (Nat.cast_pos.mpr hM))

private theorem physicalResidueCoordinateEquiv_val
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M)
    (j : Fin (residueIndexLength lo hi M a)) :
    (physicalResidueCoordinateEquiv lo hi a M hM j).val =
      a + M * (residueIndexLower lo M a + j.val) := rfl

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

include hM hbox hne in
private theorem physicalResidue_start_nonneg (i : X) :
    0 ≤ a i + M * residueIndexLower (lo i) M (a i) := by
  have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
    ⟨0, hne i⟩).property
  have hlow := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1
  rw [physicalResidueCoordinateEquiv_val] at hlow
  have hboxlow := (hbox i).1
  simpa only [Nat.cast_zero, add_zero] using hboxlow.trans hlow

noncomputable def ofPhysicalResidue : ResidueBoxSlice N M where
  start i := (a i + M * residueIndexLower (lo i) M (a i)).toNat
  length i := residueIndexLength (lo i) (lo i + H i) M (a i)
  inside i j hj := by
    have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
      ⟨j, hj⟩).property
    have hhigh := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
    rw [physicalResidueCoordinateEquiv_val] at hhigh
    have hboxhigh := (hbox i).2
    have hstart := physicalResidue_start_nonneg N H lo a M hM hbox hne i
    have hlt : ((a i + M * residueIndexLower (lo i) M (a i)).toNat : ℤ) +
        (M : ℤ) * j < N i := by
      rw [Int.toNat_of_nonneg hstart]
      nlinarith
    exact_mod_cast hlt

@[simp] theorem ofPhysicalResidue_length (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).length i =
      residueIndexLength (lo i) (lo i + H i) M (a i) := rfl

@[simp] theorem ofPhysicalResidue_start (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).start i =
      (a i + M * residueIndexLower (lo i) M (a i)).toNat := rfl

theorem ofPhysicalResidue_length_pos (i : X) :
    0 < (ofPhysicalResidue N H lo a M hM hbox hne).length i := hne i

theorem ofPhysicalResidue_point_int
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) =
      a i + M * (residueIndexLower (lo i) M (a i) + (j i).val) := by
  change (((a i + M * residueIndexLower (lo i) M (a i)).toNat + M * (j i).val : ℕ) : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg (physicalResidue_start_nonneg N H lo a M hM hbox hne i)]
  ring

noncomputable def ofPhysicalResidueEquiv :
    (∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) ≃
      IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a :=
  Equiv.piCongrRight fun i =>
    physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM

@[simp] theorem ofPhysicalResidueEquiv_val
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    ((ofPhysicalResidueEquiv N H lo a M hM hbox hne j) i).val =
      (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) := by
  rw [ofPhysicalResidue_point_int]
  rfl

end ResidueBoxSlice
end Erdos3

end

end OAI
