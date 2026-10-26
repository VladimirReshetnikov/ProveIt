import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.WangTiles942Permutation

/-!
# Reflected geometry and conditional low-field resets

All reflected terms of the literal current kernel are retained. The low
support proves that a surviving reflected source lies in the same cell.
The reset theorem explicitly assumes at most one physical selector in that
cell. It assumes neither decoded labels nor temporal phase alignment.
-/

namespace DiophantineConsistency.CurrentReflectedGeometry2011

open CurrentKernel2011 CurrentMasks2011 WangTiles942 NativeCyclicConvolution
open scoped BigOperators

set_option Elab.async false

abbrev Control := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

theorem position_injective : Function.Injective position := by
  intro e f he
  rcases e with i | i | i | i | i <;>
    rcases f with j | j | j | j | j
  all_goals simp only [position] at he
  · exact congrArg Sum.inl (physicalPosition_injective he)
  all_goals try have hi := physicalPosition_lt i
  all_goals try have hj := physicalPosition_lt j
  all_goals try omega
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq]
  all_goals apply Fin.ext; omega

theorem doubled_weight_lt (e : Entry) : 2 * weight e < 2 ^ 45 := by
  rcases e with i | j | j | j | j
  · have hh := weight_small i
    change 2 * selectorWeight (tile i) < 2 ^ 45
    omega
  all_goals
    change 2 * 2 ^ _ < 2 ^ 45
    fin_cases j <;> decide

theorem doubled_control_mass :
    (∑ e : Control, 2 * weight (.inr e)) = 2 ^ 45 - 2048 := by
  decide +kernel

theorem support_le {f : ℕ} (hf : f ∈ lowSupport) : f ≤ 1004 := by
  rw [lowSupport_def] at hf
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hf
  omega

theorem selector_position_lt (i : Fin 942) : position (.inl i) < 942 :=
  physicalPosition_lt i

theorem control_position_ge (e : Control) : 942 ≤ position (.inr e) := by
  rcases e with j | j | j | j <;> simp only [position] <;> omega

variable {N : ℕ} [NeZero (N * 2011)]

/-- The exact reflected summand in `CurrentKernel2011.convolution_eq`. -/
def reflected (c : ZMod (N * 2011) → ℕ) (k : ZMod (N * 2011)) : ℕ :=
  ∑ e : Entry, 2 * weight e * c (k - ((1005 - position e : ℕ) : ZMod (N * 2011)))

omit [NeZero (N * 2011)] in
theorem reflected_even (c : ZMod (N * 2011) → ℕ) (k : ZMod (N * 2011)) :
    Even (reflected c k) := by
  refine ⟨∑ e : Entry, weight e * c (k - ((1005 - position e : ℕ) : ZMod (N * 2011))), ?_⟩
  simp only [reflected, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem add_residue (b : ZMod (N * 2011)) (e : ℕ) :
    (b + (e : ZMod (N * 2011))).val % 2011 = (b.val + e) % 2011 := by
  have hh : (((b + (e : ZMod (N * 2011))).val : ℕ) : ZMod (N * 2011)) =
      ((b.val + e : ℕ) : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

private theorem sub_residue (k : ZMod (N * 2011)) (e : ℕ) :
    ((k - (e : ZMod (N * 2011))).val + e) % 2011 = k.val % 2011 := by
  have hh : (((k - (e : ZMod (N * 2011))).val + e : ℕ) : ZMod (N * 2011)) =
      (k.val : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

/-- Every natural output offset is allowed. A negative source wraps into
unsupported residues1006..2010; otherwise the source is h+p−1005. -/
theorem reflected_source_all (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (hp : p ≤ 1005) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 := by
  by_cases hv : 1005 ≤ h + p
  · rw [if_pos hv]
    congr 1
    rw [Nat.cast_sub hp, Nat.cast_sub hv, Nat.cast_add]
    ring
  · rw [if_neg hv]
    apply hsupport
    intro hs
    have hl := support_le hs
    have hr := sub_residue (b + (h : ZMod (N * 2011))) (1005 - p)
    simp only [add_residue, Nat.add_mod, hb, zero_add, Nat.mod_mod] at hr
    omega

/-- The original low-field API, retained for existing callers. -/
theorem reflected_source (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (hh : h ≤ 1004) (hp : p ≤ 985) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 :=
  reflected_source_all c hsupport b hb (hp.trans (by decide))

def source (h : ℕ) (e : Entry) : ℕ := h + position e - 1005

theorem source_le {h : ℕ} (hh : h ≤ 1004) (e : Entry) : source h e ≤ 984 := by
  have hp := position_le e
  unfold source
  omega

theorem source_nonselector_coefficient {h : ℕ} (hh : h ≤ 1004) (e : Entry)
    (hs : 942 ≤ source h e) : 943 ≤ position e := by
  unfold source at hs
  omega

theorem source_nonselector_coefficient_strict {h : ℕ} (hh : h ≤ 1003) (e : Entry)
    (hs : 942 ≤ source h e) : 944 ≤ position e := by
  unfold source at hs
  omega

theorem reflected_cell (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 1004) :
    reflected c (b + (h : ZMod (N * 2011))) =
      ∑ e : Entry, if 1005 ≤ h + position e then
        2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0 := by
  unfold reflected
  apply Finset.sum_congr rfl
  intro e _
  rw [reflected_source c hsupport b hb hh (position_le e)]
  split_ifs <;> simp only [source, mul_zero]

/-- The first possible reflected field is20, because the last coefficient
position is985. No earlier-cell source survives the periodic support. -/
theorem reflected_zero_before_twenty (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h < 20) : reflected c (b + (h : ZMod (N * 2011))) = 0 := by
  rw [reflected_cell c hsupport b hb (by omega)]
  apply Finset.sum_eq_zero
  intro e _
  have hp := position_le e
  rw [if_neg (by omega : ¬1005 ≤ h + position e)]

def selectorEntries (h : ℕ) : Finset Entry :=
  Finset.univ.filter (fun e => 1005 ≤ h + position e ∧ source h e < 942)

theorem selector_source_injective (h : ℕ) :
    Set.InjOn (source h) (selectorEntries h : Set Entry) := by
  intro e he f hf hef
  have he' := (Finset.mem_filter.mp he).2.1
  have hf' := (Finset.mem_filter.mp hf).2.1
  apply position_injective
  unfold source at hef
  omega

omit [NeZero (N * 2011)] in
theorem selector_source_sum_le (c : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (h : ℕ) :
    (∑ e ∈ selectorEntries h, c (b + (source h e : ZMod (N * 2011)))) ≤
      ∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011))) := by
  have hsub : (selectorEntries h).image (source h) ⊆ Finset.range 942 := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_range.mpr (Finset.mem_filter.mp he).2.2
  calc
    _ = ∑ f ∈ (selectorEntries h).image (source h), c (b + (f : ZMod (N * 2011))) := by
      symm
      exact Finset.sum_image (selector_source_injective h)
    _ ≤ ∑ f ∈ Finset.range 942, c (b + (f : ZMod (N * 2011))) :=
      Finset.sum_le_sum_of_subset hsub
    _ = _ := (Fin.sum_univ_eq_sum_range _ 942).symm

omit [NeZero (N * 2011)] in
theorem selector_reflection_lt (c : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (h : ℕ)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    (∑ e ∈ selectorEntries h,
      2 * weight e * c (b + (source h e : ZMod (N * 2011)))) < 2 ^ 45 := by
  have hs := selector_source_sum_le c b h
  have hm : (∑ e ∈ selectorEntries h,
      2 * weight e * c (b + (source h e : ZMod (N * 2011)))) ≤
      (2 ^ 45 - 1) * (∑ e ∈ selectorEntries h,
        c (b + (source h e : ZMod (N * 2011)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    apply Nat.mul_le_mul_right
    have hh := doubled_weight_lt e
    omega
  have hc : (∑ e ∈ selectorEntries h,
      c (b + (source h e : ZMod (N * 2011)))) ≤ 1 := hs.trans hone
  have hh := Nat.mul_le_mul_left (2 ^ 45 - 1) hc
  omega

private def controlCoefficient : Entry → ℕ
  | .inl _ => 0
  | .inr e => 2 * weight (.inr e)

omit [NeZero (N * 2011)] in
theorem control_reflection_le (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (b : ZMod (N * 2011))
    {h : ℕ} (hh : h ≤ 1004) :
    (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
      2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0) ≤ 2 ^ 45 - 2048 := by
  have hm (e : Entry) :
      (if 1005 ≤ h + position e ∧ 942 ≤ source h e then
        2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0) ≤
      controlCoefficient e := by
    rcases e with i | e
    · have hp := selector_position_lt i
      have hz : ¬(1005 ≤ h + position (.inl i) ∧ 942 ≤ source h (.inl i)) := by
        intro hs
        have he := source_nonselector_coefficient hh (.inl i) hs.2
        omega
      simp only [if_neg hz, controlCoefficient, le_refl]
    · simp only [controlCoefficient]
      split_ifs
      · exact (Nat.mul_le_mul_left (2 * weight (.inr e)) (hc _)).trans_eq (Nat.mul_one _)
      · exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset Entry)) => hm e)
  have hmass : (∑ e : Entry, controlCoefficient e) = 2 ^ 45 - 2048 := by
    rw [Fintype.sum_sum_type]
    simp only [controlCoefficient, Finset.sum_const_zero, zero_add]
    exact doubled_control_mass
  rw [hmass] at hs
  exact hs

/-- The selector premise is physical at-most-one, with all control bits arbitrary.
This applies through marker1004 as well as the needed reset band0..1003. -/
theorem reflected_lt (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 1004)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    reflected c (b + (h : ZMod (N * 2011))) < 2 * 2 ^ 45 - 2048 := by
  have hs := selector_reflection_lt c b h hone
  have ht := control_reflection_le c hc b hh
  rw [reflected_cell c hsupport b hb hh]
  have he :
      (∑ e : Entry, if 1005 ≤ h + position e then
        2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0) =
      (∑ e ∈ selectorEntries h,
        2 * weight e * c (b + (source h e : ZMod (N * 2011)))) +
      (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
        2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0) := by
    rw [selectorEntries, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hge : 942 ≤ source h e ↔ ¬source h e < 942 := by omega
    by_cases hv : 1005 ≤ h + position e <;>
      by_cases hf : source h e < 942 <;>
        simp only [hv, hf, hge, not_true_eq_false, not_false_eq_true,
          and_true, and_false, if_true, if_false, zero_add, add_zero]
  rw [he]
  omega

/-- The only three non-reflected monomials are each evaluated once. -/
theorem convolution_le_reflected_add_three (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (k : ZMod (N * 2011)) :
    convolution CurrentKernel2011.folded c k ≤ reflected c k + 3 := by
  rw [CurrentKernel2011.convolution_eq]
  have h₁ := hc (k - 18)
  have h₂ := hc (k - 1004)
  have h₃ := hc (k - 2020)
  change _ ≤ (∑ e : Entry, 2 * weight e *
    c (k - ((1005 - position e : ℕ) : ZMod (N * 2011)))) + 3
  omega

/-- A reset bound uses arbitrary Boolean control digits, and any temporal
digits within the unconditional Boolean rotation bound. -/
theorem low_raw_budget (c r : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 46)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 1004)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    convolution CurrentKernel2011.folded c (b + (h : ZMod (N * 2011))) +
      r (b + (h : ZMod (N * 2011))) + 57 < CurrentMasks2011.radix := by
  have he := reflected_lt c hc hsupport b hb hh hone
  have hu := convolution_le_reflected_add_three c hc (b + (h : ZMod (N * 2011)))
  have ht := hr (b + (h : ZMod (N * 2011)))
  change _ < 2 ^ 47
  omega

/-- Every bounded carry solution resets, not only the least cyclic solution. -/
theorem outgoing_carry_zero (c r carry : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 46)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + r k + carry (k - 1)) / CurrentMasks2011.radix)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 1004)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    carry (b + (h : ZMod (N * 2011))) = 0 := by
  rw [hrec]
  apply Nat.div_eq_of_lt
  have hh' := low_raw_budget c r hc hr hsupport b hb hh hone
  have hk' := hk (b + (h : ZMod (N * 2011)) - 1)
  omega

/-- All copy and marker tests at offsets1..1004 have zero incoming carry.
In particular this includes960..968,987..994, and1004. -/
theorem incoming_carry_zero (c r carry : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 46)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + r k + carry (k - 1)) / CurrentMasks2011.radix)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hpos : 1 ≤ h) (hh : h ≤ 1004)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    carry (b + (h : ZMod (N * 2011)) - 1) = 0 := by
  have he : b + (h : ZMod (N * 2011)) - 1 =
      b + ((h - 1 : ℕ) : ZMod (N * 2011)) := by
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  rw [he]
  exact outgoing_carry_zero c r carry hc hr hsupport hk hrec b hb (by omega) hone

theorem copy_marker_incoming_zero (c r carry : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 46)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + r k + carry (k - 1)) / CurrentMasks2011.radix)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (htest : (960 ≤ h ∧ h ≤ 968) ∨ (987 ≤ h ∧ h ≤ 994) ∨ h = 1004)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    carry (b + (h : ZMod (N * 2011)) - 1) = 0 :=
  incoming_carry_zero c r carry hc hr hsupport hk hrec b hb (by omega) (by omega) hone

end DiophantineConsistency.CurrentReflectedGeometry2011
