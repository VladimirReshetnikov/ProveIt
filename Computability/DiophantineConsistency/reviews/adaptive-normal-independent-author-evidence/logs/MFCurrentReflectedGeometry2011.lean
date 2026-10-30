import DiophantineConsistency.ReflectedSource
import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.ArithmeticCellPhysical
import DiophantineConsistency.MFNativeCyclicConvolution
import DiophantineConsistency.MFWangTiles942Core
import DiophantineConsistency.MFWangTiles942Permutation
import DiophantineConsistency.NativeCyclicCarry
import DiophantineConsistency.SplitCertificate59
import DiophantineConsistency.WangTiles942Data
import DiophantineConsistency.WangTiles942TableData
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.Zify

/-! Matrix-free variant of `DiophantineConsistency.CurrentReflectedGeometry2011`:
the declarations needed for local normalization are retained, with geometry
facts shared from `ArithmeticCellPhysical`. -/
/-!
# Reflected geometry and conditional low-field resets

All reflected terms of the literal current kernel are retained. The low
support proves that a surviving reflected source lies in the same cell.
The reset theorem explicitly assumes at most one physical selector in that
cell. It assumes neither decoded labels nor temporal phase alignment.
-/

namespace DiophantineConsistency.MF.CurrentReflectedGeometry2011

open DiophantineConsistency.MF.CurrentKernel2011 DiophantineConsistency.CurrentKernel2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.WangTiles942 DiophantineConsistency.WangTiles942 DiophantineConsistency.MF.NativeCyclicConvolution
open scoped BigOperators

set_option Elab.async false

abbrev Control := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

theorem position_injective : Function.Injective position := by
  exact ArithmeticCellPhysical.position_injective

theorem doubled_weight_lt (e : Entry) : 2 * weight e < 2 ^ 45 := by
  exact ArithmeticCellPhysical.doubled_weight_lt e

theorem doubled_control_mass :
    (∑ e : Control, 2 * weight (.inr e)) = 2 ^ 45 - 2048 := by
  exact ArithmeticCellPhysical.doubled_control_mass

theorem support_le {f : ℕ} (hf : f ∈ lowSupport) : f ≤ 1004 := by
  rw [lowSupport_def] at hf
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hf
  omega

theorem selector_position_lt (i : Fin 942) : position (.inl i) < 942 :=
  physicalPosition_lt i

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

/-- A negative same-cell offset wraps into unsupported residues1006..2010.
Otherwise the source is exactly the nonnegative offset h+p−1005. -/
theorem reflected_source (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (hh : h ≤ 1004) (hp : p ≤ 985) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 := by
  exact ReflectedSource.source c ↑lowSupport (fun f hf => support_le hf) hsupport b hb hh hp

def source (h : ℕ) (e : Entry) : ℕ := h + position e - 1005

theorem source_nonselector_coefficient {h : ℕ} (hh : h ≤ 1004) (e : Entry)
    (hs : 942 ≤ source h e) : 943 ≤ position e := by
  exact ArithmeticCellPhysical.source_nonselector_coefficient hh e hs

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

def selectorEntries (h : ℕ) : Finset Entry :=
  Finset.univ.filter (fun e => 1005 ≤ h + position e ∧ source h e < 942)

theorem selector_source_injective (h : ℕ) :
    Set.InjOn (source h) (selectorEntries h : Set Entry) := by
  exact ArithmeticCellPhysical.selector_source_injective h

omit [NeZero (N * 2011)] in
theorem selector_source_sum_le (c : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (h : ℕ) :
    (∑ e ∈ selectorEntries h, c (b + (source h e : ZMod (N * 2011)))) ≤
      ∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011))) := by
  have hr := ArithmeticCellPhysical.selector_sum_le h (fun j => c (b + (j : ZMod (N * 2011))))
  exact hr.trans_eq (Fin.sum_univ_eq_sum_range _ 942).symm

omit [NeZero (N * 2011)] in
theorem selector_reflection_lt (c : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (h : ℕ)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    (∑ e ∈ selectorEntries h,
      2 * weight e * c (b + (source h e : ZMod (N * 2011)))) < 2 ^ 45 := by
  exact ArithmeticCellPhysical.selector_weighted_lt h (fun j => c (b + (j : ZMod (N * 2011))))
    ((selector_source_sum_le c b h).trans hone)

omit [NeZero (N * 2011)] in
theorem control_reflection_le (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (b : ZMod (N * 2011))
    {h : ℕ} (hh : h ≤ 1004) :
    (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
      2 * weight e * c (b + (source h e : ZMod (N * 2011))) else 0) ≤ 2 ^ 45 - 2048 := by
  exact ArithmeticCellPhysical.reflected_control_le hh _ (fun e => hc _)

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
    exact ArithmeticCellPhysical.reflected_split h _
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

end DiophantineConsistency.MF.CurrentReflectedGeometry2011
