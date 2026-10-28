import DiophantineConsistency.CurrentReflectedGeometry2011
import DiophantineConsistency.CurrentSelectorTail2011
import DiophantineConsistency.CurrentClause2011

/-!
# The actual 483 padding tests before selector-count recovery

The exact coefficient tail resets the early band without onehot or label
decoding. At fields64..546 the reflected residue counts successive physical
selector prefixes. The complete high mask supplies the actual bit-three
tests. Temporal bounds/divisibility are explicit and require no alignment.
-/

namespace DiophantineConsistency.CurrentEarlyPadding2011

open CurrentKernel2011 CurrentMasks2011 WangTiles942 NativeCyclicConvolution
  CurrentReflectedGeometry2011 PaddingStaircase
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The suffix of coefficient positions is a prefix of source positions. -/
theorem shifted_suffix_sum (a : ℕ → ℕ) {j : ℕ} (hj : j ≤ 942) :
    (∑ p ∈ Finset.range 942, if 942 ≤ j + p then a (j + p - 942) else 0) =
      prefixSum a j := by
  have hn : 942 = (942 - j) + j := by omega
  have hz : (∑ p ∈ Finset.range (942 - j),
      if 942 ≤ j + p then a (j + p - 942) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_range.mp hp
    rw [if_neg (by omega : ¬942 ≤ j + p)]
  calc
    _ = ∑ p ∈ Finset.range ((942 - j) + j),
        if 942 ≤ j + p then a (j + p - 942) else 0 :=
      congrArg (fun n => ∑ p ∈ Finset.range n,
        if 942 ≤ j + p then a (j + p - 942) else 0) hn
    _ = _ := by
      rw [Finset.sum_range_add, hz, zero_add]
      unfold prefixSum
      apply Finset.sum_congr rfl
      intro p _
      rw [if_pos (by omega : 942 ≤ j + (942 - j + p)),
        show j + (942 - j + p) - 942 = p by omega]

variable {N : ℕ} [NeZero (N * 2011)]

theorem early_reflected_bound (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 546) :
    reflected c (b + (h : ZMod (N * 2011))) ≤ 137820284543942 := by
  apply CurrentSelectorTail2011.tail_source_bound
    (fun e => c (b + (h : ZMod (N * 2011)) - ((1005 - position e : ℕ) : ZMod (N * 2011))))
  · intro e
    exact hc _
  · intro e he
    rw [reflected_source c hsupport b hb (by omega) (position_le e)]
    rw [if_neg (by omega : ¬1005 ≤ h + position e)]

theorem early_raw_budget (c r : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 10)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 546) :
    convolution CurrentKernel2011.folded c (b + (h : ZMod (N * 2011))) +
      r (b + (h : ZMod (N * 2011))) + 57 < CurrentMasks2011.radix := by
  have he := early_reflected_bound c hc hsupport b hb hh
  have hu := convolution_le_reflected_add_three c hc (b + (h : ZMod (N * 2011)))
  have ht := hr (b + (h : ZMod (N * 2011)))
  have hn := CurrentSelectorTail2011.early_reset_numeric
  change 137820284543942 + 2 ^ 10 + 60 < CurrentMasks2011.radix at hn
  omega

/-- The local normalization identity alone suffices; a division formula or
prior zero incoming carry is not an additional premise. -/
theorem early_carry_zero (c r carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 10)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + r k + carry (k - 1) =
      digits k + CurrentMasks2011.radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (hh : h ≤ 546) : carry (b + (h : ZMod (N * 2011))) = 0 := by
  have hbudget := early_raw_budget c r hc hr hsupport b hb hh
  have hin := hk (b + (h : ZMod (N * 2011)) - 1)
  have he := hlocal (b + (h : ZMod (N * 2011)))
  change _ < 2 ^ 47 at hbudget
  change _ = _ + 2 ^ 47 * _ at he
  omega

private def selectorUnit : Entry → ℕ
  | .inl _ => 2
  | .inr _ => 0

private theorem reflected_mod_sixteen (e : Entry) :
    2 * weight e ≡ selectorUnit e [MOD 16] := by
  exact (CurrentClause2011.reflected_weight_mod e).of_dvd (by decide : 16 ∣ 2048)

omit [NeZero (N * 2011)] in
theorem reflected_mod_selector_sources (c : ZMod (N * 2011) → ℕ)
    (k : ZMod (N * 2011)) :
    reflected c k ≡ 2 * (∑ i : Fin 942,
      c (k - ((1005 - physicalPosition i : ℕ) : ZMod (N * 2011)))) [MOD 16] := by
  have hs := Nat.ModEq.sum (s := Finset.univ) (fun e _ =>
    (reflected_mod_sixteen e).mul_right
      (c (k - ((1005 - position e : ℕ) : ZMod (N * 2011)))))
  have he : (∑ e : Entry, selectorUnit e *
      c (k - ((1005 - position e : ℕ) : ZMod (N * 2011)))) =
      2 * (∑ i : Fin 942,
        c (k - ((1005 - physicalPosition i : ℕ) : ZMod (N * 2011)))) := by
    simp only [Fintype.sum_sum_type, selectorUnit, zero_mul, Finset.sum_const_zero,
      add_zero, position, Finset.mul_sum]
  rw [he] at hs
  exact hs

/-- The actual physical permutation identifies every prefix, including its
first and last positions, without a supplied permutation or tile decoding. -/
theorem selector_sources_eq_prefix (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    (∑ i : Fin 942, c (b + ((63 + j : ℕ) : ZMod (N * 2011)) -
      ((1005 - physicalPosition i : ℕ) : ZMod (N * 2011)))) =
      prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j := by
  have he (i : Fin 942) :
      c (b + ((63 + j : ℕ) : ZMod (N * 2011)) -
        ((1005 - physicalPosition i : ℕ) : ZMod (N * 2011))) =
      if 942 ≤ j + physicalPosition i then
        c (b + ((j + physicalPosition i - 942 : ℕ) : ZMod (N * 2011))) else 0 := by
    rw [reflected_source c hsupport b hb (by omega)
      ((physicalPosition_lt i).le.trans (by decide : 942 ≤ 985))]
    have hv : (1005 ≤ 63 + j + physicalPosition i) ↔ 942 ≤ j + physicalPosition i := by omega
    simp only [hv, show 63 + j + physicalPosition i - 1005 = j + physicalPosition i - 942 by omega]
  have hp := Equiv.sum_comp physicalEquiv (fun p : Fin 942 =>
    if 942 ≤ j + p.val then c (b + ((j + p.val - 942 : ℕ) : ZMod (N * 2011))) else 0)
  change (∑ i : Fin 942, if 942 ≤ j + physicalPosition i then
      c (b + ((j + physicalPosition i - 942 : ℕ) : ZMod (N * 2011))) else 0) = _ at hp
  have hf : (∑ p : Fin 942, if 942 ≤ j + p.val then
      c (b + ((j + p.val - 942 : ℕ) : ZMod (N * 2011))) else 0) =
      prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j := by
    rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
      if 942 ≤ j + p then c (b + ((j + p - 942 : ℕ) : ZMod (N * 2011))) else 0) 942]
    exact shifted_suffix_sum (fun f => c (b + (f : ZMod (N * 2011)))) (by omega)
  calc
    _ = ∑ i : Fin 942, if 942 ≤ j + physicalPosition i then
        c (b + ((j + physicalPosition i - 942 : ℕ) : ZMod (N * 2011))) else 0 :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = ∑ p : Fin 942, if 942 ≤ j + p.val then
        c (b + ((j + p.val - 942 : ℕ) : ZMod (N * 2011))) else 0 := hp
    _ = _ := hf

theorem reflected_padding_residue (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    reflected c (b + ((63 + j : ℕ) : ZMod (N * 2011))) ≡
      2 * prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j [MOD 16] := by
  have hm := reflected_mod_selector_sources c (b + ((63 + j : ℕ) : ZMod (N * 2011)))
  rwa [selector_sources_eq_prefix c hsupport b hb hj] at hm

/-- The actual shared18 and spatial2020 inputs; no decoded interpretation
is needed for either digit to be Boolean. -/
def paddingUnit (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) (j : ℕ) : ℕ :=
  c (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 18) +
    c (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 2020)

def paddingDigit (digits : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (j : ℕ) : ℕ :=
  digits (b + ((63 + j : ℕ) : ZMod (N * 2011)))

omit [NeZero (N * 2011)] in
theorem paddingUnit_le_two (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (b : ZMod (N * 2011)) (j : ℕ) :
    paddingUnit c b j ≤ 2 := by
  have ha := hc (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 18)
  have hb := hc (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 2020)
  unfold paddingUnit
  omega

theorem bare_marker_input_zero (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    c (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 1004) = 0 := by
  have hh := reflected_source c hsupport b hb
    (h := 63 + j) (p := 1) (by omega) (by decide)
  rw [if_neg (by omega : ¬1005 ≤ 63 + j + 1)] at hh
  exact hh

theorem padding_convolution (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    convolution CurrentKernel2011.folded c (b + ((63 + j : ℕ) : ZMod (N * 2011))) =
      paddingUnit c b j + reflected c (b + ((63 + j : ℕ) : ZMod (N * 2011))) := by
  rw [CurrentKernel2011.convolution_eq, bare_marker_input_zero c hsupport b hb hj, add_zero]
  rfl

theorem padding_convolution_residue (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    convolution CurrentKernel2011.folded c (b + ((63 + j : ℕ) : ZMod (N * 2011))) ≡
      2 * prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j + paddingUnit c b j [MOD 16] := by
  rw [padding_convolution c hsupport b hb hj]
  exact ((reflected_padding_residue c hsupport b hb hj).add_left (paddingUnit c b j)).trans
    (by rw [Nat.add_comm])

theorem padding_incoming_zero (c r carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 10)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + r k + carry (k - 1) =
      digits k + CurrentMasks2011.radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    carry (b + ((63 + j : ℕ) : ZMod (N * 2011)) - 1) = 0 := by
  have he : b + ((63 + j : ℕ) : ZMod (N * 2011)) - 1 =
      b + ((62 + j : ℕ) : ZMod (N * 2011)) := by
    push_cast
    ring
  rw [he]
  exact early_carry_zero c r carry digits hc hr hsupport hk hlocal b hb (by omega)

/-- The normalized physical digit has the staircase residue. The temporal
term is removed only by explicit divisibility, never by alignment. -/
theorem padding_digit_residue (c r carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 10)
    (hrmod : ∀ k, r k % 16 = 0)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + r k + carry (k - 1) =
      digits k + CurrentMasks2011.radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    paddingDigit digits b j % 16 =
      (2 * prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j + paddingUnit c b j) % 16 := by
  have hz := padding_incoming_zero c r carry digits hc hr hsupport hk hlocal b hb hj
  have he := hlocal (b + ((63 + j : ℕ) : ZMod (N * 2011)))
  rw [hz, add_zero] at he
  have hm : paddingDigit digits b j ≡
      convolution CurrentKernel2011.folded c (b + ((63 + j : ℕ) : ZMod (N * 2011))) +
        r (b + ((63 + j : ℕ) : ZMod (N * 2011))) [MOD 16] := by
    change _ % 16 = _ % 16
    rw [he]
    simp only [Nat.add_mod, Nat.mul_mod,
      show CurrentMasks2011.radix % 16 = 0 from by decide,
      Nat.zero_mul, Nat.zero_mod, add_zero, Nat.mod_mod, paddingDigit]
  have ht : r (b + ((63 + j : ℕ) : ZMod (N * 2011))) ≡ 0 [MOD 16] := hrmod _
  have hh := hm.trans ((padding_convolution_residue c hsupport b hb hj).add ht)
  simpa only [Nat.ModEq, add_zero] using hh

theorem padding_target_residue (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    (b + ((63 + j : ℕ) : ZMod (N * 2011))).val % 2011 = 63 + j := by
  rw [CurrentClause2011.addition_residue]
  simp only [Nat.add_mod, hb, zero_add,
    Nat.mod_eq_of_lt (by omega : 63 + j < 2011)]

/-- Every staircase mask is an actual bit-three test of the full repeated
high mask; none of these positions is the exceptional global origin. -/
theorem padding_mask (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) :
    CurrentHighDigits2011.maskDigits (b + ((63 + j : ℕ) : ZMod (N * 2011))) = 8 := by
  have hres := padding_target_residue b hb hj
  have hn : b + ((63 + j : ℕ) : ZMod (N * 2011)) ≠ 0 := by
    intro hz
    rw [hz, ZMod.val_zero, Nat.zero_mod] at hres
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn, hres]
  exact CurrentHighDigits2011.cellDigit_padding ⟨by omega, by omega⟩

theorem padding_digit_mask (digits : ZMod (N * 2011) → ℕ)
    (hmask : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {j : ℕ} (hj : j ≤ 483) : paddingDigit digits b j &&& 8 = 0 := by
  simpa only [padding_mask b hb hj, paddingDigit] using
    hmask (b + ((63 + j : ℕ) : ZMod (N * 2011)))

/-- All483 physical bindings needed by the generic preliminary-count lemma.
No one-selector bound, decoded labels, or temporal alignment is assumed. -/
theorem padding_bindings (c r carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 2 ^ 10)
    (hrmod : ∀ k, r k % 16 = 0)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + r k + carry (k - 1) =
      digits k + CurrentMasks2011.radix * carry k)
    (hmask : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (∀ j, 1 ≤ j → j ≤ 483 → paddingUnit c b j ≤ 2) ∧
    (∀ j, 1 ≤ j → j ≤ 483 → paddingDigit digits b j % 16 =
      (2 * prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j + paddingUnit c b j) % 16) ∧
    (∀ j, 1 ≤ j → j ≤ 483 → paddingDigit digits b j &&& 8 = 0) := by
  refine ⟨fun j _ _ => paddingUnit_le_two c hc b j, ?_, ?_⟩
  · intro j _ hj
    exact padding_digit_residue c r carry digits hc hr hrmod hsupport hk hlocal b hb hj
  · intro j _ hj
    exact padding_digit_mask digits hmask b hb hj

end DiophantineConsistency.CurrentEarlyPadding2011
