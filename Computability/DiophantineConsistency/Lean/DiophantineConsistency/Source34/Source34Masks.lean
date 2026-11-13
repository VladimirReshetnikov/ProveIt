import DiophantineConsistency.Source34.Source34Ports
import DiophantineConsistency.ArithmeticMaskConstants
import DiophantineConsistency.ArithmeticMaskData

/-! # Population and residue facts of the source34 masks

These are the five mask facts that the port-generic
`FreeJSaturationClient.graph_saturation` consumes. They are the recipe's §3
facts:

* `MC < 2^d` and `MF_native < 2^d`, with `d = 121·8801`;
* `MC ≡ 0 (mod 2)` and `MF_native ≡ 4 (mod 8)`;
* `popcount(MC) + popcount(MF_native) = d`. Separately,
  `popcount(MC) = d − 989` and `popcount(MF_native) = 989`.

The populations are sums of per-digit popcounts (`population_ofDigits`). The
kernel evaluates only the popcounts of the six distinct digit values
(`pcF 121`). The mask support has 988 elements, including the special cell
`1063`. No million-bit numeral is materialized. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
noncomputable section
namespace Source34Masks
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryPopulation ArithmeticMaskConstants
open ArithmeticMaskData (pcF)
open Source34Ports CompactListMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The support -/

theorem filter_nodup : (Source34Kernel.support.filter (· ≠ 1)).Nodup :=
  Source34Kernel.support_nodup.filter _

theorem filter_length : (Source34Kernel.support.filter (· ≠ 1)).length = 988 := by
  decide +kernel

theorem support_card : maskSupport.card = 988 := by
  unfold maskSupport
  rw [List.toFinset_card_of_nodup filter_nodup, filter_length]

theorem special_mem : (1063:ℕ) ∈ maskSupport := by
  unfold maskSupport
  rw [List.mem_toFinset, List.mem_filter]
  refine ⟨?_, by decide⟩
  unfold Source34Kernel.support
  exact List.mem_append_right _ (by simp)

theorem support_bounded : maskSupport ⊆ Finset.range 8801 := by
  intro x hx
  unfold maskSupport at hx
  rw [List.mem_toFinset, List.mem_filter] at hx
  have h := (List.all_eq_true.mp Source34Kernel.support_below_target) x hx.1
  rw [Finset.mem_range]
  have : x < 4393 := of_decide_eq_true h
  omega

/-! ## Populations -/

attribute [local irreducible] maskSupport Source34Kernel.support

private theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  have hr : (List.range n).toFinset = Finset.range n := by ext; simp
  simpa only [hr] using (List.sum_toFinset f (List.nodup_range (n := n))).symm

private theorem pop_ones : pcF 121 (radix-1) = 121 := by unfold radix; decide +kernel
private theorem pop_ordinary : pcF 121 (radix-2) = 120 := by unfold radix; decide +kernel
private theorem pop_special : pcF 121 (radix-4) = 119 := by unfold radix; decide +kernel

/-- `lowNat` and `highNat` with the radix written as `2^121`, the form of
`population_ofDigits`; `rfl` unfolds only `radix`. -/
theorem lowNat_eq : lowNat = Nat.ofDigits (2^121) (digits radix 8801 1063 maskSupport) := rfl
theorem highNat_eq : highNat = Nat.ofDigits (2^121) highDigits := rfl

/-- The low-mask list population for an arbitrary length, special cell and
support. It is generic so that no concrete digit list is ever available to
reduce. The concrete form, stated directly, timed out in `whnf`. This is
Compact44's `list_population_general` at width `121`. -/
theorem list_population_general (len special : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range len) (hspecial : special ∈ S) :
    ((digits radix len special S).map (pcF 121)).sum + S.card + 1 = len*121 := by
  have hspecial_range : special ∈ Finset.range len := hS hspecial
  simp only [digits, List.map_map]
  rw [sum_map_range]
  have hpoint (j : ℕ) : pcF 121 (digit radix special S j) +
      (if j ∈ S then 1 else 0) + (if j = special then 1 else 0) = 121 := by
    by_cases hs : j = special
    · subst j
      simp only [digit, if_pos hspecial, if_true]
      rw [pop_special]
    · by_cases hj : j ∈ S
      · simp only [digit, if_neg hs, if_pos hj]
        rw [pop_ordinary]
      · simp only [digit, if_neg hs, if_neg hj]
        rw [pop_ones]
  have he : (∑ j ∈ Finset.range len, (pcF 121 (digit radix special S j) +
      (if j ∈ S then 1 else 0) + (if j = special then 1 else 0))) = len*121 := by
    simp_rw [hpoint]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at he
  have hs : (∑ j ∈ Finset.range len, if j ∈ S then 1 else 0) = S.card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hS]
    simp
  have hexc : (∑ j ∈ Finset.range len, if j = special then 1 else 0) = 1 := by
    simp [hspecial_range]
  rw [hs, hexc] at he
  exact he

theorem low_list_population :
    ((digits radix 8801 1063 maskSupport).map (pcF 121)).sum + 988 + 1 = 8801*121 := by
  have h := list_population_general 8801 1063 maskSupport support_bounded special_mem
  rw [support_card] at h
  exact h

theorem low_digit_lt (x : ℕ) (hx : x ∈ digits radix 8801 1063 maskSupport) : x < 2^121 := by
  have h := digits_lt radix 8801 1063 maskSupport (by unfold radix; norm_num) x hx
  simpa only [radix] using h

theorem model_low_population : population ((lowNat : ℕ) : V) = 1063932 := by
  have h := population_ofDigits (V:=V) 121 (digits radix 8801 1063 maskSupport) low_digit_lt
  have hl := low_list_population
  have hs : ((digits radix 8801 1063 maskSupport).map (pcF 121)).sum = 1063932 := by omega
  rw [hs] at h
  rw [lowNat_eq, h, Nat.cast_ofNat]

private theorem pop_zero : pcF 121 0 = 0 := by decide +kernel
private theorem pop_one : pcF 121 1 = 1 := by decide +kernel
private theorem pop_four : pcF 121 4 = 1 := by decide +kernel
theorem mu_eq : mu = 105637550019019116791391934462 := by
  unfold mu Mixed121Kernel.W
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
private theorem pop_mu : pcF 121 mu = 53 := by rw [mu_eq]; decide +kernel
private theorem pop_padding : pcF 121 padding = 119 := by unfold padding; decide +kernel
private theorem pop_last : pcF 121 lastPadding = 27 := by unfold lastPadding; decide +kernel

theorem high_list_population : (highDigits.map (pcF 121)).sum = 989 := by
  simp only [highDigits, highInit, track, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil,
    pop_zero, pop_one, pop_four, pop_mu, pop_padding, pop_last, smul_eq_mul]
  norm_num

theorem high_digit_lt (x : ℕ) (hx : x ∈ highDigits) : x < 2^121 := by
  unfold highDigits at hx
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · simpa only [radix] using highInit_digit_lt x hx
  · norm_num

theorem model_high_population : population ((highNat : ℕ) : V) = 989 := by
  have h := population_ofDigits (V:=V) 121 highDigits high_digit_lt
  rw [high_list_population] at h
  rw [highNat_eq, h, Nat.cast_ofNat]

theorem model_population_sum :
    population ((lowNat : ℕ) : V) + population ((highNat : ℕ) : V) = (121:V)*8801 := by
  rw [model_low_population, model_high_population]
  norm_num

/-! ## Bounds and residues -/

theorem model_low_lt : ((lowNat : ℕ) : V) < Exp.exp ((121:V)*8801) := by
  have h := ofDigits_lt_exp (V:=V) 121 (digits radix 8801 1063 maskSupport) low_digit_lt
  have hlen : (digits radix 8801 1063 maskSupport).length = 8801 := by
    simp only [digits, List.length_map, List.length_range]
  rw [hlen] at h
  rw [lowNat_eq]
  simpa only [Nat.cast_ofNat] using h

theorem model_high_lt : ((highNat : ℕ) : V) < Exp.exp ((121:V)*8801) := by
  have h := ofDigits_lt_exp (V:=V) 121 highDigits high_digit_lt
  rw [highDigits_length] at h
  rw [highNat_eq]
  simpa only [Nat.cast_ofNat] using h

/-! The parity proofs never touch the 8801-term sums or `generalize` over
concrete terms. Each mask is split as its cell-0 digit plus `radix·T` by
generic list lemmas, and the arithmetic is a lemma over the variable `T`. A
defect-sum version did not finish in 47 minutes. -/

/-- Peel cell 0 off a mask digit list; generic in all arguments. -/
theorem digits_succ (B n special : ℕ) (S : Finset ℕ) :
    digits B (n+1) special S =
      digit B special S 0 :: (List.range n).map (fun j => digit B special S (j+1)) := by
  unfold digits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

private theorem even_of_head (T : ℕ) : (radix - 2 + radix * T) % 2 = 0 := by
  have h1 : (radix - 2) % 2 = 0 := by unfold radix; norm_num
  have h2 : radix * T = 2 * (2^120 * T) := by unfold radix; ring
  rw [Nat.add_mod, h1, h2, Nat.mul_mod_right]

private theorem mod_eight_of (T : ℕ) : (4 + radix * T) % 8 = 4 := by
  have hr : radix * T = 8 * (2^118 * T) := by unfold radix; ring
  rw [hr, Nat.add_mul_mod_self_left]

theorem low_digit_zero : digit radix 1063 maskSupport 0 = radix - 2 := by
  simp only [digit, if_neg (by norm_num : (0:ℕ) ≠ 1063), if_pos Source34Ports.zero_mem_support]

/-! The masks are opened by `rw` with `rfl` lemmas, never `unfold` or `delta`.
A definitional goal change leaves the kernel the obligation
`Nat.ofDigits … % 2 = 0 ≡ lowNat % 2 = 0`, and its Nat-literal extension then
evaluates `lowNat` to a numeral (8801 digits with support lookups). `rw` leaves
only `lowNat ≡ body`, which one delta step settles. -/
theorem lowNat_def : lowNat = Nat.ofDigits radix (digits radix 8801 1063 maskSupport) := rfl
theorem highNat_def : highNat = Nat.ofDigits radix highDigits := rfl
theorem highDigits_def : highDigits = highInit ++ [0] := rfl
theorem highInit_def : highInit =
    [4] ++ List.replicate 999 0 ++ track ++ [0] ++ track ++ List.replicate 1154 0 ++ [1] ++
    List.replicate 1100 0 ++ [1] ++
    List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++
    List.replicate 3296 0 ++ List.replicate 7 padding ++ [lastPadding] := rfl

/-- `digits_succ` at `8801 = 8800 + 1`. Stated with the literal `8801`, so that
rewriting the goal is syntactic; otherwise `8800 + 1` against `8801` under
`Nat.mod` makes the kernel evaluate the mask. -/
theorem digits_8801 : digits radix 8801 1063 maskSupport =
    digit radix 1063 maskSupport 0 ::
      (List.range 8800).map (fun j => digit radix 1063 maskSupport (j+1)) :=
  digits_succ radix 8800 1063 maskSupport

theorem low_even_nat : lowNat % 2 = 0 := by
  rw [lowNat_def, digits_8801, Nat.ofDigits_cons, low_digit_zero]
  exact even_of_head _

theorem high_mod_eight_nat : highNat % 8 = 4 := by
  rw [highNat_def, highDigits_def, highInit_def]
  simp only [List.append_assoc, List.cons_append, Nat.ofDigits_cons]
  exact mod_eight_of _

theorem model_low_even : ((lowNat : ℕ) : V) % 2 = 0 := by
  have h := cast_mod (V:=V) lowNat 2
  rw [low_even_nat] at h
  simp only [Nat.cast_zero, Nat.cast_ofNat] at h
  exact h.symm

theorem model_high_mod_eight : ((highNat : ℕ) : V) % 8 = 4 := by
  have h := cast_mod (V:=V) highNat 8
  rw [high_mod_eight_nat] at h
  simp only [Nat.cast_ofNat] at h
  exact h.symm
end Source34Masks
#print axioms Source34Masks.support_card
#print axioms Source34Masks.low_list_population
#print axioms Source34Masks.model_low_population
#print axioms Source34Masks.high_list_population
#print axioms Source34Masks.model_high_population
#print axioms Source34Masks.model_population_sum
#print axioms Source34Masks.model_low_lt
#print axioms Source34Masks.model_high_lt
#print axioms Source34Masks.low_even_nat
#print axioms Source34Masks.high_mod_eight_nat
#print axioms Source34Masks.model_low_even
#print axioms Source34Masks.model_high_mod_eight
