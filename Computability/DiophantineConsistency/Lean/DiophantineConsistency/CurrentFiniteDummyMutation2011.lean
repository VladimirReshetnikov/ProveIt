import DiophantineConsistency.CurrentDummySafety2011

/-!
# Finite sets of actual safe dummy updates

The original zero-dummy normalization is fixed. Each insertion constructs an
actual new Boolean word and derives its ordinary increment from physical
safety. No aggregate nonwrapping bound or desired F increment is supplied.
This module does not choose the finite support or a modular target.
-/

namespace DiophantineConsistency.CurrentFiniteDummyMutation2011

open CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentDummyMutation2011 CurrentDummySafety2011 NativeRankVariation
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

/-- The actual Boolean dummy controls for an arbitrary finite set of cells. -/
def enabled {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) : ℕ :=
  if j ∈ S then 1 else 0

def powerSum {N : ℕ} (S : Finset (ZMod N)) : ℕ :=
  ∑ j ∈ S, (radix^2011)^j.val

def totalIncrement {N : ℕ} (S : Finset (ZMod N)) : ℕ :=
  radix^977*powerSum S

theorem enabled_boolean {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) : enabled S j ≤ 1 := by
  unfold enabled
  split_ifs <;> omega

theorem enabled_empty {N : ℕ} : enabled (∅ : Finset (ZMod N)) = fun _ => 0 := by
  funext j
  simp only [enabled,Finset.notMem_empty,if_false]

theorem enabled_not_mem {N : ℕ} {S : Finset (ZMod N)} {j : ZMod N} (hj : j ∉ S) :
    enabled S j = 0 := by simp only [enabled,if_neg hj]

theorem enabled_insert {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) :
    enabled (insert j S) = Function.update (enabled S) j 1 := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [enabled,Finset.mem_insert_self,if_true,Function.update_self]
  · rw [Function.update_of_ne hi]
    simp only [enabled,Finset.mem_insert,hi,false_or]

theorem powerSum_empty {N : ℕ} : powerSum (∅ : Finset (ZMod N)) = 0 := by
  simp only [powerSum,Finset.sum_empty]

theorem powerSum_insert {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) (hj : j ∉ S) :
    powerSum (insert j S) = (radix^2011)^j.val+powerSum S := by
  exact Finset.sum_insert hj

theorem totalIncrement_empty {N : ℕ} : totalIncrement (∅ : Finset (ZMod N)) = 0 := by
  rw [totalIncrement,powerSum_empty,Nat.mul_zero]

theorem totalIncrement_insert {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) (hj : j ∉ S) :
    totalIncrement (insert j S) = totalIncrement S+dummyIncrement j := by
  rw [totalIncrement,powerSum_insert S j hj,Nat.mul_add]
  exact Nat.add_comm _ _

/-- Cast the complete natural sum, without changing its finite index set. -/
theorem powerSum_cast {N : ℕ} (R : Type*) [Semiring R] (S : Finset (ZMod N)) :
    (powerSum S : R) = ∑ j ∈ S, ((radix : R)^2011)^j.val := by
  simp only [powerSum,Nat.cast_sum,Nat.cast_pow]

variable {N : ℕ} [NeZero N]

/-- The ordinary source sum is independent of marker bounds and carries. -/
theorem source_enabled_sum (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (S : Finset (ZMod N)) :
    NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (enabled S) marker) =
      NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (fun _ => 0) marker)+
        totalIncrement S := by
  induction S using Finset.induction_on with
  | empty => rw [enabled_empty,totalIncrement_empty,Nat.add_zero]
  | @insert j S hj ih =>
      rw [enabled_insert,source_increment a (enabled S) marker j (enabled_not_mem hj),ih,
        totalIncrement_insert S j hj,Nat.add_assoc]

private theorem exists_normalization_sum (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (hm : ∀ j, marker j ≤ 1) (s : ℕ) (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N)
    (carry0 digits0 : ZMod (N*2011) → ℕ)
    (hf0 : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (fun _ => 0) marker) (displacement s) carry0 digits0) :
    ∃ carry digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a (enabled S) marker) (displacement s) carry digits ∧
      NativeCyclicConvolution.word radix digits = NativeCyclicConvolution.word radix digits0+
        (CurrentKernel2011.K+2^(displacement s))*totalIncrement S := by
  revert hsafe
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨carry0,digits0,?_,?_⟩
      · simpa only [enabled_empty] using hf0
      · rw [totalIncrement_empty,Nat.mul_zero,Nat.add_zero]
  | @insert j S hj ih =>
      intro hsafe
      have hsub : ∀ i ∈ S, i.val+1 < N ∧ i.val+s < N :=
        fun i hi => hsafe i (Finset.mem_insert_of_mem hi)
      obtain ⟨carry,digits,hf,he⟩ := ih hsub
      have hjbounds := hsafe j (Finset.mem_insert_self j S)
      obtain ⟨carry',digits',hf',_,hstep⟩ := exists_safe_normalized_increment
        a (enabled S) marker (enabled_boolean S) hm s j (enabled_not_mem hj)
        hjbounds.1 hjbounds.2 carry digits hf
      refine ⟨carry',digits',?_,?_⟩
      · simpa only [enabled_insert] using hf'
      · rw [hstep,he,totalIncrement_insert S j hj,Nat.mul_add,Nat.add_assoc]

/-- The same original F determines every actual normalization of the final
enabled word. No desired sum identity or nonwrapping hypothesis is supplied. -/
theorem finite_normalized_increment (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (hm : ∀ j, marker j ≤ 1) (s : ℕ) (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N)
    (carry0 digits0 carry digits : ZMod (N*2011) → ℕ)
    (hf0 : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (fun _ => 0) marker) (displacement s) carry0 digits0)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (enabled S) marker) (displacement s) carry digits) :
    NativeCyclicConvolution.word radix digits = NativeCyclicConvolution.word radix digits0+
      (CurrentKernel2011.K+2^(displacement s))*totalIncrement S := by
  obtain ⟨k',f',hf',he⟩ := exists_normalization_sum a marker hm s S hsafe carry0 digits0 hf0
  have hlt := (normalized_word_strict a (enabled S) marker
    (enabled_boolean S) hm s carry digits hf).2
  have hlt' := (normalized_word_strict a (enabled S) marker
    (enabled_boolean S) hm s k' f' hf').2
  have hh := (hf.transport.symm.trans hf'.transport).eq_of_lt_of_lt hlt hlt'
  exact hh.trans he

/-- Construct the complete finite update and both ordinary word equalities. -/
theorem exists_finite_normalized_increment (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (hm : ∀ j, marker j ≤ 1) (s : ℕ) (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N)
    (carry0 digits0 : ZMod (N*2011) → ℕ)
    (hf0 : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (fun _ => 0) marker) (displacement s) carry0 digits0) :
    ∃ carry digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a (enabled S) marker) (displacement s) carry digits ∧
      NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (enabled S) marker) =
        NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (fun _ => 0) marker)+
          totalIncrement S ∧
      NativeCyclicConvolution.word radix digits = NativeCyclicConvolution.word radix digits0+
        (CurrentKernel2011.K+2^(displacement s))*totalIncrement S := by
  obtain ⟨carry,digits,hf,he⟩ := exists_normalization_sum a marker hm s S hsafe carry0 digits0 hf0
  exact ⟨carry,digits,hf,source_enabled_sum a marker S,he⟩

/-- Exact rank change for any two actual endpoint normalizations, retaining
the original source-mask port and the complete sum of physical place values. -/
theorem finite_rank_decrement (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (hm : ∀ j, marker j ≤ 1) (s : ℕ) (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N)
    (carry0 digits0 carry digits : ZMod (N*2011) → ℕ)
    (hf0 : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (fun _ => 0) marker) (displacement s) carry0 digits0)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (enabled S) marker) (displacement s) carry digits)
    (MC MF J : ℤ) :
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (enabled S) marker))
      (NativeCyclicConvolution.word radix digits) MC MF J =
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a (fun _ => 0) marker))
      (NativeCyclicConvolution.word radix digits0) MC MF J-
        rankGamma (R := ℤ) (radix^(N*2011) : ℕ) (CurrentKernel2011.K+2^(displacement s) : ℕ)
          (radix^977 : ℕ)*(powerSum S : ℤ) := by
  rw [source_enabled_sum,finite_normalized_increment a marker hm s S hsafe
    carry0 digits0 carry digits hf0 hf]
  simp only [totalIncrement,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  rw [rank_variation]
  unfold rankGamma
  ring

end DiophantineConsistency.CurrentFiniteDummyMutation2011
