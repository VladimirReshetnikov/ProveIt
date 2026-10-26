import DiophantineConsistency.CurrentWordHighMask2011
import DiophantineConsistency.NativeRankVariation

/-!
# Exact one-dummy mutation and conditional ordinary transport increment

The source update changes exactly one physical digit. The normalized-word
increment requires an explicit ordinary nonwrapping bound; transport
congruences alone are not treated as ordinary equalities. No safe-position
or full controller claim is made here.
-/

namespace DiophantineConsistency.CurrentDummyMutation2011

open CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentWordHighMask2011 NativeCyclicConvolution NativeRankVariation
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

section Generic

/-- A point increment in any finite cyclic digit word has its exact
ordinary place value, independent of digit bounds or carries. -/
theorem word_update_increment {n : ℕ} [NeZero n] (ρ : ℕ)
    (c : ZMod n → ℕ) (i : ZMod n) :
    NativeCyclicConvolution.word ρ (Function.update c i (c i+1)) =
      NativeCyclicConvolution.word ρ c+ρ^i.val := by
  have he : Function.update c i (c i+1) =
      fun k => c k+(if k = i then 1 else 0) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Function.update_self,ite_true]
    · rw [Function.update_of_ne hk,if_neg hk,add_zero]
  rw [he,word_add]
  congr 1
  simp only [NativeCyclicConvolution.word,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Ordinary equality follows from both transports only after the new
representative and the proposed ordinary sum are strictly below the modulus. -/
theorem transport_increment {A C C' F F' modulus δ : ℕ}
    (hC : C' = C+δ) (hF : A*C ≡ F [MOD modulus])
    (hF' : A*C' ≡ F' [MOD modulus]) (hlt : F' < modulus)
    (hnowrap : F+A*δ < modulus) : F' = F+A*δ := by
  have he : A*C' ≡ F+A*δ [MOD modulus] := by
    rw [hC,Nat.mul_add]
    exact hF.add_right _
  exact (hF'.symm.trans he).eq_of_lt_of_lt hlt hnowrap

end Generic

variable {N : ℕ} [NeZero N]

/-- The actual positional increment, with the canonical cell representative. -/
def dummyIncrement (j : ZMod N) : ℕ := radix^977*(radix^2011)^j.val

omit [NeZero N] in
theorem dummyIncrement_pos (j : ZMod N) : 0 < dummyIncrement j := by
  unfold dummyIncrement
  have hr : 0 < radix := by decide
  exact Nat.mul_pos (pow_pos hr _) (pow_pos (pow_pos hr _) _)

theorem dummy_place_value (j : ZMod N) :
    radix^(base j+(977 : ZMod (N*2011))).val = dummyIncrement j := by
  have hv := base_add_val j 977 (by decide)
  simp only [Nat.cast_ofNat] at hv
  rw [hv]
  unfold dummyIncrement
  rw [Nat.mul_comm j.val 2011,pow_add,pow_mul]
  exact Nat.mul_comm _ _

/-- Updating a control cell changes exactly its own literal physical slot.
Numeric controls and a one-cell cyclic modulus are allowed. -/
theorem word_update_dummy (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    CurrentWordConstruction2011.word a (Function.update dummy j 1) marker =
      Function.update (CurrentWordConstruction2011.word a dummy marker) (base j+977) 1 := by
  funext i
  by_cases hi : i = base j+977
  · subst i
    rw [word_dummy,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases he : i.val%2011 = 977
    · have hj : ((i.val/2011 : ℕ) : ZMod N) ≠ j := by
        intro hh
        apply hi
        have hr := cell_representation i
        rw [hh,he] at hr
        exact hr.symm
      simp only [CurrentWordConstruction2011.word,he,ite_true,Function.update_of_ne hj]
    · simp only [CurrentWordConstruction2011.word,if_neg he]

theorem word_update_unchanged (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (i : ZMod (N*2011)) (hi : i ≠ base j+977) :
    CurrentWordConstruction2011.word a (Function.update dummy j 1) marker i =
      CurrentWordConstruction2011.word a dummy marker i := by
  rw [word_update_dummy,Function.update_of_ne hi]

omit [NeZero N] in
theorem update_boolean (dummy : ZMod N → ℕ) (hd : ∀ i, dummy i ≤ 1)
    (j i : ZMod N) : Function.update dummy j 1 i ≤ 1 := by
  by_cases hi : i = j
  · subst i
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    exact hd i

/-- The exact packed source increment requires only that the selected
dummy was zero. Other controls may be arbitrary natural numbers. -/
theorem source_increment (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (hj : dummy j = 0) :
    NativeCyclicConvolution.word radix
      (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker) =
    NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker)+
      dummyIncrement j := by
  rw [word_update_dummy]
  have hz : CurrentWordConstruction2011.word a dummy marker (base j+977)+1 = 1 := by
    rw [word_dummy,hj,zero_add]
  rw [← hz,word_update_increment,dummy_place_value]

/-- Both normalized words are bound by their actual transport facts.
Only the proposed new ordinary sum's nonwrapping bound remains an input. -/
theorem normalized_increment (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0)
    (carry digits carry' digits' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)
    (hf' : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
        (displacement s) carry' digits')
    (hnowrap : NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)-1) :
    NativeCyclicConvolution.word radix digits' = NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j := by
  have hlt := (normalized_word_strict a (Function.update dummy j 1) marker
    (update_boolean dummy hd j) hm s carry' digits' hf').2
  exact transport_increment (source_increment a dummy marker j hj)
    hf.transport hf'.transport hlt hnowrap

/-- The updated carry solution can be constructed. The nonwrapping
condition concerns the original normalized word and the ordinary increment. -/
theorem exists_normalized_increment (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0)
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)
    (hnowrap : NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)-1) :
    ∃ carry' digits' : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
          (displacement s) carry' digits' ∧
      NativeCyclicConvolution.word radix digits' = NativeCyclicConvolution.word radix digits+
        (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j := by
  obtain ⟨carry',digits',hf'⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a (Function.update dummy j 1) marker (update_boolean dummy hd j) hm (displacement s)
  exact ⟨carry',digits',hf',normalized_increment a dummy marker hd hm s j hj
    carry digits carry' digits' hf hf' hnowrap⟩

/-- The rank consequence is applied only after proving the ordinary F
increment. The source high-mask port is retained without an extra shift. -/
theorem rank_decrement (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0)
    (carry digits carry' digits' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)
    (hf' : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
        (displacement s) carry' digits')
    (hnowrap : NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)-1)
    (MC MF J : ℤ) :
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix
        (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker))
      (NativeCyclicConvolution.word radix digits') MC MF J =
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker))
      (NativeCyclicConvolution.word radix digits) MC MF J-
        rankGamma (R := ℤ) (radix^(N*2011) : ℕ) (CurrentKernel2011.K+2^(displacement s) : ℕ)
          (radix^977 : ℕ)*(radix^2011 : ℤ)^j.val := by
  rw [source_increment a dummy marker j hj,
    normalized_increment a dummy marker hd hm s j hj carry digits carry' digits' hf hf' hnowrap]
  simp only [dummyIncrement,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  exact rank_power_variation _ _ _ _ _ _ _ _ _ _

end DiophantineConsistency.CurrentDummyMutation2011
