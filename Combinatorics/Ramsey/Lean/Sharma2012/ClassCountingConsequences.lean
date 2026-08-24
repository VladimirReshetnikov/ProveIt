import Sharma2012.CorollaryConsequences
import Sharma2012.UpperConsequences

/-!
# Finite class counting for Sharma's upper bound

This module encodes Theta words as finite permutations, splits them by the
parity of their first entry, and injects the odd-first words into normalized
odd/even interleaving classes.
-/
set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.Sharma2012

local instance classCountingDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev Theta12Finite (n : Nat) :=
  {sigma : Equiv.Perm (Fin n) // IsTheta12 n (permutationWord sigma)}

abbrev Theta21Finite (n : Nat) :=
  {sigma : Equiv.Perm (Fin n) // IsTheta21 n (permutationWord sigma)}

lemma permutationWord_toFinset {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    (permutationWord sigma).toFinset = segment n := by
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset, segment, Finset.mem_Icc]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hx
    have hi' := hi
    simp [permutationWord] at hi'
    omega
  · intro hx
    let y : Fin n := ⟨x - 1, by omega⟩
    obtain ⟨i, hi⟩ := sigma.surjective y
    apply List.mem_iff_getElem.mpr
    refine ⟨i, ?_⟩
    simp [permutationWord, y, hi]
    omega

lemma isTheta_permutationWord_iff {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    IsTheta n (permutationWord sigma) ↔ IsThetaPermutation sigma := by
  constructor
  · exact fun h => h.2
  · intro h
    have hnodup : (permutationWord sigma).Nodup := by
      apply List.nodup_ofFn_ofInjective
      intro i j hij
      apply sigma.injective
      exact Fin.ext (Nat.add_right_cancel hij)
    exact ⟨⟨hnodup, permutationWord_toFinset sigma⟩, h⟩

def reversePermutation {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  Fin.revPerm.trans sigma

lemma permutationWord_reversePermutation {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    permutationWord (reversePermutation sigma) =
      reversal (permutationWord sigma) := by
  apply List.ext_getElem
  · simp [permutationWord, reversal]
  · intro i hi hri
    simp only [permutationWord, List.length_ofFn] at hi
    simp only [permutationWord, reversal, List.length_reverse, List.length_ofFn] at hri
    simp [permutationWord, reversePermutation, reversal,
      List.getElem_reverse]
    apply congr_arg Fin.val
    apply congr_arg sigma
    apply Fin.ext
    simp
    omega

def complementPermutation {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  sigma.trans Fin.revPerm

lemma permutationWord_complementPermutation {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    permutationWord (complementPermutation sigma) =
      complement n (permutationWord sigma) := by
  apply List.ext_getElem
  · simp [permutationWord, complement]
  · intro i hi hci
    simp only [permutationWord, List.length_ofFn] at hi
    simp only [permutationWord, complement, List.length_map, List.length_ofFn] at hci
    simp [permutationWord, complementPermutation, complement]
    omega

lemma reversePermutation_involutive {n : Nat} :
    Function.Involutive (@reversePermutation n) := by
  intro sigma
  apply permutationWord_injective
  simp only [permutationWord_reversePermutation, reversal]
  simp

lemma complementPermutation_involutive {n : Nat} :
    Function.Involutive (@complementPermutation n) := by
  intro sigma
  apply Equiv.ext
  intro i
  simp [complementPermutation]

def thetaWordEquiv (n : Nat) :
    ThetaPermutation n ≃ {sigma : Equiv.Perm (Fin n) // IsTheta n (permutationWord sigma)} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun sigma =>
    (isTheta_permutationWord_iff sigma).symm

lemma card_thetaWords (n : Nat) :
    Fintype.card {sigma : Equiv.Perm (Fin n) // IsTheta n (permutationWord sigma)} =
      theta n := by
  rw [← Fintype.card_congr (thetaWordEquiv n)]
  rfl

lemma isTheta21_reversal_of_isTheta12 {n : Nat} {word : List Nat}
    (hn : 2 ≤ n) (hword : IsTheta12 n word) :
    IsTheta21 n (reversal word) := by
  rcases hword.2 with ⟨first, hfirst, hfirstOdd⟩
  obtain ⟨first', last, hfirst', hlast, hfirstLast⟩ :=
    proposition_2_1_holds n word hn hword.1
  have hfirstEq : first' = first := by
    unfold StartsWith at hfirst hfirst'
    exact Option.some.inj (hfirst'.symm.trans hfirst)
  subst first'
  have hlastEven : Even last := by
    rcases Nat.even_or_odd last with hlastEven | hlastOdd
    · exact hlastEven
    · exact False.elim (hfirstLast (by
        rcases hfirstOdd with ⟨a, ha⟩
        rcases hlastOdd with ⟨b, hb⟩
        unfold Nat.ModEq
        omega))
  exact ⟨isTheta_reversal hword.1,
    ⟨last, startsWith_reversal_of_endsWith hlast, hlastEven⟩⟩

def theta21Theta12Equiv (n : Nat) (hn : 2 ≤ n) :
    Theta21Finite n ≃ Theta12Finite n where
  toFun sigma :=
    ⟨reversePermutation sigma.1, by
      rw [permutationWord_reversePermutation]
      exact isTheta12_reversal_of_isTheta21 hn sigma.2⟩
  invFun sigma :=
    ⟨reversePermutation sigma.1, by
      rw [permutationWord_reversePermutation]
      exact isTheta21_reversal_of_isTheta12 hn sigma.2⟩
  left_inv sigma := by
    apply Subtype.ext
    exact reversePermutation_involutive sigma.1
  right_inv sigma := by
    apply Subtype.ext
    exact reversePermutation_involutive sigma.1

lemma startsOdd_or_startsEven_of_isTheta {n : Nat} {word : List Nat}
    (hn : 1 ≤ n) (hword : IsTheta n word) :
    StartsOdd word ∨ StartsEven word := by
  cases word with
  | nil =>
      have := isTheta_length hword
      simp at this
      omega
  | cons first tail =>
      rcases Nat.even_or_odd first with hfirst | hfirst
      · exact Or.inr ⟨first, by simp [StartsWith], hfirst⟩
      · exact Or.inl ⟨first, by simp [StartsWith], hfirst⟩

noncomputable def thetaSplit {n : Nat} (hn : 1 ≤ n) :
    ThetaPermutation n → Theta12Finite n ⊕ Theta21Finite n :=
  fun sigma =>
    let htheta : IsTheta n (permutationWord sigma.1) :=
      (isTheta_permutationWord_iff sigma.1).2 sigma.2
    if hodd : StartsOdd (permutationWord sigma.1) then
      Sum.inl ⟨sigma.1, htheta, hodd⟩
    else
      Sum.inr ⟨sigma.1, htheta,
        (startsOdd_or_startsEven_of_isTheta hn htheta).resolve_left hodd⟩

lemma thetaSplit_injective {n : Nat} (hn : 1 ≤ n) :
    Function.Injective (thetaSplit hn) := by
  intro sigma tau h
  apply Subtype.ext
  have hproj (rho : ThetaPermutation n) :
      Sum.elim Subtype.val Subtype.val (thetaSplit hn rho) = rho.1 := by
    simp only [thetaSplit]
    split <;> rfl
  have hraw := congr_arg (Sum.elim Subtype.val Subtype.val) h
  simpa only [hproj] using hraw

lemma theta_card_le_twice_theta12 {n : Nat} (hn : 2 ≤ n) :
    theta n ≤ 2 * Fintype.card (Theta12Finite n) := by
  have hcard := Fintype.card_le_of_injective (thetaSplit (by omega))
    (thetaSplit_injective (by omega : 1 ≤ n))
  have heq : Fintype.card (Theta21Finite n) =
      Fintype.card (Theta12Finite n) :=
    Fintype.card_congr (theta21Theta12Equiv n hn)
  change Fintype.card (ThetaPermutation n) ≤ _
  simpa [heq, Nat.two_mul] using hcard

def thetaComplementEquiv (n : Nat) :
    ThetaPermutation n ≃ ThetaPermutation n where
  toFun sigma :=
    ⟨complementPermutation sigma.1, by
      apply (isTheta_permutationWord_iff _).1
      rw [permutationWord_complementPermutation]
      exact isTheta_complement
        ((isTheta_permutationWord_iff sigma.1).2 sigma.2)⟩
  invFun sigma :=
    ⟨complementPermutation sigma.1, by
      apply (isTheta_permutationWord_iff _).1
      rw [permutationWord_complementPermutation]
      exact isTheta_complement
        ((isTheta_permutationWord_iff sigma.1).2 sigma.2)⟩
  left_inv sigma := by
    apply Subtype.ext
    exact complementPermutation_involutive sigma.1
  right_inv sigma := by
    apply Subtype.ext
    exact complementPermutation_involutive sigma.1

noncomputable def permutationOfTheta {n : Nat} (word : List Nat)
    (hword : IsTheta n word) : Equiv.Perm (Fin n) :=
  Classical.choose (exists_permutationWord_eq_of_isTheta hword)

lemma permutationWord_permutationOfTheta {n : Nat} (word : List Nat)
    (hword : IsTheta n word) :
    permutationWord (permutationOfTheta word hword) = word :=
  Classical.choose_spec (exists_permutationWord_eq_of_isTheta hword)

noncomputable def oddTraceIndex {n : Nat} (sigma : Theta12Finite n) :
    ThetaPermutation ((n + 1) / 2) := by
  let hbase : IsTheta ((n + 1) / 2) (oddBase (permutationWord sigma.1)) :=
    isTheta_oddBase sigma.2.1
  let pi := permutationOfTheta (oddBase (permutationWord sigma.1)) hbase
  exact ⟨pi, (isTheta_permutationWord_iff pi).1 (by
    rw [permutationWord_permutationOfTheta]
    exact hbase)⟩

noncomputable def evenTraceIndex {n : Nat} (sigma : Theta12Finite n) :
    ThetaPermutation (n / 2) := by
  let hbase : IsTheta (n / 2) (evenBase (permutationWord sigma.1)) :=
    isTheta_evenBase sigma.2.1
  let pi := permutationOfTheta (evenBase (permutationWord sigma.1)) hbase
  exact ⟨pi, (isTheta_permutationWord_iff pi).1 (by
    rw [permutationWord_permutationOfTheta]
    exact hbase)⟩

lemma permutationWord_oddTraceIndex {n : Nat} (sigma : Theta12Finite n) :
    permutationWord (oddTraceIndex sigma).1 =
      oddBase (permutationWord sigma.1) := by
  simp only [oddTraceIndex]
  apply permutationWord_permutationOfTheta

lemma permutationWord_evenTraceIndex {n : Nat} (sigma : Theta12Finite n) :
    permutationWord (evenTraceIndex sigma).1 =
      evenBase (permutationWord sigma.1) := by
  simp only [evenTraceIndex]
  apply permutationWord_permutationOfTheta

noncomputable def normalizedInterleavingClass (n : Nat)
    (oddIndex : ThetaPermutation ((n + 1) / 2))
    (evenIndex : ThetaPermutation (n / 2)) : Finset (Equiv.Perm (Fin n)) :=
  interleavingClass n
    (oddLift (permutationWord oddIndex.1))
    (evenLift (permutationWord evenIndex.1))

noncomputable def theta12Encoding (n : Nat) :
    Theta12Finite n →
      Σ oddIndex : ThetaPermutation ((n + 1) / 2),
        Σ evenIndex : ThetaPermutation (n / 2),
          {sigma : Equiv.Perm (Fin n) //
            sigma ∈ normalizedInterleavingClass n oddIndex evenIndex} :=
  fun sigma =>
    ⟨oddTraceIndex sigma, evenTraceIndex sigma,
      ⟨sigma.1, by
        simp only [normalizedInterleavingClass, interleavingClass,
          Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨sigma.2, ?_, ?_⟩
        · rw [permutationWord_oddTraceIndex, oddLift_oddBase]
        · rw [permutationWord_evenTraceIndex, evenLift_evenBase]⟩⟩

lemma theta12Encoding_injective (n : Nat) :
    Function.Injective (theta12Encoding n) := by
  intro sigma tau h
  apply Subtype.ext
  have hraw := congr_arg (fun encoded => encoded.2.2.1) h
  simpa only [theta12Encoding] using hraw

lemma theta12_card_le_sum_interleavingClasses (n : Nat) :
    Fintype.card (Theta12Finite n) ≤
      ∑ oddIndex : ThetaPermutation ((n + 1) / 2),
        ∑ evenIndex : ThetaPermutation (n / 2),
          (normalizedInterleavingClass n oddIndex evenIndex).card := by
  have hcard := Fintype.card_le_of_injective (theta12Encoding n)
    (theta12Encoding_injective n)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using hcard


end LeanProofs.Sharma2012
