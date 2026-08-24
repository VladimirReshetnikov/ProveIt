import Sharma2012.Statements
import RamseyPaperCommon.FiniteBridges

/-!
# Certified enumeration of three-progression-free permutations

The three papers share the same finite counting sequence.  This file gives a
small decidable characterization of three-term avoidance and will provide the
single executable counter used to certify the finite tables in all three
catalogues.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.RamseyPaperCommon

open LeanProofs.Sharma2012

/-- No entry at an intermediate position is the arithmetic mean of entries at
two surrounding positions.  For a word without repeated entries, this is
exactly avoidance of increasing and decreasing three-term APs. -/
def MidpointFree (word : List Nat) : Prop :=
  forall i j k : Fin word.length, (i : Nat) < j -> (j : Nat) < k ->
    word.get i + word.get k ≠ 2 * word.get j

/-- The function-valued version of `MidpointFree`. -/
def SequenceMidpointFree {n : Nat} (sequence : Fin n -> Nat) : Prop :=
  forall i j k : Fin n, (i : Nat) < j -> (j : Nat) < k ->
    sequence i + sequence k ≠ 2 * sequence j

@[simp] theorem midpointFree_ofFn {n : Nat} (sequence : Fin n -> Nat) :
    MidpointFree (List.ofFn sequence) <-> SequenceMidpointFree sequence := by
  let hlen : (List.ofFn sequence).length = n := List.length_ofFn
  constructor
  · intro h i j k hij hjk
    let i' := Fin.cast hlen.symm i
    let j' := Fin.cast hlen.symm j
    let k' := Fin.cast hlen.symm k
    have hi : (List.ofFn sequence).get i' = sequence i := by
      rw [List.get_ofFn]
      congr 1
    have hj : (List.ofFn sequence).get j' = sequence j := by
      rw [List.get_ofFn]
      congr 1
    have hk : (List.ofFn sequence).get k' = sequence k := by
      rw [List.get_ofFn]
      congr 1
    simpa only [hi, hj, hk] using h i' j' k' hij hjk
  · intro h i j k hij hjk
    let i' := Fin.cast hlen i
    let j' := Fin.cast hlen j
    let k' := Fin.cast hlen k
    have hi : (List.ofFn sequence).get i = sequence i' := by
      rw [List.get_ofFn]
    have hj : (List.ofFn sequence).get j = sequence j' := by
      rw [List.get_ofFn]
    have hk : (List.ofFn sequence).get k = sequence k' := by
      rw [List.get_ofFn]
    simpa only [hi, hj, hk] using h i' j' k' hij hjk

/-- A fully computational decision procedure for `MidpointFree`. -/
def midpointFreeDecidable (word : List Nat) : Decidable (MidpointFree word) := by
  unfold MidpointFree
  exact Fintype.decidableForallFintype

/-- Boolean form of `MidpointFree`, used by the reflected enumerator. -/
def midpointFreeCheck (word : List Nat) : Bool :=
  @decide (MidpointFree word) (midpointFreeDecidable word)

@[simp] theorem midpointFreeCheck_eq_true (word : List Nat) :
    midpointFreeCheck word = true <-> MidpointFree word := by
  simp only [midpointFreeCheck, decide_eq_true_eq]

private lemma containsThreeAP_of_increasing_positions {word : List Nat}
    {i₀ i₁ i₂ a d : Nat} (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hd : 0 < d)
    (h₀ : word[i₀]? = some a) (h₁ : word[i₁]? = some (a + d))
    (h₂ : word[i₂]? = some (a + 2 * d)) : ContainsThreeAP word := by
  let indices : Fin 3 -> Nat := ![i₀, i₁, i₂]
  refine ⟨indices, ?_, a, d, hd, Or.inl ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [indices, hi₀₁, hi₁₂]
  · intro i
    fin_cases i <;> simp [indices, h₀, h₁, h₂, Nat.mul_comm]

private lemma containsThreeAP_of_decreasing_positions {word : List Nat}
    {i₀ i₁ i₂ a d : Nat} (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hd : 0 < d)
    (h₀ : word[i₀]? = some (a + 2 * d)) (h₁ : word[i₁]? = some (a + d))
    (h₂ : word[i₂]? = some a) : ContainsThreeAP word := by
  let indices : Fin 3 -> Nat := ![i₀, i₁, i₂]
  refine ⟨indices, ?_, a, d, hd, Or.inr ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [indices, hi₀₁, hi₁₂]
  · intro i
    fin_cases i <;> simp [indices, h₀, h₁, h₂, Nat.mul_comm]

/-- On a word with distinct entries, the midpoint test is equivalent to the
paper's increasing-or-decreasing definition of three-term avoidance. -/
theorem threeFree_iff_midpointFree {word : List Nat} (hnodup : word.Nodup) :
    ThreeFree word <-> MidpointFree word := by
  constructor
  · intro hfree i j k hij hjk
    let x0 := word.get i
    let x1 := word.get j
    let x2 := word.get k
    have h02 : x0 ≠ x2 := by
      intro h
      have hik : i = k := hnodup.get_inj_iff.mp h
      omega
    have hi : word[(i : Nat)]? = some x0 := by
      simpa only [x0, List.get_eq_getElem] using List.getElem?_eq_getElem i.isLt
    have hj : word[(j : Nat)]? = some x1 := by
      simpa only [x1, List.get_eq_getElem] using List.getElem?_eq_getElem j.isLt
    have hk : word[(k : Nat)]? = some x2 := by
      simpa only [x2, List.get_eq_getElem] using List.getElem?_eq_getElem k.isLt
    intro hmidpoint
    apply hfree
    rcases lt_or_gt_of_ne h02 with h02lt | h20lt
    · let d := x1 - x0
      have hd : 0 < d := by
        dsimp only [x0, x1, x2, d] at *
        omega
      have hx1 : x1 = x0 + d := by
        dsimp only [d]
        omega
      have hx2 : x2 = x0 + 2 * d := by
        dsimp only [d]
        omega
      apply containsThreeAP_of_increasing_positions hij hjk hd hi
      · simpa only [hx1] using hj
      · simpa only [hx2] using hk
    · let d := x1 - x2
      have hd : 0 < d := by
        dsimp only [x0, x1, x2, d] at *
        omega
      have hx1 : x1 = x2 + d := by
        dsimp only [d]
        omega
      have hx0 : x0 = x2 + 2 * d := by
        dsimp only [d]
        omega
      apply containsThreeAP_of_decreasing_positions (a := x2) hij hjk hd
      · simpa only [hx0] using hi
      · simpa only [hx1] using hj
      · exact hk
  · intro hmidpoint hap
    rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
    · have h0 := hvalues (0 : Fin 3)
      have h1 := hvalues (1 : Fin 3)
      have h2 := hvalues (2 : Fin 3)
      simp only [Fin.val_zero, zero_mul, add_zero] at h0
      norm_num at h1 h2
      obtain ⟨hi0, hv0⟩ := List.getElem?_eq_some_iff.mp h0
      obtain ⟨hi1, hv1⟩ := List.getElem?_eq_some_iff.mp h1
      obtain ⟨hi2, hv2⟩ := List.getElem?_eq_some_iff.mp h2
      have h01 : indices 0 < indices 1 := hindices (by decide)
      have h12 : indices 1 < indices 2 := hindices (by decide)
      exact (hmidpoint ⟨indices 0, hi0⟩ ⟨indices 1, hi1⟩
        ⟨indices 2, hi2⟩ h01 h12) (by simp only [List.get_eq_getElem, hv0, hv1, hv2]; omega)
    · have h0 := hvalues (0 : Fin 3)
      have h1 := hvalues (1 : Fin 3)
      have h2 := hvalues (2 : Fin 3)
      norm_num at h0 h1 h2
      obtain ⟨hi0, hv0⟩ := List.getElem?_eq_some_iff.mp h0
      obtain ⟨hi1, hv1⟩ := List.getElem?_eq_some_iff.mp h1
      obtain ⟨hi2, hv2⟩ := List.getElem?_eq_some_iff.mp h2
      have h01 : indices 0 < indices 1 := hindices (by decide)
      have h12 : indices 1 < indices 2 := hindices (by decide)
      exact (hmidpoint ⟨indices 0, hi0⟩ ⟨indices 1, hi1⟩
        ⟨indices 2, hi2⟩ h01 h12) (by simp only [List.get_eq_getElem, hv0, hv1, hv2]; omega)

/-- A three-term integer-signed progression is equivalently a nondegenerate
midpoint equation. -/
theorem isArithmeticProgression_three_iff (x : Fin 3 -> Nat) :
    LeanProofs.LeSaulnierVijay2011.IsArithmeticProgression x <->
      x 0 + x 2 = 2 * x 1 /\ x 0 ≠ x 2 := by
  constructor
  · rintro ⟨a, d, hd, _, hvalues⟩
    have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    constructor
    · exact_mod_cast (by omega : (x 0 : Int) + x 2 = 2 * x 1)
    · intro h02
      have : (d : Int) = 0 := by
        rw [h02] at h0
        omega
      exact (bne_iff_ne.mp hd) this
  · rintro ⟨hmidpoint, h02⟩
    refine ⟨(x 0 : Int), (x 1 : Int) - (x 0 : Int), ?_, trivial, ?_⟩
    · apply bne_iff_ne.mpr
      intro hd
      have hx01 : x 0 = x 1 := by omega
      have hx12 : x 1 = x 2 := by omega
      exact h02 (hx01.trans hx12)
    · intro i
      fin_cases i
      · norm_num
      · norm_num
      · norm_num
        change (x 2 : Int) = (x 0 : Int) +
          2 * ((x 1 : Int) - (x 0 : Int))
        have hm : (x 0 : Int) + x 2 = 2 * x 1 := by exact_mod_cast hmidpoint
        omega

/-- The displayed word of a finite permutation has no duplicate entries. -/
theorem permutationWord_nodup {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    (permutationWord sigma).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply sigma.injective
  exact Fin.ext (Nat.add_right_cancel hij)

/-- LeSaulnier--Vijay finite avoidance is exactly the decidable midpoint
condition on the common displayed word. -/
theorem finiteAvoiding_iff_midpointFree {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding 3 sigma <->
      MidpointFree (permutationWord sigma) := by
  rw [LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding]
  rw [show permutationWord sigma = List.ofFn
    (LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma) by rfl]
  rw [midpointFree_ofFn]
  unfold SequenceMidpointFree
  constructor
  · intro hfree i j k hij hjk hmidpoint
    apply hfree
    let indices : Fin 3 -> Fin n := ![i, j, k]
    refine ⟨indices, ?_, (isArithmeticProgression_three_iff
      (fun t => LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma
        (indices t))).mpr ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro t
      fin_cases t
      · exact hij
      · exact hjk
    · constructor
      · simpa [indices, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two] using hmidpoint
      · intro h02
        have hval : (sigma i : Nat) = sigma k := Nat.add_right_cancel h02
        have hik : i = k := sigma.injective (Fin.ext hval)
        omega
  · intro hmidpoint hap
    rcases hap with ⟨indices, hindices, hprogression⟩
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    obtain ⟨hmiddle, _⟩ :=
      (isArithmeticProgression_three_iff
        (fun t => LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma
          (indices t))).mp hprogression
    exact (hmidpoint (indices 0) (indices 1) (indices 2) h01 h12)
      hmiddle

/-- The Sharma and LeSaulnier--Vijay finite predicates coincide. -/
theorem isThetaPermutation_iff_finiteAvoiding {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    IsThetaPermutation sigma <->
      LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding 3 sigma := by
  rw [IsThetaPermutation,
    threeFree_iff_midpointFree (permutationWord_nodup sigma),
    finiteAvoiding_iff_midpointFree]

/-! ## A reflected finite counter -/

/-- Native implementation of the backtracking counter.  A state records the
entries already used and the entries forbidden as the third member of an AP.
Memo tables are scoped to the first three entries, keeping the verification of
the largest table values within a predictable memory bound.  Complementing
every value proves that only half of the possible first entries need be
searched. -/
unsafe def fastReflectedM (n : Nat) : Nat := unsafeBaseIO do
  if n = 0 then
    return 1
  if n = 1 then
    return 1
  if n = 2 then
    return 2
  let full := (1 <<< n) - 1
  let cache : IO.Ref (Std.HashMap Nat Nat) ← IO.mkRef {}
  let rec visit (used forbidden : Nat) : BaseIO Nat := do
    if used = full then
      return 1
    let key := (used <<< n) ||| forbidden
    if let some answer := (← cache.get).get? key then
      return answer
    let mut total := 0
    for x in [0:n] do
      if !used.testBit x && !forbidden.testBit x then
        let mut nextForbidden := forbidden
        for a in [0:n] do
          if used.testBit a then
            if a ≤ 2 * x then
              let z := 2 * x - a
              if z < n then
                nextForbidden := nextForbidden ||| (1 <<< z)
        total := total + (← visit (used ||| (1 <<< x)) nextForbidden)
    cache.modify fun table => table.insert key total
    return total
  let mut grandTotal := 0
  for first in [0:(n + 1) / 2] do
    let mut branchTotal := 0
    for second in [0:n] do
      if second ≠ first then
        let mut initialForbidden := 0
        if first ≤ 2 * second then
          let z := 2 * second - first
          if z < n then
            initialForbidden := 1 <<< z
        let usedTwo := (1 <<< first) ||| (1 <<< second)
        for third in [0:n] do
          if !usedTwo.testBit third && !initialForbidden.testBit third then
            cache.set {}
            let mut nextForbidden := initialForbidden
            for a in [0:n] do
              if usedTwo.testBit a then
                if a ≤ 2 * third then
                  let z := 2 * third - a
                  if z < n then
                    nextForbidden := nextForbidden ||| (1 <<< z)
            branchTotal := branchTotal +
              (← visit (usedTwo ||| (1 <<< third)) nextForbidden)
    if 2 * first + 1 = n then
      grandTotal := grandTotal + branchTotal
    else
      grandTotal := grandTotal + 2 * branchTotal
  return grandTotal

/-- Direct finite enumeration using the executable midpoint test.  A faster
extension-equivalent implementation is installed below; this simple version
is the logical specification used by all proofs. -/
@[implemented_by fastReflectedM]
def reflectedM (n : Nat) : Nat :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun sigma =>
    midpointFreeCheck (permutationWord sigma) = true).card

/-- The reflected predicate subtype and the LeSaulnier--Vijay avoiding subtype
are canonically equivalent. -/
def reflectedAvoiderEquiv (n : Nat) :
    {sigma : Equiv.Perm (Fin n) //
      midpointFreeCheck (permutationWord sigma) = true} ≃
      {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding 3 sigma} where
  toFun sigma := ⟨sigma.1, (finiteAvoiding_iff_midpointFree sigma.1).mpr
    ((midpointFreeCheck_eq_true _).mp sigma.2)⟩
  invFun sigma := ⟨sigma.1, (midpointFreeCheck_eq_true _).mpr
    ((finiteAvoiding_iff_midpointFree sigma.1).mp sigma.2)⟩
  left_inv sigma := by cases sigma; rfl
  right_inv sigma := by cases sigma; rfl

/-- Correctness of the reflected counter with respect to the paper's `M`. -/
theorem reflectedM_eq_M (n : Nat) :
    reflectedM n = LeanProofs.LeSaulnierVijay2011.M n := by
  classical
  unfold reflectedM LeanProofs.LeSaulnierVijay2011.M
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (reflectedAvoiderEquiv n)

/-- Sharma's `theta` and LeSaulnier--Vijay's `M` are the same sequence. -/
theorem sharma_theta_eq_M (n : Nat) :
    theta n = LeanProofs.LeSaulnierVijay2011.M n := by
  classical
  unfold theta LeanProofs.LeSaulnierVijay2011.M
  apply Fintype.card_congr
  exact
    { toFun := fun sigma =>
        ⟨sigma.1, (isThetaPermutation_iff_finiteAvoiding sigma.1).mp sigma.2⟩
      invFun := fun sigma =>
        ⟨sigma.1, (isThetaPermutation_iff_finiteAvoiding sigma.1).mpr sigma.2⟩
      left_inv := fun sigma => by cases sigma; rfl
      right_inv := fun sigma => by cases sigma; rfl }

/-- Davis's `M` is also computed by the same reflected counter. -/
theorem reflectedM_eq_davis_M (n : Nat) :
    reflectedM n = LeanProofs.DavisEntringerGrahamSimmons1977.M n := by
  rw [reflectedM_eq_M, davis_M_eq_lesaulnier_M]

end LeanProofs.RamseyPaperCommon
