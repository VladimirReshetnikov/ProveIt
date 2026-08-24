import Sharma2012.Statements

/-!
# Proofs for Sharma (2009)

This file proves the formalized results in source order.  The propositions
`introduction_ratio_question` and `open_problem_1`--`open_problem_3` record
questions left open in the paper, so they deliberately have no proof
declarations here.

The numbered inequalities (1) and (2), all numbered theorems, lemmas,
propositions, and corollaries are proved results in the source.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.Sharma2012

local instance classicalDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Elementary facts about permutation words -/

/-- Entrywise doubling, used for the even trace in the paper's recursive
constructions. -/
def evenLift (word : List Nat) : List Nat :=
  word.map fun x => 2 * x

/-- Entrywise `x ↦ 2x - 1`, used for the odd trace in the paper's recursive
constructions. -/
def oddLift (word : List Nat) : List Nat :=
  word.map fun x => 2 * x - 1

lemma isTheta_nodup {n : Nat} {word : List Nat} (h : IsTheta n word) :
    word.Nodup :=
  h.1.1

lemma isTheta_toFinset {n : Nat} {word : List Nat} (h : IsTheta n word) :
    word.toFinset = segment n :=
  h.1.2

lemma isTheta_threeFree {n : Nat} {word : List Nat} (h : IsTheta n word) :
    ThreeFree word :=
  h.2

lemma isTheta_length {n : Nat} {word : List Nat} (h : IsTheta n word) :
    word.length = n := by
  calc
    word.length = word.toFinset.card := (List.toFinset_card_of_nodup h.1.1).symm
    _ = (segment n).card := by rw [h.1.2]
    _ = n := by simp [segment]

lemma mem_of_mem_segment_of_isTheta {n x : Nat} {word : List Nat}
    (hword : IsTheta n word) (hx : x ∈ segment n) : x ∈ word := by
  rw [← List.mem_toFinset, hword.1.2]
  exact hx

lemma mem_segment_of_mem_of_isTheta {n x : Nat} {word : List Nat}
    (hword : IsTheta n word) (hx : x ∈ word) : x ∈ segment n := by
  rw [← hword.1.2, List.mem_toFinset]
  exact hx

lemma positive_of_mem_of_isTheta {n x : Nat} {word : List Nat}
    (hword : IsTheta n word) (hx : x ∈ word) : 0 < x := by
  have hxSegment := mem_segment_of_mem_of_isTheta hword hx
  exact (Finset.mem_Icc.mp (show x ∈ Finset.Icc 1 n from hxSegment)).1

lemma oddLiftValue_injective : Function.Injective (fun x : Nat => 2 * x - 1) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all <;> omega

lemma getElem?_index_pos_of_ne_head {word : List Nat} {i x first : Nat}
    (hx : word[i]? = some x) (hfirst : word[0]? = some first) (hne : x ≠ first) :
    0 < i := by
  by_contra hi
  have hi0 : i = 0 := by omega
  subst i
  apply hne
  exact Option.some.inj (hx.symm.trans hfirst)

lemma getElem?_index_lt_last_of_ne_last {word : List Nat} {i x last : Nat}
    (hx : word[i]? = some x)
    (hlast : word[word.length - 1]? = some last) (hne : x ≠ last) :
    i < word.length - 1 := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hx
  by_contra hilast
  have hiLast : i = word.length - 1 := by omega
  subst i
  apply hne
  exact Option.some.inj (hx.symm.trans hlast)

lemma getElem?_index_unique_of_nodup {word : List Nat} (hword : word.Nodup)
    {i j x : Nat} (hi : word[i]? = some x) (hj : word[j]? = some x) : i = j := by
  obtain ⟨hiLen, hiValue⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hjValue⟩ := List.getElem?_eq_some_iff.mp hj
  exact hword.getElem_inj_iff.mp (hiValue.trans hjValue.symm)

lemma occursLeftOf_total_of_mem {word : List Nat} (_hword : word.Nodup) {x y : Nat}
    (hx : x ∈ word) (hy : y ∈ word) (hne : x ≠ y) :
    OccursLeftOf word x y ∨ OccursLeftOf word y x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hne (Option.some.inj (hi.symm.trans hj))
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Or.inl ⟨i, j, hij, hi, hj⟩
  · exact Or.inr ⟨j, i, hji, hj, hi⟩

lemma not_occursLeftOf_to_head {word : List Nat} (hword : word.Nodup) {x first : Nat}
    (hfirst : word[0]? = some first) : ¬ OccursLeftOf word x first := by
  rintro ⟨i, j, hij, hi, hj⟩
  have hj0 := getElem?_index_unique_of_nodup hword hj hfirst
  omega

lemma containsThreeAP_of_increasing_positions {word : List Nat} {i₀ i₁ i₂ a d : Nat}
    (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hd : 0 < d)
    (h₀ : word[i₀]? = some a) (h₁ : word[i₁]? = some (a + d))
    (h₂ : word[i₂]? = some (a + 2 * d)) : ContainsThreeAP word := by
  let indices : Fin 3 → Nat := ![i₀, i₁, i₂]
  refine ⟨indices, ?_, a, d, hd, Or.inl ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [indices, hi₀₁, hi₁₂]
  · intro i
    fin_cases i <;> simp [indices, h₀, h₁, h₂, Nat.mul_comm]

lemma containsThreeAP_of_decreasing_positions {word : List Nat} {i₀ i₁ i₂ a d : Nat}
    (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hd : 0 < d)
    (h₀ : word[i₀]? = some (a + 2 * d)) (h₁ : word[i₁]? = some (a + d))
    (h₂ : word[i₂]? = some a) : ContainsThreeAP word := by
  let indices : Fin 3 → Nat := ![i₀, i₁, i₂]
  refine ⟨indices, ?_, a, d, hd, Or.inr ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [indices, hi₀₁, hi₁₂]
  · intro i
    fin_cases i <;> simp [indices, h₀, h₁, h₂, Nat.mul_comm]

lemma exists_of_getElem?_map_eq_some {f : Nat -> Nat} {word : List Nat}
    {i y : Nat} (h : (word.map f)[i]? = some y) :
    exists x : Nat, word[i]? = some x /\ f x = y := by
  rw [List.getElem?_map] at h
  cases hx : word[i]? with
  | none => simp [hx] at h
  | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at h
      exact ⟨x, rfl, h⟩

lemma threeFree_evenLift {word : List Nat} (hword : ThreeFree word) :
    ThreeFree (evenLift word) := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    simp only [Fin.val_zero, zero_mul, add_zero] at h0
    norm_num at h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h0
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h1
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    let e := x1 - x0
    have he : 0 < e := by
      dsimp [e]
      omega
    have hx1Eq : x1 = x0 + e := by
      dsimp [e]
      omega
    have hx2Eq : x2 = x0 + 2 * e := by
      dsimp [e]
      omega
    apply hword
    apply containsThreeAP_of_increasing_positions h01 h12 he hx0
    · rw [← hx1Eq]
      exact hx1
    · rw [← hx2Eq]
      exact hx2
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h0
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h1
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x) h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    let e := x1 - x2
    have he : 0 < e := by
      dsimp [e]
      omega
    have hx1Eq : x1 = x2 + e := by
      dsimp [e]
      omega
    have hx0Eq : x0 = x2 + 2 * e := by
      dsimp [e]
      omega
    apply hword
    apply containsThreeAP_of_decreasing_positions (a := x2) h01 h12 he
    · rw [← hx0Eq]
      exact hx0
    · rw [← hx1Eq]
      exact hx1
    · exact hx2

lemma threeFree_oddLift {word : List Nat} (hword : ThreeFree word)
    (hpositive : forall x : Nat, x ∈ word -> 0 < x) :
    ThreeFree (oddLift word) := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    simp only [Fin.val_zero, zero_mul, add_zero] at h0
    norm_num at h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h0
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h1
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h2
    have hx0Pos := hpositive x0 (List.mem_iff_getElem?.mpr ⟨indices 0, hx0⟩)
    have hx1Pos := hpositive x1 (List.mem_iff_getElem?.mpr ⟨indices 1, hx1⟩)
    have hx2Pos := hpositive x2 (List.mem_iff_getElem?.mpr ⟨indices 2, hx2⟩)
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    let e := x1 - x0
    have he : 0 < e := by
      dsimp [e]
      omega
    have hx1Eq : x1 = x0 + e := by
      dsimp [e]
      omega
    have hx2Eq : x2 = x0 + 2 * e := by
      dsimp [e]
      omega
    apply hword
    apply containsThreeAP_of_increasing_positions h01 h12 he hx0
    · rw [← hx1Eq]
      exact hx1
    · rw [← hx2Eq]
      exact hx2
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h0
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h1
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => 2 * x - 1) h2
    have hx0Pos := hpositive x0 (List.mem_iff_getElem?.mpr ⟨indices 0, hx0⟩)
    have hx1Pos := hpositive x1 (List.mem_iff_getElem?.mpr ⟨indices 1, hx1⟩)
    have hx2Pos := hpositive x2 (List.mem_iff_getElem?.mpr ⟨indices 2, hx2⟩)
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    let e := x1 - x2
    have he : 0 < e := by
      dsimp [e]
      omega
    have hx1Eq : x1 = x2 + e := by
      dsimp [e]
      omega
    have hx0Eq : x0 = x2 + 2 * e := by
      dsimp [e]
      omega
    apply hword
    apply containsThreeAP_of_decreasing_positions (a := x2) h01 h12 he
    · rw [← hx0Eq]
      exact hx0
    · rw [← hx1Eq]
      exact hx1
    · exact hx2

lemma threeFree_append_of_mod_two_separated {left right : List Nat}
    (hleft : ThreeFree left) (hright : ThreeFree right)
    (hseparate : forall x : Nat, x ∈ left -> forall y : Nat, y ∈ right ->
      ¬ Nat.ModEq 2 x y) : ThreeFree (left ++ right) := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    simp only [Fin.val_zero, zero_mul, add_zero] at h0
    norm_num at h1 h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    by_cases h0Left : indices 0 < left.length
    · by_cases h2Left : indices 2 < left.length
      · have h0' := h0
        have h1' := h1
        have h2' := h2
        rw [List.getElem?_append_left h0Left] at h0'
        rw [List.getElem?_append_left (by omega)] at h1'
        rw [List.getElem?_append_left h2Left] at h2'
        exact hleft (containsThreeAP_of_increasing_positions h01 h12 hd h0' h1' h2')
      · have h0' := h0
        have h2' := h2
        rw [List.getElem?_append_left h0Left] at h0'
        rw [List.getElem?_append_right (Nat.le_of_not_gt h2Left)] at h2'
        have haMem : a ∈ left :=
          List.mem_iff_getElem?.mpr ⟨indices 0, h0'⟩
        have hcMem : a + 2 * d ∈ right :=
          List.mem_iff_getElem?.mpr ⟨indices 2 - left.length, h2'⟩
        exact (hseparate a haMem (a + 2 * d) hcMem) (by simp [Nat.ModEq])
    · have h0Right : left.length <= indices 0 := Nat.le_of_not_gt h0Left
      have h1Right : left.length <= indices 1 := by omega
      have h2Right : left.length <= indices 2 := by omega
      let shifted : Fin 3 -> Nat := fun i => indices i - left.length
      have hshifted : StrictMono shifted := by
        intro i j hij
        have hij' := hindices hij
        have hiRight : left.length <= indices i :=
          h0Right.trans (hindices.monotone (Fin.zero_le i))
        simp only [shifted]
        omega
      have h0' := h0
      have h1' := h1
      have h2' := h2
      rw [List.getElem?_append_right h0Right] at h0'
      rw [List.getElem?_append_right h1Right] at h1'
      rw [List.getElem?_append_right h2Right] at h2'
      apply hright
      apply containsThreeAP_of_increasing_positions
        (i₀ := shifted 0) (i₁ := shifted 1) (i₂ := shifted 2)
        (hshifted (by decide)) (hshifted (by decide)) hd
      · exact h0'
      · exact h1'
      · exact h2'
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    by_cases h0Left : indices 0 < left.length
    · by_cases h2Left : indices 2 < left.length
      · have h0' := h0
        have h1' := h1
        have h2' := h2
        rw [List.getElem?_append_left h0Left] at h0'
        rw [List.getElem?_append_left (by omega)] at h1'
        rw [List.getElem?_append_left h2Left] at h2'
        exact hleft (containsThreeAP_of_decreasing_positions h01 h12 hd h0' h1' h2')
      · have h0' := h0
        have h2' := h2
        rw [List.getElem?_append_left h0Left] at h0'
        rw [List.getElem?_append_right (Nat.le_of_not_gt h2Left)] at h2'
        have haMem : a + 2 * d ∈ left :=
          List.mem_iff_getElem?.mpr ⟨indices 0, h0'⟩
        have hcMem : a ∈ right :=
          List.mem_iff_getElem?.mpr ⟨indices 2 - left.length, h2'⟩
        exact (hseparate (a + 2 * d) haMem a hcMem) (by simp [Nat.ModEq])
    · have h0Right : left.length <= indices 0 := Nat.le_of_not_gt h0Left
      have h1Right : left.length <= indices 1 := by omega
      have h2Right : left.length <= indices 2 := by omega
      let shifted : Fin 3 -> Nat := fun i => indices i - left.length
      have hshifted : StrictMono shifted := by
        intro i j hij
        have hij' := hindices hij
        have hiRight : left.length <= indices i :=
          h0Right.trans (hindices.monotone (Fin.zero_le i))
        simp only [shifted]
        omega
      have h0' := h0
      have h1' := h1
      have h2' := h2
      rw [List.getElem?_append_right h0Right] at h0'
      rw [List.getElem?_append_right h1Right] at h1'
      rw [List.getElem?_append_right h2Right] at h2'
      apply hright
      apply containsThreeAP_of_decreasing_positions
        (i₀ := shifted 0) (i₁ := shifted 1) (i₂ := shifted 2)
        (hshifted (by decide)) (hshifted (by decide)) hd
      · exact h0'
      · exact h1'
      · exact h2'

lemma odd_even_lifts_mod_two_separated {oddWord evenWord : List Nat}
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    forall x : Nat, x ∈ oddLift oddWord -> forall y : Nat, y ∈ evenLift evenWord ->
      ¬ Nat.ModEq 2 x y := by
  intro x hx y hy
  rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
  have haPos := hpositive a ha
  intro hmod
  have hoddForm : 2 * a - 1 = 2 * (a - 1) + 1 := by omega
  have hoddMod : (2 * a - 1) % 2 = 1 := by rw [hoddForm]; simp
  simp only [Nat.ModEq, Nat.mul_mod_right] at hmod
  omega

lemma even_odd_lifts_mod_two_separated {evenWord oddWord : List Nat}
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    forall x : Nat, x ∈ evenLift evenWord -> forall y : Nat, y ∈ oddLift oddWord ->
      ¬ Nat.ModEq 2 x y := by
  intro x hx y hy
  rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
  have hbPos := hpositive b hb
  intro hmod
  have hoddForm : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
  have hoddMod : (2 * b - 1) % 2 = 1 := by rw [hoddForm]; simp
  simp only [Nat.ModEq, Nat.mul_mod_right] at hmod
  omega

lemma threeFree_oddEvenLifts {oddWord evenWord : List Nat}
    (hodd : ThreeFree oddWord) (heven : ThreeFree evenWord)
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    ThreeFree (oddLift oddWord ++ evenLift evenWord) :=
  threeFree_append_of_mod_two_separated
    (threeFree_oddLift hodd hpositive) (threeFree_evenLift heven)
    (odd_even_lifts_mod_two_separated hpositive)

lemma threeFree_evenOddLifts {evenWord oddWord : List Nat}
    (heven : ThreeFree evenWord) (hodd : ThreeFree oddWord)
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    ThreeFree (evenLift evenWord ++ oddLift oddWord) :=
  threeFree_append_of_mod_two_separated
    (threeFree_evenLift heven) (threeFree_oddLift hodd hpositive)
    (even_odd_lifts_mod_two_separated hpositive)

lemma nodup_oddEvenLifts {oddWord evenWord : List Nat}
    (hodd : oddWord.Nodup) (heven : evenWord.Nodup)
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    (oddLift oddWord ++ evenLift evenWord).Nodup := by
  have hoddLift : (oddLift oddWord).Nodup := by
    exact hodd.map oddLiftValue_injective
  have hevenLift : (evenLift evenWord).Nodup := by
    exact heven.map (by intro x y hxy; simp only at hxy; omega)
  rw [List.nodup_append]
  refine ⟨hoddLift, hevenLift, ?_⟩
  intro x hx y hy hxy
  exact (odd_even_lifts_mod_two_separated hpositive x hx y hy)
    (hxy ▸ Nat.ModEq.rfl)

lemma nodup_evenOddLifts {evenWord oddWord : List Nat}
    (heven : evenWord.Nodup) (hodd : oddWord.Nodup)
    (hpositive : forall x : Nat, x ∈ oddWord -> 0 < x) :
    (evenLift evenWord ++ oddLift oddWord).Nodup := by
  have hevenLift : (evenLift evenWord).Nodup := by
    exact heven.map (by intro x y hxy; simp only at hxy; omega)
  have hoddLift : (oddLift oddWord).Nodup := by
    exact hodd.map oddLiftValue_injective
  rw [List.nodup_append]
  refine ⟨hevenLift, hoddLift, ?_⟩
  intro x hx y hy hxy
  exact (even_odd_lifts_mod_two_separated hpositive x hx y hy)
    (hxy ▸ Nat.ModEq.rfl)

lemma mem_evenLift_iff {k x : Nat} {word : List Nat} (hword : IsTheta k word) :
    x ∈ evenLift word ↔ Even x /\ 1 <= x /\ x <= 2 * k := by
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haSegment := mem_segment_of_mem_of_isTheta hword ha
    have haBounds := Finset.mem_Icc.mp (show a ∈ Finset.Icc 1 k from haSegment)
    exact ⟨⟨a, by omega⟩, by omega, by omega⟩
  · rintro ⟨⟨a, ha⟩, hxPos, hxTop⟩
    have haSegment : a ∈ segment k := by
      simp only [segment, Finset.mem_Icc]
      omega
    have haMem := mem_of_mem_segment_of_isTheta hword haSegment
    apply List.mem_map.mpr
    exact ⟨a, haMem, by omega⟩

lemma mem_oddLift_iff {k x : Nat} {word : List Nat} (hword : IsTheta k word) :
    x ∈ oddLift word ↔ Odd x /\ 1 <= x /\ x <= 2 * k - 1 := by
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haSegment := mem_segment_of_mem_of_isTheta hword ha
    have haBounds := Finset.mem_Icc.mp (show a ∈ Finset.Icc 1 k from haSegment)
    refine ⟨?_, by omega, by omega⟩
    exact ⟨a - 1, by omega⟩
  · rintro ⟨⟨a, ha⟩, hxPos, hxTop⟩
    have haSegment : a + 1 ∈ segment k := by
      simp only [segment, Finset.mem_Icc]
      omega
    have haMem := mem_of_mem_segment_of_isTheta hword haSegment
    apply List.mem_map.mpr
    exact ⟨a + 1, haMem, by omega⟩

lemma oddEvenLifts_toFinset_even {k : Nat} {oddWord evenWord : List Nat}
    (hodd : IsTheta k oddWord) (heven : IsTheta k evenWord) :
    (oddLift oddWord ++ evenLift evenWord).toFinset = segment (2 * k) := by
  apply Finset.ext
  intro x
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset]
  rw [mem_oddLift_iff hodd, mem_evenLift_iff heven]
  simp only [segment, Finset.mem_Icc]
  constructor
  · rintro (⟨_, hx, htop⟩ | ⟨_, hx, htop⟩)
    · exact ⟨hx, by omega⟩
    · exact ⟨hx, htop⟩
  · intro hx
    rcases Nat.even_or_odd x with hEven | hOdd
    · exact Or.inr ⟨hEven, hx.1, hx.2⟩
    · exact Or.inl ⟨hOdd, hx.1, by grind⟩

lemma oddEvenLifts_toFinset_odd {k : Nat} {oddWord evenWord : List Nat}
    (hodd : IsTheta (k + 1) oddWord) (heven : IsTheta k evenWord) :
    (oddLift oddWord ++ evenLift evenWord).toFinset = segment (2 * k + 1) := by
  apply Finset.ext
  intro x
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset]
  rw [mem_oddLift_iff hodd, mem_evenLift_iff heven]
  simp only [segment, Finset.mem_Icc]
  constructor
  · rintro (⟨_, hx, htop⟩ | ⟨_, hx, htop⟩)
    · exact ⟨hx, by omega⟩
    · exact ⟨hx, by omega⟩
  · intro hx
    rcases Nat.even_or_odd x with hEven | hOdd
    · exact Or.inr ⟨hEven, hx.1, by grind⟩
    · exact Or.inl ⟨hOdd, hx.1, by omega⟩

lemma evenOddLifts_toFinset_even {k : Nat} {evenWord oddWord : List Nat}
    (heven : IsTheta k evenWord) (hodd : IsTheta k oddWord) :
    (evenLift evenWord ++ oddLift oddWord).toFinset = segment (2 * k) := by
  rw [List.toFinset_append, Finset.union_comm, ← List.toFinset_append]
  exact oddEvenLifts_toFinset_even hodd heven

lemma evenOddLifts_toFinset_odd {k : Nat} {evenWord oddWord : List Nat}
    (heven : IsTheta k evenWord) (hodd : IsTheta (k + 1) oddWord) :
    (evenLift evenWord ++ oddLift oddWord).toFinset = segment (2 * k + 1) := by
  rw [List.toFinset_append, Finset.union_comm, ← List.toFinset_append]
  exact oddEvenLifts_toFinset_odd hodd heven

lemma isTheta_oddEvenLifts_even {k : Nat} {oddWord evenWord : List Nat}
    (hodd : IsTheta k oddWord) (heven : IsTheta k evenWord) :
    IsTheta (2 * k) (oddLift oddWord ++ evenLift evenWord) := by
  refine ⟨⟨?_, oddEvenLifts_toFinset_even hodd heven⟩, ?_⟩
  · exact nodup_oddEvenLifts (isTheta_nodup hodd) (isTheta_nodup heven)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)
  · exact threeFree_oddEvenLifts (isTheta_threeFree hodd) (isTheta_threeFree heven)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)

lemma isTheta_evenOddLifts_even {k : Nat} {evenWord oddWord : List Nat}
    (heven : IsTheta k evenWord) (hodd : IsTheta k oddWord) :
    IsTheta (2 * k) (evenLift evenWord ++ oddLift oddWord) := by
  refine ⟨⟨?_, evenOddLifts_toFinset_even heven hodd⟩, ?_⟩
  · exact nodup_evenOddLifts (isTheta_nodup heven) (isTheta_nodup hodd)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)
  · exact threeFree_evenOddLifts (isTheta_threeFree heven) (isTheta_threeFree hodd)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)

lemma isTheta_oddEvenLifts_odd {k : Nat} {oddWord evenWord : List Nat}
    (hodd : IsTheta (k + 1) oddWord) (heven : IsTheta k evenWord) :
    IsTheta (2 * k + 1) (oddLift oddWord ++ evenLift evenWord) := by
  refine ⟨⟨?_, oddEvenLifts_toFinset_odd hodd heven⟩, ?_⟩
  · exact nodup_oddEvenLifts (isTheta_nodup hodd) (isTheta_nodup heven)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)
  · exact threeFree_oddEvenLifts (isTheta_threeFree hodd) (isTheta_threeFree heven)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)

lemma isTheta_evenOddLifts_odd {k : Nat} {evenWord oddWord : List Nat}
    (heven : IsTheta k evenWord) (hodd : IsTheta (k + 1) oddWord) :
    IsTheta (2 * k + 1) (evenLift evenWord ++ oddLift oddWord) := by
  refine ⟨⟨?_, evenOddLifts_toFinset_odd heven hodd⟩, ?_⟩
  · exact nodup_evenOddLifts (isTheta_nodup heven) (isTheta_nodup hodd)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)
  · exact threeFree_evenOddLifts (isTheta_threeFree heven) (isTheta_threeFree hodd)
      (fun x hx => positive_of_mem_of_isTheta hodd hx)

lemma startsWith_oddLift {word : List Nat} {x : Nat} (h : StartsWith word x) :
    StartsWith (oddLift word) (2 * x - 1) := by
  unfold StartsWith at h ⊢
  simp only [oddLift, List.head?_map, h, Option.map_some]

lemma startsWith_evenLift {word : List Nat} {x : Nat} (h : StartsWith word x) :
    StartsWith (evenLift word) (2 * x) := by
  unfold StartsWith at h ⊢
  simp only [evenLift, List.head?_map, h, Option.map_some]

lemma StartsWith.append {left right : List Nat} {x : Nat} (h : StartsWith left x) :
    StartsWith (left ++ right) x := by
  have hleft : left ≠ [] := by
    intro hnil
    subst left
    simp [StartsWith] at h
  rw [StartsWith, List.head?_append_of_ne_nil left hleft]
  exact h

lemma threeFree_of_length_lt_three {word : List Nat} (hlength : word.length < 3) :
    ThreeFree word := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues⟩
  rcases hvalues with hvalues | hvalues
  · have h2 := hvalues (2 : Fin 3)
    obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.mp h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    omega
  · have h2 := hvalues (2 : Fin 3)
    obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.mp h2
    have h01 : indices 0 < indices 1 := hindices (by decide)
    have h12 : indices 1 < indices 2 := hindices (by decide)
    omega

lemma singleton_one_isTheta : IsTheta 1 [1] := by
  refine ⟨⟨by simp, ?_⟩, threeFree_of_length_lt_three (by simp)⟩
  simp [segment]

lemma complementValue_mem_segment {n x : Nat} (hx : x ∈ segment n) :
    n + 1 - x ∈ segment n := by
  simp only [segment, Finset.mem_Icc] at hx ⊢
  omega

lemma sameHalf_complement_iff_of_even {n x y : Nat} (hn : Even n)
    (hx : x ∈ segment n) (hy : y ∈ segment n) :
    SameHalf n (n + 1 - x) (n + 1 - y) ↔ SameHalf n x y := by
  rcases hn with ⟨k, hk⟩
  have hnEq : n = 2 * k := by omega
  subst n
  simp only [segment, lowerHalf, upperHalf, SameHalf, Finset.mem_Icc] at hx hy ⊢
  omega

lemma sameHalf_complement_iff_of_odd_away_middle {n x y : Nat} (hn : Odd n)
    (hx : x ∈ segment n) (hy : y ∈ segment n)
    (hxMiddle : x ≠ (n + 1) / 2) (hyMiddle : y ≠ (n + 1) / 2) :
    SameHalf n (n + 1 - x) (n + 1 - y) ↔ SameHalf n x y := by
  rcases hn with ⟨k, hk⟩
  subst n
  simp only [segment, lowerHalf, upperHalf, SameHalf, Finset.mem_Icc] at hx hy ⊢
  norm_num at hxMiddle hyMiddle ⊢
  omega

lemma takeWhile_length_eq_of_prefix_and_stop {p q : Nat -> Bool} {xs : List Nat}
    (hpq : forall x : Nat, x ∈ xs.takeWhile p -> q x = true)
    (hstop : match (xs.dropWhile p).head? with
      | none => True
      | some x => q x = false) :
    (xs.takeWhile q).length = (xs.takeWhile p).length := by
  let pre := xs.takeWhile p
  let rest := xs.dropWhile p
  have hdecomp : pre ++ rest = xs := by
    exact List.takeWhile_append_dropWhile
  have hprefix : forall x : Nat, x ∈ pre -> q x := by
    intro x hx
    exact hpq x hx
  change (xs.takeWhile q).length = pre.length
  rw [← hdecomp, List.takeWhile_append_of_pos hprefix]
  cases hrest : rest with
  | nil => simp
  | cons x ys =>
      have hqx : q x = false := by simpa [rest, hrest] using hstop
      simp [hqx]

private lemma right_endpoint_left_of_middle_aux {n : Nat} {word : List Nat}
    (hword : IsTheta n word) {a d : Nat} (hd : 0 < d)
    (hm : a + d ∈ word) (hc : a + 2 * d ∈ word)
    (ham : OccursLeftOf word a (a + d)) :
    OccursLeftOf word (a + 2 * d) (a + d) := by
  rcases occursLeftOf_total_of_mem (isTheta_nodup hword) hc hm (by omega) with hcm | hmc
  · exact hcm
  · rcases ham with ⟨i, j, hij, hi, hj⟩
    rcases hmc with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' :=
      getElem?_index_unique_of_nodup (isTheta_nodup hword) hj hj'
    subst j'
    exfalso
    exact (isTheta_threeFree hword)
      (containsThreeAP_of_increasing_positions hij hjk hd hi hj hk)

lemma odd_middle_not_first_outside_half {n first : Nat} {tail : List Nat}
    (hn : Odd n) (hword : IsTheta n (first :: tail)) :
    let middle := (n + 1) / 2
    let p := fun y : Nat => decide (SameHalf n first y)
    (tail.dropWhile p).head? ≠ some middle := by
  rcases hn with ⟨k, hk⟩
  subst n
  dsimp only
  let middle := k + 1
  let p := fun y : Nat => decide (SameHalf (2 * k + 1) first y)
  intro hhead
  have hmiddleEq : (2 * k + 1 + 1) / 2 = middle := by
    dsimp [middle]
    omega
  rw [hmiddleEq] at hhead
  have hfirstMem : first ∈ first :: tail := by simp
  have hfirstSegment := mem_segment_of_mem_of_isTheta hword hfirstMem
  have hfirstBounds :=
    Finset.mem_Icc.mp (show first ∈ Finset.Icc 1 (2 * k + 1) from hfirstSegment)
  have hpMiddleFalse : p middle = false := by
    simpa [p, middle, hhead] using List.head?_dropWhile_not p tail
  have hnotSame : ¬ SameHalf (2 * k + 1) first middle := by
    simpa [p] using hpMiddleFalse
  have hfirstLower : first ∈ lowerHalf (2 * k + 1) := by
    simp only [middle, SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hnotSame ⊢
    omega
  let pre := tail.takeWhile p
  let rest := tail.dropWhile p
  have hdecomp : pre ++ rest = tail := List.takeWhile_append_dropWhile
  change rest.head? = some middle at hhead
  cases hrest : rest with
  | nil => simp [hrest] at hhead
  | cons y ys =>
      have hyMiddle : y = middle := by simpa [hrest] using hhead
      subst y
      have htailEq : tail = pre ++ middle :: ys := by
        rw [← hdecomp, hrest]
      have hfirstAt : (first :: tail)[0]? = some first := by simp
      have hmiddleAt : (first :: tail)[pre.length + 1]? = some middle := by
        rw [htailEq]
        simp
      have hmiddleSegment : middle ∈ segment (2 * k + 1) := by
        simp only [middle, segment, Finset.mem_Icc]
        omega
      let reflected := 2 * k + 2 - first
      have hreflectedSegment : reflected ∈ segment (2 * k + 1) := by
        exact complementValue_mem_segment hfirstSegment
      have hmiddleMem := mem_of_mem_segment_of_isTheta hword hmiddleSegment
      have hreflectedMem := mem_of_mem_segment_of_isTheta hword hreflectedSegment
      let d := middle - first
      have hd : 0 < d := by
        simp only [middle, lowerHalf, Finset.mem_Icc] at hfirstLower
        dsimp [d]
        omega
      have hmidEq : first + d = middle := by
        dsimp [d]
        omega
      have hreflectEq : first + 2 * d = reflected := by
        dsimp [d, reflected, middle]
        omega
      have hfirstMiddle : OccursLeftOf (first :: tail) first middle :=
        ⟨0, pre.length + 1, by omega, hfirstAt, hmiddleAt⟩
      have hreflectionBefore : OccursLeftOf (first :: tail) reflected middle := by
        have h := right_endpoint_left_of_middle_aux hword
          (a := first) (d := d) hd
          (hmidEq ▸ hmiddleMem) (hreflectEq ▸ hreflectedMem)
          (by simpa [hmidEq] using hfirstMiddle)
        simpa [hmidEq, hreflectEq] using h
      rcases hreflectionBefore with ⟨i, j, hij, hi, hj⟩
      have hjEq : j = pre.length + 1 :=
        getElem?_index_unique_of_nodup (isTheta_nodup hword) hj hmiddleAt
      subst j
      have hreflectedNeFirst : reflected ≠ first := by
        dsimp [reflected]
        simp only [lowerHalf, Finset.mem_Icc] at hfirstLower
        omega
      have hiPos := getElem?_index_pos_of_ne_head hi hfirstAt hreflectedNeFirst
      have hiPre : i - 1 < pre.length := by omega
      have hi' := hi
      rw [htailEq, List.getElem?_cons, if_neg (by omega)] at hi'
      rw [List.getElem?_append_left hiPre] at hi'
      have hreflectedPre : reflected ∈ pre :=
        List.mem_iff_getElem?.mpr ⟨i - 1, hi'⟩
      have hpReflected : p reflected = true :=
        List.mem_takeWhile_imp hreflectedPre
      have hreflectedUpper : reflected ∈ upperHalf (2 * k + 1) := by
        simp only [reflected, upperHalf, Finset.mem_Icc]
        simp only [lowerHalf, Finset.mem_Icc] at hfirstLower
        omega
      have hnotSameReflected : ¬ SameHalf (2 * k + 1) first reflected := by
        simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hfirstLower hreflectedUpper ⊢
        omega
      exact hnotSameReflected (by simpa [p] using hpReflected)

lemma right_endpoint_left_of_middle_of_left_endpoint {n : Nat} {word : List Nat}
    (hword : IsTheta n word) {a d : Nat} (hd : 0 < d)
    (_ha : a ∈ word) (hm : a + d ∈ word) (hc : a + 2 * d ∈ word)
    (ham : OccursLeftOf word a (a + d)) :
    OccursLeftOf word (a + 2 * d) (a + d) := by
  rcases occursLeftOf_total_of_mem (isTheta_nodup hword) hc hm (by omega) with hcm | hmc
  · exact hcm
  · rcases ham with ⟨i, j, hij, hi, hj⟩
    rcases hmc with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' :=
      getElem?_index_unique_of_nodup (isTheta_nodup hword) hj hj'
    subst j'
    exfalso
    exact (isTheta_threeFree hword)
      (containsThreeAP_of_increasing_positions hij hjk hd hi hj hk)

lemma middle_left_of_right_endpoint_of_middle_left {n : Nat} {word : List Nat}
    (hword : IsTheta n word) {a d : Nat} (hd : 0 < d)
    (_ha : a ∈ word) (hm : a + d ∈ word) (hc : a + 2 * d ∈ word)
    (hma : OccursLeftOf word (a + d) a) :
    OccursLeftOf word (a + d) (a + 2 * d) := by
  rcases occursLeftOf_total_of_mem (isTheta_nodup hword) hm hc (by omega) with hmc | hcm
  · exact hmc
  · rcases hcm with ⟨i, j, hij, hi, hj⟩
    rcases hma with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' :=
      getElem?_index_unique_of_nodup (isTheta_nodup hword) hj hj'
    subst j'
    exfalso
    exact (isTheta_threeFree hword)
      (containsThreeAP_of_decreasing_positions hij hjk hd hi hj hk)

lemma consecutive_odd_before_even_of_one_left_two {n : Nat} {word : List Nat}
    (hword : IsTheta n word) (honeTwo : OccursLeftOf word 1 2) :
    forall x : Nat, x ∈ segment n -> x + 1 ∈ segment n ->
      (Odd x -> OccursLeftOf word x (x + 1)) /\
      (Even x -> OccursLeftOf word (x + 1) x) := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
      intro hx hxNext
      have hxPos : 1 <= x := by
        simpa [segment] using (Finset.mem_Icc.mp hx).1
      by_cases hxOne : x = 1
      · subst x
        constructor
        · intro _
          exact honeTwo
        · intro hxEven
          norm_num at hxEven
      · have hxTwo : 2 <= x := by omega
        have hxPrev : x - 1 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hx hxNext ⊢
          omega
        have hprevNext : x - 1 + 1 ∈ segment n := by
          convert hx using 1 <;> omega
        have hprev := ih (x - 1) (by omega) hxPrev hprevNext
        have ha : x - 1 ∈ word := mem_of_mem_segment_of_isTheta hword hxPrev
        have hm0 : x ∈ word := mem_of_mem_segment_of_isTheta hword hx
        have hc0 : x + 1 ∈ word := mem_of_mem_segment_of_isTheta hword hxNext
        have hmidEq : x - 1 + 1 = x := by omega
        have hrightEq : x - 1 + 2 * 1 = x + 1 := by omega
        have hm : x - 1 + 1 ∈ word := by simpa [hmidEq] using hm0
        have hc : x - 1 + 2 * 1 ∈ word := by simpa [hrightEq] using hc0
        constructor
        · intro hxOdd
          have hprevEven : Even (x - 1) := by grind
          have hmiddleLeft : OccursLeftOf word (x - 1 + 1) (x - 1) :=
            hprev.2 hprevEven
          have hresult := middle_left_of_right_endpoint_of_middle_left hword
            (a := x - 1) (d := 1) (by omega) ha hm hc hmiddleLeft
          simpa [hmidEq, hrightEq] using hresult
        · intro hxEven
          have hprevOdd : Odd (x - 1) := by grind
          have hleft : OccursLeftOf word (x - 1) (x - 1 + 1) :=
            hprev.1 hprevOdd
          have hresult := right_endpoint_left_of_middle_of_left_endpoint hword
            (a := x - 1) (d := 1) (by omega) ha hm hc hleft
          simpa [hmidEq, hrightEq] using hresult

lemma consecutive_even_before_odd_of_two_left_one {n : Nat} {word : List Nat}
    (hword : IsTheta n word) (htwoOne : OccursLeftOf word 2 1) :
    forall x : Nat, x ∈ segment n -> x + 1 ∈ segment n ->
      (Odd x -> OccursLeftOf word (x + 1) x) /\
      (Even x -> OccursLeftOf word x (x + 1)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
      intro hx hxNext
      have hxPos : 1 <= x := by
        simpa [segment] using (Finset.mem_Icc.mp hx).1
      by_cases hxOne : x = 1
      · subst x
        constructor
        · intro _
          exact htwoOne
        · intro hxEven
          norm_num at hxEven
      · have hxTwo : 2 <= x := by omega
        have hxPrev : x - 1 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hx hxNext ⊢
          omega
        have hprevNext : x - 1 + 1 ∈ segment n := by
          convert hx using 1 <;> omega
        have hprev := ih (x - 1) (by omega) hxPrev hprevNext
        have ha : x - 1 ∈ word := mem_of_mem_segment_of_isTheta hword hxPrev
        have hm0 : x ∈ word := mem_of_mem_segment_of_isTheta hword hx
        have hc0 : x + 1 ∈ word := mem_of_mem_segment_of_isTheta hword hxNext
        have hmidEq : x - 1 + 1 = x := by omega
        have hrightEq : x - 1 + 2 * 1 = x + 1 := by omega
        have hm : x - 1 + 1 ∈ word := by simpa [hmidEq] using hm0
        have hc : x - 1 + 2 * 1 ∈ word := by simpa [hrightEq] using hc0
        constructor
        · intro hxOdd
          have hprevEven : Even (x - 1) := by grind
          have hleft : OccursLeftOf word (x - 1) (x - 1 + 1) :=
            hprev.2 hprevEven
          have hresult := right_endpoint_left_of_middle_of_left_endpoint hword
            (a := x - 1) (d := 1) (by omega) ha hm hc hleft
          simpa [hmidEq, hrightEq] using hresult
        · intro hxEven
          have hprevOdd : Odd (x - 1) := by grind
          have hmiddleLeft : OccursLeftOf word (x - 1 + 1) (x - 1) :=
            hprev.1 hprevOdd
          have hresult := middle_left_of_right_endpoint_of_middle_left hword
            (a := x - 1) (d := 1) (by omega) ha hm hc hmiddleLeft
          simpa [hmidEq, hrightEq] using hresult

/-! ## Section 2: structural results -/

/-- **Proposition 2.1.** The endpoints of a progression-free permutation have
opposite parity. -/
theorem proposition_2_1_holds : proposition_2_1 := by
  intro n gamma hn hgamma
  have hlength : gamma.length = n := isTheta_length hgamma
  have hneNil : gamma ≠ [] := by
    intro hnil
    subst gamma
    simp at hlength
    omega
  let first := gamma.head hneNil
  let last := gamma.getLast hneNil
  have hfirst : StartsWith gamma first := by
    exact List.head?_eq_some_head hneNil
  have hlast : EndsWith gamma last := by
    exact List.getLast?_eq_some_getLast hneNil
  refine ⟨first, last, hfirst, hlast, ?_⟩
  intro hparity
  have hfirstAt : gamma[0]? = some first := by
    rw [← List.head?_eq_getElem?]
    exact hfirst
  have hlastAt : gamma[gamma.length - 1]? = some last := by
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hlengthTwo : 2 <= gamma.length := by omega
  have hfirstLastNe : first ≠ last := by
    intro heq
    have hindexNe := (List.nodup_iff_getElem?_ne_getElem?.mp (isTheta_nodup hgamma))
      0 (gamma.length - 1) (by omega) (by omega)
    exact hindexNe (hfirstAt.trans ((congrArg some heq).trans hlastAt.symm))
  have hfirstMem : first ∈ gamma :=
    List.mem_iff_getElem?.mpr ⟨0, hfirstAt⟩
  have hlastMem : last ∈ gamma :=
    List.mem_iff_getElem?.mpr ⟨gamma.length - 1, hlastAt⟩
  have hfirstSegment := mem_segment_of_mem_of_isTheta hgamma hfirstMem
  have hlastSegment := mem_segment_of_mem_of_isTheta hgamma hlastMem
  rcases lt_or_gt_of_ne hfirstLastNe with hfirstLast | hlastFirst
  · obtain ⟨d, hlastEq⟩ :=
      (Nat.modEq_iff_exists_eq_add hfirstLast.le).mp hparity
    have hd : 0 < d := by omega
    let middle := first + d
    have hmiddleSegment : middle ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at hfirstSegment hlastSegment ⊢
      dsimp [middle]
      omega
    have hmiddleMem := mem_of_mem_segment_of_isTheta hgamma hmiddleSegment
    obtain ⟨i, hmiddleAt⟩ := List.mem_iff_getElem?.mp hmiddleMem
    have hmiddleNeFirst : middle ≠ first := by
      dsimp [middle]
      omega
    have hmiddleNeLast : middle ≠ last := by
      dsimp [middle]
      omega
    have hiPos := getElem?_index_pos_of_ne_head hmiddleAt hfirstAt hmiddleNeFirst
    have hiLast := getElem?_index_lt_last_of_ne_last hmiddleAt hlastAt hmiddleNeLast
    apply isTheta_threeFree hgamma
    apply containsThreeAP_of_increasing_positions hiPos hiLast hd hfirstAt
      hmiddleAt
    calc
      gamma[gamma.length - 1]? = some last := hlastAt
      _ = some (first + 2 * d) := by rw [hlastEq]
  · obtain ⟨d, hfirstEq⟩ :=
      (Nat.modEq_iff_exists_eq_add hlastFirst.le).mp hparity.symm
    have hd : 0 < d := by omega
    let middle := last + d
    have hmiddleSegment : middle ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at hfirstSegment hlastSegment ⊢
      dsimp [middle]
      omega
    have hmiddleMem := mem_of_mem_segment_of_isTheta hgamma hmiddleSegment
    obtain ⟨i, hmiddleAt⟩ := List.mem_iff_getElem?.mp hmiddleMem
    have hmiddleNeFirst : middle ≠ first := by
      dsimp [middle]
      omega
    have hmiddleNeLast : middle ≠ last := by
      dsimp [middle]
      omega
    have hiPos := getElem?_index_pos_of_ne_head hmiddleAt hfirstAt hmiddleNeFirst
    have hiLast := getElem?_index_lt_last_of_ne_last hmiddleAt hlastAt hmiddleNeLast
    apply isTheta_threeFree hgamma
    apply containsThreeAP_of_decreasing_positions hiPos hiLast hd
    · calc
        gamma[0]? = some first := hfirstAt
        _ = some (last + 2 * d) := by rw [hfirstEq]
    · exact hmiddleAt
    · exact hlastAt

/-- **Proposition 2.2.** The orientation `1 < 2` forces an odd first entry. -/
theorem proposition_2_2_holds : proposition_2_2 := by
  intro n gamma hgamma honeTwo
  refine ⟨hgamma, ?_⟩
  rcases honeTwo with ⟨i, j, hij, hi, hj⟩
  have hneNil : gamma ≠ [] := by
    intro hnil
    subst gamma
    simp at hi
  let first := gamma.head hneNil
  have hfirst : StartsWith gamma first := List.head?_eq_some_head hneNil
  refine ⟨first, hfirst, ?_⟩
  rcases Nat.even_or_odd first with hfirstEven | hfirstOdd
  · have honeTwo : OccursLeftOf gamma 1 2 := ⟨i, j, hij, hi, hj⟩
    have hfirstAt : gamma[0]? = some first := by
      rw [← List.head?_eq_getElem?]
      exact hfirst
    have hfirstMem : first ∈ gamma :=
      List.mem_iff_getElem?.mpr ⟨0, hfirstAt⟩
    have hfirstSegment := mem_segment_of_mem_of_isTheta hgamma hfirstMem
    have hfirstTwo : 2 <= first := by
      simp only [segment, Finset.mem_Icc] at hfirstSegment
      grind
    have hprevSegment : first - 1 ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at hfirstSegment ⊢
      omega
    have hprevNextSegment : first - 1 + 1 ∈ segment n := by
      convert hfirstSegment using 1 <;> omega
    have hprevOdd : Odd (first - 1) := by grind
    have horient := consecutive_odd_before_even_of_one_left_two hgamma honeTwo
      (first - 1) hprevSegment hprevNextSegment
    have hbefore : OccursLeftOf gamma (first - 1) first := by
      convert horient.1 hprevOdd using 1 <;> omega
    exfalso
    exact (not_occursLeftOf_to_head (isTheta_nodup hgamma) hfirstAt) hbefore
  · exact hfirstOdd

/-- **Proposition 2.3.** Every consecutive odd/even pair has the canonical
orientation in a `Theta_12` word. -/
theorem proposition_2_3_holds : proposition_2_3 := by
  intro n gamma x hgamma12 hx hxNext
  rcases hgamma12 with ⟨hgamma, ⟨first, hfirst, hfirstOdd⟩⟩
  have hxBounds : 1 <= x ∧ x + 1 <= n := by
    simpa only [segment, Finset.mem_Icc] using ⟨(Finset.mem_Icc.mp hx).1,
      (Finset.mem_Icc.mp hxNext).2⟩
  have honeSegment : 1 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have htwoSegment : 2 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have honeMem := mem_of_mem_segment_of_isTheta hgamma honeSegment
  have htwoMem := mem_of_mem_segment_of_isTheta hgamma htwoSegment
  have honeTwo : OccursLeftOf gamma 1 2 := by
    rcases occursLeftOf_total_of_mem (isTheta_nodup hgamma) honeMem htwoMem (by omega) with
      honeTwo | htwoOne
    · exact honeTwo
    · exfalso
      have hfirstAt : gamma[0]? = some first := by
        rw [← List.head?_eq_getElem?]
        exact hfirst
      have hfirstMem : first ∈ gamma :=
        List.mem_iff_getElem?.mpr ⟨0, hfirstAt⟩
      have hfirstSegment := mem_segment_of_mem_of_isTheta hgamma hfirstMem
      by_cases hfirstOne : first = 1
      · subst first
        exact (not_occursLeftOf_to_head (isTheta_nodup hgamma) hfirstAt) htwoOne
      · have hfirstTwo : 2 <= first := by
          simp only [segment, Finset.mem_Icc] at hfirstSegment
          omega
        have hprevSegment : first - 1 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hfirstSegment ⊢
          omega
        have hprevNextSegment : first - 1 + 1 ∈ segment n := by
          convert hfirstSegment using 1 <;> omega
        have hprevEven : Even (first - 1) := by grind
        have hreverse := consecutive_even_before_odd_of_two_left_one hgamma htwoOne
          (first - 1) hprevSegment hprevNextSegment
        have hbefore : OccursLeftOf gamma (first - 1) first := by
          convert hreverse.2 hprevEven using 1 <;> omega
        exact (not_occursLeftOf_to_head (isTheta_nodup hgamma) hfirstAt) hbefore
  exact consecutive_odd_before_even_of_one_left_two hgamma honeTwo x hx hxNext

/-- **Proposition 2.4.** Every entry of `[n]` can begin a progression-free
permutation. -/
theorem proposition_2_4_holds : proposition_2_4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro j hj
      have hjBounds := Finset.mem_Icc.mp (show j ∈ Finset.Icc 1 n from hj)
      by_cases hnZero : n = 0
      · omega
      by_cases hnOne : n = 1
      · subst n
        have hjOne : j = 1 := by omega
        subst j
        exact ⟨[1], singleton_one_isTheta, by simp [StartsWith]⟩
      have hnTwo : 2 <= n := by omega
      rcases Nat.even_or_odd n with hnEven | hnOdd
      · rcases hnEven with ⟨k, hk⟩
        have hnEq : n = 2 * k := by omega
        have hkPos : 0 < k := by omega
        rcases Nat.even_or_odd j with hjEven | hjOdd
        · rcases hjEven with ⟨a, ha⟩
          have haSegment : a ∈ segment k := by
            simp only [segment, Finset.mem_Icc]
            omega
          obtain ⟨delta, hdelta, hdeltaStart⟩ := ih k (by omega) a haSegment
          let gamma := evenLift delta ++ oddLift delta
          refine ⟨gamma, ?_, ?_⟩
          · simpa [gamma, hnEq] using isTheta_evenOddLifts_even hdelta hdelta
          · have hstart := (startsWith_evenLift hdeltaStart).append (right := oddLift delta)
            simpa [gamma] using (show StartsWith (evenLift delta ++ oddLift delta) j by
              convert hstart using 1 <;> omega)
        · rcases hjOdd with ⟨a, ha⟩
          have haSegment : a + 1 ∈ segment k := by
            simp only [segment, Finset.mem_Icc]
            omega
          obtain ⟨delta, hdelta, hdeltaStart⟩ := ih k (by omega) (a + 1) haSegment
          let gamma := oddLift delta ++ evenLift delta
          refine ⟨gamma, ?_, ?_⟩
          · simpa [gamma, hnEq] using isTheta_oddEvenLifts_even hdelta hdelta
          · have hstart := (startsWith_oddLift hdeltaStart).append (right := evenLift delta)
            simpa [gamma] using (show StartsWith (oddLift delta ++ evenLift delta) j by
              convert hstart using 1 <;> omega)
      · rcases hnOdd with ⟨k, hk⟩
        have hnEq : n = 2 * k + 1 := by omega
        have hkPos : 0 < k := by omega
        have honeK : 1 ∈ segment k := by
          simp only [segment, Finset.mem_Icc]
          omega
        have honeKSuc : 1 ∈ segment (k + 1) := by
          simp only [segment, Finset.mem_Icc]
          omega
        rcases Nat.even_or_odd j with hjEven | hjOdd
        · rcases hjEven with ⟨a, ha⟩
          have haSegment : a ∈ segment k := by
            simp only [segment, Finset.mem_Icc]
            omega
          obtain ⟨evenWord, heven, hevenStart⟩ := ih k (by omega) a haSegment
          obtain ⟨oddWord, hodd, _⟩ := ih (k + 1) (by omega) 1 honeKSuc
          let gamma := evenLift evenWord ++ oddLift oddWord
          refine ⟨gamma, ?_, ?_⟩
          · simpa [gamma, hnEq] using isTheta_evenOddLifts_odd heven hodd
          · have hstart := (startsWith_evenLift hevenStart).append (right := oddLift oddWord)
            simpa [gamma] using (show StartsWith (evenLift evenWord ++ oddLift oddWord) j by
              convert hstart using 1 <;> omega)
        · rcases hjOdd with ⟨a, ha⟩
          have haSegment : a + 1 ∈ segment (k + 1) := by
            simp only [segment, Finset.mem_Icc]
            omega
          obtain ⟨oddWord, hodd, hoddStart⟩ := ih (k + 1) (by omega) (a + 1) haSegment
          obtain ⟨evenWord, heven, _⟩ := ih k (by omega) 1 honeK
          let gamma := oddLift oddWord ++ evenLift evenWord
          refine ⟨gamma, ?_, ?_⟩
          · simpa [gamma, hnEq] using isTheta_oddEvenLifts_odd hodd heven
          · have hstart := (startsWith_oddLift hoddStart).append (right := evenLift evenWord)
            simpa [gamma] using (show StartsWith (oddLift oddWord ++ evenLift evenWord) j by
              convert hstart using 1 <;> omega)

/-- **Proposition 2.5.** Complementation preserves the prologue length away
from the exceptional central entry in an odd segment. -/
theorem proposition_2_5_holds : proposition_2_5 := by
  intro n gamma hgamma hexception
  cases gamma with
  | nil => simp [prologue, complement]
  | cons first tail =>
      let p := fun y : Nat => decide (SameHalf n first y)
      let q := fun y : Nat =>
        decide (SameHalf n (n + 1 - first) (n + 1 - y))
      have hfirstMem : first ∈ first :: tail := by simp
      have hfirstSegment := mem_segment_of_mem_of_isTheta hgamma hfirstMem
      have hprefixSegment : forall y : Nat, y ∈ tail.takeWhile p -> y ∈ segment n := by
        intro y hy
        have hyTail : y ∈ tail := by
          rw [← List.takeWhile_append_dropWhile (l := tail) (p := p)]
          exact List.mem_append_left _ hy
        exact mem_segment_of_mem_of_isTheta hgamma (by simp [hyTail])
      have hstopSegment : match (tail.dropWhile p).head? with
          | none => True
          | some y => y ∈ segment n := by
        cases hrest : tail.dropWhile p with
        | nil => simp [hrest]
        | cons y ys =>
            have hyTail : y ∈ tail := by
              rw [← List.takeWhile_append_dropWhile (l := tail) (p := p)]
              simp [hrest]
            have hyWord : y ∈ first :: tail := by simp [hyTail]
            simpa [hrest] using mem_segment_of_mem_of_isTheta hgamma hyWord
      have hpq : forall y : Nat, y ∈ tail.takeWhile p -> q y = true := by
        intro y hy
        have hpTrue : p y = true := List.mem_takeWhile_imp hy
        have hsame : SameHalf n first y := by simpa [p] using hpTrue
        rcases Nat.even_or_odd n with hnEven | hnOdd
        · simpa [q] using
            (sameHalf_complement_iff_of_even hnEven hfirstSegment
              (hprefixSegment y hy)).2 hsame
        · have hmiddleFirst : first ≠ (n + 1) / 2 := by
            intro hfirstMiddle
            apply hexception
            refine ⟨hnOdd, ?_⟩
            simp [prologue, hfirstMiddle]
          have hmiddleY : y ≠ (n + 1) / 2 := by
            intro hyMiddle
            apply hexception
            refine ⟨hnOdd, ?_⟩
            simp only [prologue, List.mem_cons]
            right
            exact hyMiddle ▸ hy
          simpa [q] using
            (sameHalf_complement_iff_of_odd_away_middle hnOdd hfirstSegment
              (hprefixSegment y hy) hmiddleFirst hmiddleY).2 hsame
      have hstop : match (tail.dropWhile p).head? with
          | none => True
          | some y => q y = false := by
        cases hrest : tail.dropWhile p with
        | nil => simp [hrest]
        | cons y ys =>
            have hpFalse : p y = false := by
              simpa [hrest] using List.head?_dropWhile_not p tail
            have hnotSame : ¬ SameHalf n first y := by
              simpa [p] using hpFalse
            have hySegment : y ∈ segment n := by
              simpa [hrest] using hstopSegment
            rcases Nat.even_or_odd n with hnEven | hnOdd
            · have hnotComplement :
                  ¬ SameHalf n (n + 1 - first) (n + 1 - y) := by
                simpa only [sameHalf_complement_iff_of_even hnEven hfirstSegment hySegment]
                  using hnotSame
              simpa [q, hrest] using hnotComplement
            · have hmiddleFirst : first ≠ (n + 1) / 2 := by
                intro hfirstMiddle
                apply hexception
                refine ⟨hnOdd, ?_⟩
                simp [prologue, hfirstMiddle]
              have hmiddleY : y ≠ (n + 1) / 2 := by
                intro hyMiddle
                have hmiddleStop := odd_middle_not_first_outside_half hnOdd hgamma
                exact hmiddleStop (by simpa [p, hrest, hyMiddle])
              have hnotComplement :
                  ¬ SameHalf n (n + 1 - first) (n + 1 - y) := by
                simpa only [sameHalf_complement_iff_of_odd_away_middle hnOdd hfirstSegment
                  hySegment hmiddleFirst hmiddleY] using hnotSame
              simpa [q, hrest] using hnotComplement
      have hlength := takeWhile_length_eq_of_prefix_and_stop hpq hstop
      simpa [prologue, complement, p, q, Function.comp_def, List.takeWhile_map]
        using hlength.symm

lemma sameHalf_even_values_iff (n x y : Nat) :
    SameHalf (2 * n) (2 * x) (2 * y) ↔ SameHalf n x y := by
  simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc]
  omega

lemma takeWhile_length_eq_prefix_of_append {p : Nat -> Bool}
    {xs pre rest : List Nat} (hxs : xs = pre ++ rest)
    (hprefix : forall x : Nat, x ∈ pre -> p x = true)
    (hstop : match rest.head? with
      | none => True
      | some x => p x = false) :
    (xs.takeWhile p).length = pre.length := by
  rw [hxs, List.takeWhile_append_of_pos]
  · cases hrest : rest with
    | nil => simp
    | cons x ys =>
        have hpx : p x = false := by simpa [hrest] using hstop
        simp [hpx]
  · intro x hx
    exact hprefix x hx

lemma prologue_doubledEvenOdd_length {n first : Nat} {tail : List Nat}
    (hgamma : IsTheta n (first :: tail)) :
    (prologue n (first :: tail)).length =
      (prologue (2 * n) (doubledEvenOdd (first :: tail))).length := by
  let p := fun y : Nat => decide (SameHalf n first y)
  let r := fun z : Nat => decide (SameHalf (2 * n) (2 * first) z)
  let pre := evenLift (tail.takeWhile p)
  let rest := evenLift (tail.dropWhile p) ++ oddLift (first :: tail)
  let deltaTail := evenLift tail ++ oddLift (first :: tail)
  have hdecomp : deltaTail = pre ++ rest := by
    dsimp only [deltaTail, pre, rest, evenLift]
    calc
      List.map (fun x => 2 * x) tail ++ oddLift (first :: tail) =
          List.map (fun x => 2 * x)
              (tail.takeWhile p ++ tail.dropWhile p) ++ oddLift (first :: tail) := by
            rw [List.takeWhile_append_dropWhile]
      _ = List.map (fun x => 2 * x) (tail.takeWhile p) ++
            (List.map (fun x => 2 * x) (tail.dropWhile p) ++
              oddLift (first :: tail)) := by
            simp only [List.map_append, List.append_assoc]
  have hprefix : forall z : Nat, z ∈ pre -> r z = true := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
    have hpTrue : p y = true := List.mem_takeWhile_imp hy
    have hsame : SameHalf n first y := by simpa [p] using hpTrue
    simpa [r] using (sameHalf_even_values_iff n first y).2 hsame
  have hstop : match rest.head? with
      | none => True
      | some z => r z = false := by
    cases hdrop : tail.dropWhile p with
    | cons y ys =>
        have hpFalse : p y = false := by
          simpa [hdrop] using List.head?_dropWhile_not p tail
        have hnotSame : ¬ SameHalf n first y := by simpa [p] using hpFalse
        have hnotLifted : ¬ SameHalf (2 * n) (2 * first) (2 * y) := by
          simpa only [sameHalf_even_values_iff] using hnotSame
        simpa [rest, evenLift, hdrop, r] using hnotLifted
    | nil =>
        have hall : forall y : Nat, y ∈ tail -> p y = true :=
          List.dropWhile_eq_nil_iff.mp hdrop
        have hfirstSegment : first ∈ segment n :=
          mem_segment_of_mem_of_isTheta hgamma (by simp)
        have hfirstBounds :=
          Finset.mem_Icc.mp (show first ∈ Finset.Icc 1 n from hfirstSegment)
        have hnOne : n = 1 := by
          by_contra hnNeOne
          have hnTwo : 2 <= n := by omega
          by_cases hfirstLower : first <= n / 2
          · have hnSegment : n ∈ segment n := by
              simp only [segment, Finset.mem_Icc]
              omega
            have hnWord := mem_of_mem_segment_of_isTheta hgamma hnSegment
            have hnTail : n ∈ tail := by
              simp only [List.mem_cons] at hnWord
              rcases hnWord with hnFirst | hnTail
              · omega
              · exact hnTail
            have hpN := hall n hnTail
            have hsame : SameHalf n first n := by simpa [p] using hpN
            simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hsame
            omega
          · have honeSegment : 1 ∈ segment n := by
              simp only [segment, Finset.mem_Icc]
              omega
            have honeWord := mem_of_mem_segment_of_isTheta hgamma honeSegment
            have honeTail : 1 ∈ tail := by
              simp only [List.mem_cons] at honeWord
              rcases honeWord with honeFirst | honeTail
              · omega
              · exact honeTail
            have hpOne := hall 1 honeTail
            have hsame : SameHalf n first 1 := by simpa [p] using hpOne
            simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hsame
            omega
        have hfirstOne : first = 1 := by omega
        subst n
        subst first
        simp [rest, evenLift, oddLift, hdrop, r, SameHalf, lowerHalf, upperHalf]
  have htake := takeWhile_length_eq_prefix_of_append hdecomp hprefix hstop
  have htake' : (tail.takeWhile p).length = (deltaTail.takeWhile r).length := by
    simpa [pre, evenLift] using htake.symm
  simpa [prologue, doubledEvenOdd, evenLift, oddLift, p, r, deltaTail]
    using congrArg Nat.succ htake'

/-- **Proposition 2.6.** The even-then-odd doubling construction preserves
both progression-freeness and prologue length; complementation preserves the
new prologue length as well. -/
theorem proposition_2_6_holds : proposition_2_6 := by
  intro n gamma hgamma
  let delta := doubledEvenOdd gamma
  have hdelta : IsTheta (2 * n) delta := by
    simpa [delta, doubledEvenOdd, evenLift, oddLift] using
      isTheta_evenOddLifts_even hgamma hgamma
  refine ⟨hdelta, ?_, ?_⟩
  · cases gamma with
    | nil => simp [prologue, delta, doubledEvenOdd]
    | cons first tail =>
        simpa [delta] using prologue_doubledEvenOdd_length (n := n) hgamma
  · exact proposition_2_5_holds (2 * n) delta hdelta (by simp)

lemma occursLeftOf_trans {word : List Nat} (hword : word.Nodup) {x y z : Nat}
    (hxy : OccursLeftOf word x y) (hyz : OccursLeftOf word y z) :
    OccursLeftOf word x z := by
  rcases hxy with ⟨i, j, hij, hi, hj⟩
  rcases hyz with ⟨j', k, hjk, hj', hk⟩
  have hjEq : j = j' := getElem?_index_unique_of_nodup hword hj hj'
  subst j'
  exact ⟨i, k, by omega, hi, hk⟩

lemma occursLeftOf_asymm {word : List Nat} (hword : word.Nodup) {x y : Nat}
    (hxy : OccursLeftOf word x y) : ¬ OccursLeftOf word y x := by
  intro hyx
  rcases hxy with ⟨i, j, hij, hi, hj⟩
  rcases hyx with ⟨j', i', hji, hj', hi'⟩
  have hjEq : j = j' := getElem?_index_unique_of_nodup hword hj hj'
  have hiEq : i = i' := getElem?_index_unique_of_nodup hword hi hi'
  omega

lemma alternating_stepTwo_pairs_backward {n a count : Nat} {word : List Nat}
    (hword : IsTheta n word)
    (hmem : forall i : Nat, i <= count + 1 -> a + 2 * i ∈ word)
    (hstart : OccursLeftOf word (a + 2) a) :
    forall i : Nat, i <= count ->
      (Even i -> OccursLeftOf word (a + 2 * (i + 1)) (a + 2 * i)) /\
      (Odd i -> OccursLeftOf word (a + 2 * i) (a + 2 * (i + 1))) := by
  intro i hi
  induction i with
  | zero =>
      constructor
      · intro _
        simpa using hstart
      · intro hzeroOdd
        norm_num at hzeroOdd
  | succ i ih =>
      have hiPrev : i <= count := by omega
      have hih := ih hiPrev
      have ha := hmem i (by omega)
      have hm := hmem (i + 1) (by omega)
      have hc := hmem (i + 2) (by omega)
      constructor
      · intro hsuccEven
        have hiOdd : Odd i := by grind
        have hleft := hih.2 hiOdd
        have hresult := right_endpoint_left_of_middle_of_left_endpoint hword
          (a := a + 2 * i) (d := 2) (by omega) ha (by convert hm using 1 <;> omega)
          (by convert hc using 1 <;> omega) (by convert hleft using 1 <;> omega)
        convert hresult using 1 <;> omega
      · intro hsuccOdd
        have hiEven : Even i := by grind
        have hmiddle := hih.1 hiEven
        have hresult := middle_left_of_right_endpoint_of_middle_left hword
          (a := a + 2 * i) (d := 2) (by omega) ha (by convert hm using 1 <;> omega)
          (by convert hc using 1 <;> omega) (by convert hmiddle using 1 <;> omega)
        convert hresult using 1 <;> omega

lemma alternating_stepTwo_pairs_forward {n a count : Nat} {word : List Nat}
    (hword : IsTheta n word)
    (hmem : forall i : Nat, i <= count + 1 -> a + 2 * i ∈ word)
    (hstart : OccursLeftOf word a (a + 2)) :
    forall i : Nat, i <= count ->
      (Even i -> OccursLeftOf word (a + 2 * i) (a + 2 * (i + 1))) /\
      (Odd i -> OccursLeftOf word (a + 2 * (i + 1)) (a + 2 * i)) := by
  intro i hi
  induction i with
  | zero =>
      constructor
      · intro _
        simpa using hstart
      · intro hzeroOdd
        norm_num at hzeroOdd
  | succ i ih =>
      have hiPrev : i <= count := by omega
      have hih := ih hiPrev
      have ha := hmem i (by omega)
      have hm := hmem (i + 1) (by omega)
      have hc := hmem (i + 2) (by omega)
      constructor
      · intro hsuccEven
        have hiOdd : Odd i := by grind
        have hmiddle := hih.2 hiOdd
        have hresult := middle_left_of_right_endpoint_of_middle_left hword
          (a := a + 2 * i) (d := 2) (by omega) ha (by convert hm using 1 <;> omega)
          (by convert hc using 1 <;> omega) (by convert hmiddle using 1 <;> omega)
        convert hresult using 1 <;> omega
      · intro hsuccOdd
        have hiEven : Even i := by grind
        have hleft := hih.1 hiEven
        have hresult := right_endpoint_left_of_middle_of_left_endpoint hword
          (a := a + 2 * i) (d := 2) (by omega) ha (by convert hm using 1 <;> omega)
          (by convert hc using 1 <;> omega) (by convert hleft using 1 <;> omega)
        convert hresult using 1 <;> omega

lemma odd_ordered_endpoints_left_of_even_mean {n : Nat} {word : List Nat}
    (hword12 : IsTheta12 n word) {x y m : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hmSegment : m ∈ segment n) (hxy : x < y)
    (hxOdd : Odd x) (hyOdd : Odd y) (hmEven : Even m)
    (hmean : x + y = 2 * m) :
    OccursLeftOf word x m /\ OccursLeftOf word y m := by
  generalize hd : Nat.dist x y = distance
  induction distance using Nat.strong_induction_on generalizing x y m with
  | h distance ih =>
      rcases hxOdd with ⟨a, ha⟩
      rcases hyOdd with ⟨b, hb⟩
      rcases hmEven with ⟨s, hs⟩
      let steps := b - a
      have hab : a < b := by omega
      have hstepsPos : 0 < steps := by simp [steps, hab]
      have hyAsSteps : y = x + 2 * steps := by
        dsimp [steps]
        omega
      have hstepsOdd : Odd steps := by
        refine ⟨s - a - 1, ?_⟩
        dsimp [steps]
        omega
      by_cases hstepsOne : steps = 1
      · have hmEq : m = x + 1 := by omega
        have hyEq : y = m + 1 := by omega
        have hxNextSegment : x + 1 ∈ segment n := by simpa [hmEq] using hmSegment
        have hmNextSegment : m + 1 ∈ segment n := by simpa [hyEq] using hySegment
        have hxOrientation := proposition_2_3_holds n word x hword12 hxSegment hxNextSegment
        have hmOrientation := proposition_2_3_holds n word m hword12 hmSegment hmNextSegment
        refine ⟨?_, ?_⟩
        · simpa [hmEq] using hxOrientation.1 (by exact ⟨a, ha⟩)
        · simpa [hyEq] using hmOrientation.2 (by exact ⟨s, hs⟩)
      · have hstepsThree : 3 <= steps := by grind
        have hinnerXSegment : x + 2 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
          omega
        have hinnerYSegment : y - 2 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
          omega
        have hinnerOrder : x + 2 < y - 2 := by omega
        have hinnerXOdd : Odd (x + 2) := by grind
        have hinnerYOdd : Odd (y - 2) := by grind
        have hinnerMean : x + 2 + (y - 2) = 2 * m := by omega
        have hinnerDist : Nat.dist (x + 2) (y - 2) < distance := by
          rw [Nat.dist_eq_sub_of_le hinnerOrder.le, ← hd,
            Nat.dist_eq_sub_of_le hxy.le]
          omega
        have hinner := ih (Nat.dist (x + 2) (y - 2)) hinnerDist
          hinnerXSegment hinnerYSegment hmSegment hinnerOrder hinnerXOdd hinnerYOdd
          (by exact ⟨s, hs⟩) hinnerMean rfl
        have hxMem := mem_of_mem_segment_of_isTheta hword12.1 hxSegment
        have hmMem := mem_of_mem_segment_of_isTheta hword12.1 hmSegment
        have hyMem := mem_of_mem_segment_of_isTheta hword12.1 hySegment
        let gap := m - x
        have hgapPos : 0 < gap := by
          dsimp [gap]
          omega
        have hmidEq : x + gap = m := by
          dsimp [gap]
          omega
        have hrightEq : x + 2 * gap = y := by
          dsimp [gap]
          omega
        rcases occursLeftOf_total_of_mem (isTheta_nodup hword12.1) hxMem hmMem
            (by omega) with hxm | hmx
        · have hym := right_endpoint_left_of_middle_of_left_endpoint hword12.1
            (a := x) (d := gap) hgapPos hxMem
            (by simpa [hmidEq] using hmMem) (by simpa [hrightEq] using hyMem)
            (by simpa [hmidEq] using hxm)
          exact ⟨hxm, by simpa [hmidEq, hrightEq] using hym⟩
        · have hmy := middle_left_of_right_endpoint_of_middle_left hword12.1
            (a := x) (d := gap) hgapPos hxMem
            (by simpa [hmidEq] using hmMem) (by simpa [hrightEq] using hyMem)
            (by simpa [hmidEq] using hmx)
          have hmy' : OccursLeftOf word m y := by
            simpa [hmidEq, hrightEq] using hmy
          have hstart : OccursLeftOf word (x + 2) x :=
            occursLeftOf_trans (isTheta_nodup hword12.1) hinner.1 hmx
          have hmemSteps : forall i : Nat, i <= (steps - 1) + 1 ->
              x + 2 * i ∈ word := by
            intro i hi
            apply mem_of_mem_segment_of_isTheta hword12.1
            simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
            omega
          have hlastPair := alternating_stepTwo_pairs_backward
            (n := n) (a := x) (count := steps - 1) hword12.1 hmemSteps hstart
            (steps - 1) (by omega)
          have hlastEven : Even (steps - 1) := by grind
          have hyBeforeInner : OccursLeftOf word y (y - 2) := by
            have := hlastPair.1 hlastEven
            convert this using 1 <;> omega
          have hinnerBeforeY : OccursLeftOf word (y - 2) y :=
            occursLeftOf_trans (isTheta_nodup hword12.1) hinner.2 hmy'
          exact False.elim ((occursLeftOf_asymm (isTheta_nodup hword12.1)
            hinnerBeforeY) hyBeforeInner)

lemma odd_endpoints_left_of_even_mean {n : Nat} {word : List Nat}
    (hword12 : IsTheta12 n word) {x y m : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hmSegment : m ∈ segment n) (hxyNe : x ≠ y)
    (hxOdd : Odd x) (hyOdd : Odd y) (hmEven : Even m)
    (hmean : x + y = 2 * m) :
    OccursLeftOf word x m /\ OccursLeftOf word y m := by
  rcases lt_or_gt_of_ne hxyNe with hxy | hyx
  · exact odd_ordered_endpoints_left_of_even_mean hword12 hxSegment hySegment
      hmSegment hxy hxOdd hyOdd hmEven hmean
  · have h := odd_ordered_endpoints_left_of_even_mean hword12 hySegment hxSegment
      hmSegment hyx hyOdd hxOdd hmEven (by omega)
    exact ⟨h.2, h.1⟩

lemma even_ordered_endpoints_right_of_odd_mean {n : Nat} {word : List Nat}
    (hword12 : IsTheta12 n word) {x y m : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hmSegment : m ∈ segment n) (hxy : x < y)
    (hxEven : Even x) (hyEven : Even y) (hmOdd : Odd m)
    (hmean : x + y = 2 * m) :
    OccursLeftOf word m x /\ OccursLeftOf word m y := by
  generalize hd : Nat.dist x y = distance
  induction distance using Nat.strong_induction_on generalizing x y m with
  | h distance ih =>
      rcases hxEven with ⟨a, ha⟩
      rcases hyEven with ⟨b, hb⟩
      rcases hmOdd with ⟨s, hs⟩
      let steps := b - a
      have hab : a < b := by omega
      have hstepsPos : 0 < steps := by simp [steps, hab]
      have hyAsSteps : y = x + 2 * steps := by
        dsimp [steps]
        omega
      have hstepsOdd : Odd steps := by
        refine ⟨s - a, ?_⟩
        dsimp [steps]
        omega
      by_cases hstepsOne : steps = 1
      · have hmEq : m = x + 1 := by omega
        have hyEq : y = m + 1 := by omega
        have hxNextSegment : x + 1 ∈ segment n := by simpa [hmEq] using hmSegment
        have hmNextSegment : m + 1 ∈ segment n := by simpa [hyEq] using hySegment
        have hxOrientation := proposition_2_3_holds n word x hword12 hxSegment hxNextSegment
        have hmOrientation := proposition_2_3_holds n word m hword12 hmSegment hmNextSegment
        refine ⟨?_, ?_⟩
        · simpa [hmEq] using hxOrientation.2 (by exact ⟨a, ha⟩)
        · simpa [hyEq] using hmOrientation.1 (by exact ⟨s, hs⟩)
      · have hstepsThree : 3 <= steps := by grind
        have hinnerXSegment : x + 2 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
          omega
        have hinnerYSegment : y - 2 ∈ segment n := by
          simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
          omega
        have hinnerOrder : x + 2 < y - 2 := by omega
        have hinnerXEven : Even (x + 2) := by grind
        have hinnerYEven : Even (y - 2) := by grind
        have hinnerMean : x + 2 + (y - 2) = 2 * m := by omega
        have hinnerDist : Nat.dist (x + 2) (y - 2) < distance := by
          rw [Nat.dist_eq_sub_of_le hinnerOrder.le, ← hd,
            Nat.dist_eq_sub_of_le hxy.le]
          omega
        have hinner := ih (Nat.dist (x + 2) (y - 2)) hinnerDist
          hinnerXSegment hinnerYSegment hmSegment hinnerOrder hinnerXEven hinnerYEven
          (by exact ⟨s, hs⟩) hinnerMean rfl
        have hxMem := mem_of_mem_segment_of_isTheta hword12.1 hxSegment
        have hmMem := mem_of_mem_segment_of_isTheta hword12.1 hmSegment
        have hyMem := mem_of_mem_segment_of_isTheta hword12.1 hySegment
        let gap := m - x
        have hgapPos : 0 < gap := by
          dsimp [gap]
          omega
        have hmidEq : x + gap = m := by
          dsimp [gap]
          omega
        have hrightEq : x + 2 * gap = y := by
          dsimp [gap]
          omega
        rcases occursLeftOf_total_of_mem (isTheta_nodup hword12.1) hxMem hmMem
            (by omega) with hxm | hmx
        · have hym := right_endpoint_left_of_middle_of_left_endpoint hword12.1
            (a := x) (d := gap) hgapPos hxMem
            (by simpa [hmidEq] using hmMem) (by simpa [hrightEq] using hyMem)
            (by simpa [hmidEq] using hxm)
          have hym' : OccursLeftOf word y m := by
            simpa [hmidEq, hrightEq] using hym
          have hstart : OccursLeftOf word x (x + 2) :=
            occursLeftOf_trans (isTheta_nodup hword12.1) hxm hinner.1
          have hmemSteps : forall i : Nat, i <= (steps - 1) + 1 ->
              x + 2 * i ∈ word := by
            intro i hi
            apply mem_of_mem_segment_of_isTheta hword12.1
            simp only [segment, Finset.mem_Icc] at hxSegment hySegment ⊢
            omega
          have hlastPair := alternating_stepTwo_pairs_forward
            (n := n) (a := x) (count := steps - 1) hword12.1 hmemSteps hstart
            (steps - 1) (by omega)
          have hlastEven : Even (steps - 1) := by grind
          have hinnerBeforeY : OccursLeftOf word (y - 2) y := by
            have := hlastPair.1 hlastEven
            convert this using 1 <;> omega
          have hyBeforeInner : OccursLeftOf word y (y - 2) :=
            occursLeftOf_trans (isTheta_nodup hword12.1) hym' hinner.2
          exact False.elim ((occursLeftOf_asymm (isTheta_nodup hword12.1)
            hinnerBeforeY) hyBeforeInner)
        · have hmy := middle_left_of_right_endpoint_of_middle_left hword12.1
            (a := x) (d := gap) hgapPos hxMem
            (by simpa [hmidEq] using hmMem) (by simpa [hrightEq] using hyMem)
            (by simpa [hmidEq] using hmx)
          exact ⟨hmx, by simpa [hmidEq, hrightEq] using hmy⟩

lemma even_endpoints_right_of_odd_mean {n : Nat} {word : List Nat}
    (hword12 : IsTheta12 n word) {x y m : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hmSegment : m ∈ segment n) (hxyNe : x ≠ y)
    (hxEven : Even x) (hyEven : Even y) (hmOdd : Odd m)
    (hmean : x + y = 2 * m) :
    OccursLeftOf word m x /\ OccursLeftOf word m y := by
  rcases lt_or_gt_of_ne hxyNe with hxy | hyx
  · exact even_ordered_endpoints_right_of_odd_mean hword12 hxSegment hySegment
      hmSegment hxy hxEven hyEven hmOdd hmean
  · have h := even_ordered_endpoints_right_of_odd_mean hword12 hySegment hxSegment
      hmSegment hyx hyEven hxEven hmOdd (by omega)
    exact ⟨h.2, h.1⟩

/-- **Theorem 2.1.** Same-parity endpoints lie on the side of their
opposite-parity mean forced by a `Theta_12` ordering. -/
theorem theorem_2_1_holds : theorem_2_1 := by
  intro n gamma hgamma x y m hxSegment hySegment hmSegment hxyNe hmean
  have hxyNe' : x ≠ y := by simpa using hxyNe
  constructor
  · rintro ⟨hxOdd, hyOdd, hmEven⟩
    exact odd_endpoints_left_of_even_mean hgamma hxSegment hySegment hmSegment
      hxyNe' hxOdd hyOdd hmEven hmean
  · rintro ⟨hxEven, hyEven, hmOdd⟩
    exact even_endpoints_right_of_odd_mean hgamma hxSegment hySegment hmSegment
      hxyNe' hxEven hyEven hmOdd hmean

/-! ## Adjacent transpositions -/

/-- The value transposition underlying `swapValues`. -/
def swapEntry (x y z : Nat) : Nat :=
  if z = x then y else if z = y then x else z

@[simp] lemma swapValues_eq_map_swapEntry (x y : Nat) (word : List Nat) :
    swapValues x y word = word.map (swapEntry x y) := by
  rfl

@[simp] lemma swapEntry_left {x y : Nat} (hxy : x ≠ y) :
    swapEntry x y x = y := by
  simp [swapEntry, hxy]

@[simp] lemma swapEntry_right {x y : Nat} (hxy : x ≠ y) :
    swapEntry x y y = x := by
  simp [swapEntry, hxy]

lemma swapEntry_involutive {x y : Nat} (hxy : x ≠ y) (z : Nat) :
    swapEntry x y (swapEntry x y z) = z := by
  by_cases hzx : z = x
  · subst z
    simp [hxy]
  · by_cases hzy : z = y
    · subst z
      simp [hxy]
    · simp [swapEntry, hzx, hzy, hxy]

lemma swapEntry_injective {x y : Nat} (hxy : x ≠ y) :
    Function.Injective (swapEntry x y) := by
  intro a b hab
  calc
    a = swapEntry x y (swapEntry x y a) := (swapEntry_involutive hxy a).symm
    _ = swapEntry x y (swapEntry x y b) := congrArg (swapEntry x y) hab
    _ = b := swapEntry_involutive hxy b

lemma mem_swapValues_iff {word : List Nat} {x y z : Nat}
    (hxy : x ≠ y) (hx : x ∈ word) (hy : y ∈ word) :
    z ∈ swapValues x y word ↔ z ∈ word := by
  simp only [swapValues_eq_map_swapEntry, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    by_cases hwx : w = x
    · simpa [hwx, hxy] using hy
    · by_cases hwy : w = y
      · simpa [hwy, hxy] using hx
      · simpa [swapEntry, hwx, hwy] using hw
  · intro hz
    by_cases hzx : z = x
    · subst z
      exact ⟨y, hy, by simp [hxy]⟩
    · by_cases hzy : z = y
      · subst z
        exact ⟨x, hx, by simp [hxy]⟩
      · exact ⟨z, hz, by simp [swapEntry, hzx, hzy]⟩

lemma permutes_swapValues {S : Finset Nat} {word : List Nat} {x y : Nat}
    (hword : Permutes S word) (hx : x ∈ word) (hy : y ∈ word) (hxy : x ≠ y) :
    Permutes S (swapValues x y word) := by
  constructor
  · simpa only [swapValues_eq_map_swapEntry] using
      hword.1.map (swapEntry_injective hxy)
  · apply Finset.ext
    intro z
    simp only [List.mem_toFinset, mem_swapValues_iff hxy hx hy]
    simpa only [List.mem_toFinset] using
      (show z ∈ word.toFinset ↔ z ∈ S by rw [hword.2])

lemma adjacent_occurs_right_iff {word : List Nat} (hword : word.Nodup)
    {x y z : Nat} (hxy : ImmediatelyLeftOf word x y)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    OccursLeftOf word x z ↔ OccursLeftOf word y z := by
  rcases hxy with ⟨i, hix, hiy⟩
  constructor
  · rintro ⟨i', k, hik, hix', hk⟩
    have hiEq : i' = i := getElem?_index_unique_of_nodup hword hix' hix
    subst i'
    have hkNe : k ≠ i + 1 := by
      intro hkEq
      subst k
      apply hzy
      exact Option.some.inj (hk.symm.trans hiy)
    exact ⟨i + 1, k, by omega, hiy, hk⟩
  · rintro ⟨i', k, hik, hiy', hk⟩
    have hiEq : i' = i + 1 := getElem?_index_unique_of_nodup hword hiy' hiy
    subst i'
    exact ⟨i, k, by omega, hix, hk⟩

lemma adjacent_occurs_left_iff {word : List Nat} (hword : word.Nodup)
    {x y z : Nat} (hxy : ImmediatelyLeftOf word x y)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    OccursLeftOf word z x ↔ OccursLeftOf word z y := by
  rcases hxy with ⟨i, hix, hiy⟩
  constructor
  · rintro ⟨k, i', hki, hk, hix'⟩
    have hiEq : i' = i := getElem?_index_unique_of_nodup hword hix' hix
    subst i'
    exact ⟨k, i + 1, by omega, hk, hiy⟩
  · rintro ⟨k, i', hki, hk, hiy'⟩
    have hiEq : i' = i + 1 := getElem?_index_unique_of_nodup hword hiy' hiy
    subst i'
    have hkNe : k ≠ i := by
      intro hkEq
      subst k
      apply hzx
      exact Option.some.inj (hk.symm.trans hix)
    exact ⟨k, i, by omega, hk, hix⟩

lemma occursLeftOf_swapValues_iff {word : List Nat} {x y u v : Nat}
    (hxy : x ≠ y) :
    OccursLeftOf (swapValues x y word) u v ↔
      OccursLeftOf word (swapEntry x y u) (swapEntry x y v) := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨u', hi', hu'⟩ :=
      exists_of_getElem?_map_eq_some (f := swapEntry x y) (by simpa using hi)
    obtain ⟨v', hj', hv'⟩ :=
      exists_of_getElem?_map_eq_some (f := swapEntry x y) (by simpa using hj)
    have huEq : u' = swapEntry x y u := by
      calc
        u' = swapEntry x y (swapEntry x y u') := (swapEntry_involutive hxy u').symm
        _ = swapEntry x y u := congrArg (swapEntry x y) hu'
    have hvEq : v' = swapEntry x y v := by
      calc
        v' = swapEntry x y (swapEntry x y v') := (swapEntry_involutive hxy v').symm
        _ = swapEntry x y v := congrArg (swapEntry x y) hv'
    exact ⟨i, j, hij, by simpa [huEq] using hi', by simpa [hvEq] using hj'⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨i, j, hij, ?_, ?_⟩
    · simp only [swapValues_eq_map_swapEntry, List.getElem?_map, hi,
        Option.map_some, swapEntry_involutive hxy]
    · simp only [swapValues_eq_map_swapEntry, List.getElem?_map, hj,
        Option.map_some, swapEntry_involutive hxy]

lemma occursLeftOf_swapValues_preserved {word : List Nat} (hword : word.Nodup)
    {x y u v : Nat} (hxyAdjacent : ImmediatelyLeftOf word x y) (hxy : x ≠ y)
    (huv : u ≠ v)
    (hnotPair : ¬ ((u = x /\ v = y) \/ (u = y /\ v = x))) :
    OccursLeftOf (swapValues x y word) u v ↔ OccursLeftOf word u v := by
  rw [occursLeftOf_swapValues_iff hxy]
  by_cases hux : u = x
  · subst u
    have hvx : v ≠ x := by omega
    have hvy : v ≠ y := by
      intro hvy
      exact hnotPair (Or.inl ⟨rfl, hvy⟩)
    have hadj := adjacent_occurs_right_iff hword hxyAdjacent hvx hvy
    simpa [swapEntry, hxy, hvx, hvy] using hadj.symm
  · by_cases huy : u = y
    · subst u
      have hvy : v ≠ y := by omega
      have hvx : v ≠ x := by
        intro hvx
        exact hnotPair (Or.inr ⟨rfl, hvx⟩)
      have hadj := adjacent_occurs_right_iff hword hxyAdjacent hvx hvy
      simpa [swapEntry, hxy, hxy.symm, hvx, hvy] using hadj
    · by_cases hvx : v = x
      · subst v
        have hadj := adjacent_occurs_left_iff hword hxyAdjacent hux huy
        simpa [swapEntry, hxy, hxy.symm, hux, huy] using hadj.symm
      · by_cases hvy : v = y
        · subst v
          have hadj := adjacent_occurs_left_iff hword hxyAdjacent hux huy
          simpa [swapEntry, hxy, hxy.symm, hux, huy] using hadj
        · simp [swapEntry, hux, huy, hvx, hvy]

lemma reflection_mem_of_threeAP_values {n a d x y : Nat}
    (hd : 0 < d) (hxOdd : Odd x) (hyEven : Even y)
    (ha : a ∈ segment n) (hm : a + d ∈ segment n)
    (hc : a + 2 * d ∈ segment n)
    (hxValues : x = a \/ x = a + d \/ x = a + 2 * d)
    (hyValues : y = a \/ y = a + d \/ y = a + 2 * d) :
    (y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n) := by
  rcases hxOdd with ⟨r, hr⟩
  rcases hyEven with ⟨s, hs⟩
  simp only [segment, Finset.mem_Icc] at ha hm hc ⊢
  rcases hxValues with rfl | rfl | rfl <;>
    rcases hyValues with rfl | rfl | rfl <;> omega

lemma containsThreeAP_of_occurs_increasing {word : List Nat} (hword : word.Nodup)
    {a d : Nat} (hd : 0 < d)
    (hleft : OccursLeftOf word a (a + d))
    (hright : OccursLeftOf word (a + d) (a + 2 * d)) :
    ContainsThreeAP word := by
  rcases hleft with ⟨i, j, hij, hi, hj⟩
  rcases hright with ⟨j', k, hjk, hj', hk⟩
  have hjEq : j = j' := getElem?_index_unique_of_nodup hword hj hj'
  subst j'
  exact containsThreeAP_of_increasing_positions hij hjk hd hi hj hk

lemma containsThreeAP_of_occurs_decreasing {word : List Nat} (hword : word.Nodup)
    {a d : Nat} (hd : 0 < d)
    (hright : OccursLeftOf word (a + 2 * d) (a + d))
    (hleft : OccursLeftOf word (a + d) a) :
    ContainsThreeAP word := by
  rcases hright with ⟨i, j, hij, hi, hj⟩
  rcases hleft with ⟨j', k, hjk, hj', hk⟩
  have hjEq : j = j' := getElem?_index_unique_of_nodup hword hj hj'
  subst j'
  exact containsThreeAP_of_decreasing_positions hij hjk hd hi hj hk

lemma isTheta_swapValues_of_no_reflections {n x y : Nat} {word : List Nat}
    (hword : IsTheta n word) (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hxOdd : Odd x) (hyEven : Even y) (hxyAdjacent : ImmediatelyLeftOf word x y)
    (hnoReflections : ¬ ((y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n))) :
    IsTheta n (swapValues x y word) := by
  have hxy : x ≠ y := by grind
  have hxMem := mem_of_mem_segment_of_isTheta hword hxSegment
  have hyMem := mem_of_mem_segment_of_isTheta hword hySegment
  have hperm := permutes_swapValues hword.1 hxMem hyMem hxy
  refine ⟨hperm, ?_⟩
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have hv0 : (swapValues x y word)[indices 0]? = some a := by
      simpa using hvalues (0 : Fin 3)
    have hv1 : (swapValues x y word)[indices 1]? = some (a + d) := by
      simpa using hvalues (1 : Fin 3)
    have hv2 : (swapValues x y word)[indices 2]? = some (a + 2 * d) := by
      simpa using hvalues (2 : Fin 3)
    have haSegment : a ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 0, hv0⟩
    have hmSegment : a + d ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 1, hv1⟩
    have hcSegment : a + 2 * d ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 2, hv2⟩
    by_cases hboth :
        (x = a \/ x = a + d \/ x = a + 2 * d) /\
          (y = a \/ y = a + d \/ y = a + 2 * d)
    · exact hnoReflections (reflection_mem_of_threeAP_values hd hxOdd hyEven
        haSegment hmSegment hcSegment hboth.1 hboth.2)
    · have hnotPair01 :
          ¬ ((a = x /\ a + d = y) \/ (a = y /\ a + d = x)) := by
        intro hp
        apply hboth
        rcases hp with ⟨hax, hmy⟩ | ⟨hay, hmx⟩
        · exact ⟨Or.inl hax.symm, Or.inr (Or.inl hmy.symm)⟩
        · exact ⟨Or.inr (Or.inl hmx.symm), Or.inl hay.symm⟩
      have hnotPair12 :
          ¬ ((a + d = x /\ a + 2 * d = y) \/
            (a + d = y /\ a + 2 * d = x)) := by
        intro hp
        apply hboth
        rcases hp with ⟨hmx, hcy⟩ | ⟨hmy, hcx⟩
        · exact ⟨Or.inr (Or.inl hmx.symm), Or.inr (Or.inr hcy.symm)⟩
        · exact ⟨Or.inr (Or.inr hcx.symm), Or.inr (Or.inl hmy.symm)⟩
      have h01Beta : OccursLeftOf (swapValues x y word) a (a + d) :=
        ⟨indices 0, indices 1, hindices (by decide), hv0, hv1⟩
      have h12Beta : OccursLeftOf (swapValues x y word) (a + d) (a + 2 * d) :=
        ⟨indices 1, indices 2, hindices (by decide), hv1, hv2⟩
      have h01 := (occursLeftOf_swapValues_preserved (isTheta_nodup hword)
        hxyAdjacent hxy (by omega) hnotPair01).mp h01Beta
      have h12 := (occursLeftOf_swapValues_preserved (isTheta_nodup hword)
        hxyAdjacent hxy (by omega) hnotPair12).mp h12Beta
      exact (isTheta_threeFree hword)
        (containsThreeAP_of_occurs_increasing (isTheta_nodup hword) hd h01 h12)
  · have hv2 : (swapValues x y word)[indices 0]? = some (a + 2 * d) := by
      simpa using hvalues (0 : Fin 3)
    have hv1 : (swapValues x y word)[indices 1]? = some (a + d) := by
      simpa using hvalues (1 : Fin 3)
    have hv0 : (swapValues x y word)[indices 2]? = some a := by
      simpa using hvalues (2 : Fin 3)
    have haSegment : a ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 2, hv0⟩
    have hmSegment : a + d ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 1, hv1⟩
    have hcSegment : a + 2 * d ∈ segment n := by
      rw [← hperm.2, List.mem_toFinset]
      exact List.mem_iff_getElem?.mpr ⟨indices 0, hv2⟩
    by_cases hboth :
        (x = a \/ x = a + d \/ x = a + 2 * d) /\
          (y = a \/ y = a + d \/ y = a + 2 * d)
    · exact hnoReflections (reflection_mem_of_threeAP_values hd hxOdd hyEven
        haSegment hmSegment hcSegment hboth.1 hboth.2)
    · have hnotPair01 :
          ¬ ((a = x /\ a + d = y) \/ (a = y /\ a + d = x)) := by
        intro hp
        apply hboth
        rcases hp with ⟨hax, hmy⟩ | ⟨hay, hmx⟩
        · exact ⟨Or.inl hax.symm, Or.inr (Or.inl hmy.symm)⟩
        · exact ⟨Or.inr (Or.inl hmx.symm), Or.inl hay.symm⟩
      have hnotPair12 :
          ¬ ((a + d = x /\ a + 2 * d = y) \/
            (a + d = y /\ a + 2 * d = x)) := by
        intro hp
        apply hboth
        rcases hp with ⟨hmx, hcy⟩ | ⟨hmy, hcx⟩
        · exact ⟨Or.inr (Or.inl hmx.symm), Or.inr (Or.inr hcy.symm)⟩
        · exact ⟨Or.inr (Or.inr hcx.symm), Or.inr (Or.inl hmy.symm)⟩
      have h21Beta : OccursLeftOf (swapValues x y word) (a + 2 * d) (a + d) :=
        ⟨indices 0, indices 1, hindices (by decide), hv2, hv1⟩
      have h10Beta : OccursLeftOf (swapValues x y word) (a + d) a :=
        ⟨indices 1, indices 2, hindices (by decide), hv1, hv0⟩
      have hnotPair21 :
          ¬ ((a + 2 * d = x /\ a + d = y) \/
            (a + 2 * d = y /\ a + d = x)) := by
        rintro (⟨hcx, hmy⟩ | ⟨hcy, hmx⟩)
        · exact hnotPair12 (Or.inr ⟨hmy, hcx⟩)
        · exact hnotPair12 (Or.inl ⟨hmx, hcy⟩)
      have hnotPair10 :
          ¬ ((a + d = x /\ a = y) \/ (a + d = y /\ a = x)) := by
        rintro (⟨hmx, hay⟩ | ⟨hmy, hax⟩)
        · exact hnotPair01 (Or.inr ⟨hay, hmx⟩)
        · exact hnotPair01 (Or.inl ⟨hax, hmy⟩)
      have h21 := (occursLeftOf_swapValues_preserved (isTheta_nodup hword)
        hxyAdjacent hxy (by omega) hnotPair21).mp h21Beta
      have h10 := (occursLeftOf_swapValues_preserved (isTheta_nodup hword)
        hxyAdjacent hxy (by omega) hnotPair10).mp h10Beta
      exact (isTheta_threeFree hword)
        (containsThreeAP_of_occurs_decreasing (isTheta_nodup hword) hd h21 h10)

lemma getElem?_original_of_reverse {word : List Nat} {i value : Nat}
    (h : word.reverse[i]? = some value) :
    word[word.length - 1 - i]? = some value := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  have hi' : i < word.length := by simpa using hi
  simpa only [List.getElem?_reverse hi'] using h

lemma threeFree_reverse {word : List Nat} (hword : ThreeFree word) :
    ThreeFree word.reverse := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0r := hvalues (0 : Fin 3)
    have h1r := hvalues (1 : Fin 3)
    have h2r := hvalues (2 : Fin 3)
    have h0 : word[word.length - 1 - indices 0]? = some a := by
      apply getElem?_original_of_reverse
      simpa using h0r
    have h1 : word[word.length - 1 - indices 1]? = some (a + d) := by
      apply getElem?_original_of_reverse
      simpa using h1r
    have h2 : word[word.length - 1 - indices 2]? = some (a + 2 * d) := by
      apply getElem?_original_of_reverse
      simpa using h2r
    obtain ⟨hi0, _⟩ := List.getElem?_eq_some_iff.mp h0r
    obtain ⟨hi1, _⟩ := List.getElem?_eq_some_iff.mp h1r
    obtain ⟨hi2, _⟩ := List.getElem?_eq_some_iff.mp h2r
    have hi0' : indices 0 < word.length := by simpa using hi0
    have hi1' : indices 1 < word.length := by simpa using hi1
    have hi2' : indices 2 < word.length := by simpa using hi2
    have hi01 : indices 0 < indices 1 := hindices (by decide)
    have hi12 : indices 1 < indices 2 := hindices (by decide)
    apply hword
    exact containsThreeAP_of_decreasing_positions (by omega) (by omega) hd h2 h1 h0
  · have h2r := hvalues (0 : Fin 3)
    have h1r := hvalues (1 : Fin 3)
    have h0r := hvalues (2 : Fin 3)
    have h2 : word[word.length - 1 - indices 0]? = some (a + 2 * d) := by
      apply getElem?_original_of_reverse
      simpa using h2r
    have h1 : word[word.length - 1 - indices 1]? = some (a + d) := by
      apply getElem?_original_of_reverse
      simpa using h1r
    have h0 : word[word.length - 1 - indices 2]? = some a := by
      apply getElem?_original_of_reverse
      simpa using h0r
    obtain ⟨hi0, _⟩ := List.getElem?_eq_some_iff.mp h2r
    obtain ⟨hi1, _⟩ := List.getElem?_eq_some_iff.mp h1r
    obtain ⟨hi2, _⟩ := List.getElem?_eq_some_iff.mp h0r
    have hi0' : indices 0 < word.length := by simpa using hi0
    have hi1' : indices 1 < word.length := by simpa using hi1
    have hi2' : indices 2 < word.length := by simpa using hi2
    have hi01 : indices 0 < indices 1 := hindices (by decide)
    have hi12 : indices 1 < indices 2 := hindices (by decide)
    apply hword
    exact containsThreeAP_of_increasing_positions (by omega) (by omega) hd h0 h1 h2

lemma isTheta_reversal {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    IsTheta n (reversal word) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [reversal] using hword.1.1
  · simpa [reversal, List.toFinset_reverse] using hword.1.2
  · simpa [reversal] using threeFree_reverse hword.2

lemma endsWith_reversal_of_startsWith {word : List Nat} {x : Nat}
    (h : StartsWith word x) : EndsWith (reversal word) x := by
  cases word with
  | nil => simp [StartsWith] at h
  | cons first tail =>
      have hfirst : first = x := by simpa [StartsWith] using h
      subst first
      simp [EndsWith, reversal]

lemma endsWith_oddLift {word : List Nat} {x : Nat} (h : EndsWith word x) :
    EndsWith (oddLift word) (2 * x - 1) := by
  simpa [EndsWith, oddLift] using congrArg (Option.map fun z => 2 * z - 1) h

lemma immediatelyLeftOf_append_of_ends_starts {left right : List Nat} {x y : Nat}
    (hx : EndsWith left x) (hy : StartsWith right y) :
    ImmediatelyLeftOf (left ++ right) x y := by
  have hleftPos : 0 < left.length := by
    cases left with
    | nil => simp [EndsWith] at hx
    | cons first tail => simp
  have hxAt : left[left.length - 1]? = some x := by
    rw [← List.getLast?_eq_getElem?]
    exact hx
  have hyAt : right[0]? = some y := by
    rw [← List.head?_eq_getElem?]
    exact hy
  refine ⟨left.length - 1, ?_, ?_⟩
  · rw [List.getElem?_append_left (by omega)]
    exact hxAt
  · have hindex : left.length - 1 + 1 = left.length := by omega
    rw [hindex, List.getElem?_append_right (by omega)]
    simpa using hyAt

lemma immediatelyLeftOf_occursLeftOf {word : List Nat} {x y : Nat}
    (h : ImmediatelyLeftOf word x y) : OccursLeftOf word x y := by
  rcases h with ⟨i, hi, hj⟩
  exact ⟨i, i + 1, by omega, hi, hj⟩

lemma startsOdd_oddEvenLifts {k : Nat} {oddWord evenWord : List Nat}
    (hodd : IsTheta k oddWord) (hk : 0 < k) :
    StartsOdd (oddLift oddWord ++ evenLift evenWord) := by
  have hne : oddWord ≠ [] := by
    intro hnil
    subst oddWord
    have := isTheta_length hodd
    simp at this
    omega
  let first := oddWord.head hne
  have hfirst : StartsWith oddWord first := List.head?_eq_some_head hne
  have hfirstAt : oddWord[0]? = some first := by
    rw [← List.head?_eq_getElem?]
    exact hfirst
  have hfirstMem : first ∈ oddWord := List.mem_iff_getElem?.mpr ⟨0, hfirstAt⟩
  have hfirstPos := positive_of_mem_of_isTheta hodd hfirstMem
  refine ⟨2 * first - 1, ?_, by grind⟩
  exact (startsWith_oddLift hfirst).append (right := evenLift evenWord)

lemma doNotCommute_of_reflection {n x y : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hxOdd : Odd x) (hyEven : Even y)
    (hreflection : (y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n)) :
    DoNotCommute n x y := by
  intro gamma hgamma
  rcases hreflection with ⟨hyx, hzSegment⟩ | ⟨hxy, hzSegment⟩
  · let z := 2 * x - y
    have hzEven : Even z := by
      rcases hxOdd with ⟨a, ha⟩
      rcases hyEven with ⟨b, hb⟩
      refine ⟨2 * a + 1 - b, ?_⟩
      dsimp [z]
      omega
    have hzyNe : z != y := by
      simp only [bne_iff_ne]
      grind
    have hzMean : z + y = 2 * x := by
      dsimp [z]
      omega
    have hforced := theorem_2_1_holds n gamma hgamma z y x hzSegment hySegment
      hxSegment hzyNe hzMean
    exact (hforced.2 ⟨hzEven, hyEven, hxOdd⟩).2
  · let z := 2 * y - x
    have hzOdd : Odd z := by
      rcases hxOdd with ⟨a, ha⟩
      rcases hyEven with ⟨b, hb⟩
      refine ⟨2 * b - a - 1, ?_⟩
      dsimp [z]
      omega
    have hxzNe : x != z := by
      simp only [bne_iff_ne]
      grind
    have hxMean : x + z = 2 * y := by
      dsimp [z]
      omega
    have hforced := theorem_2_1_holds n gamma hgamma x z y hxSegment hzSegment
      hySegment hxzNe hxMean
    exact (hforced.1 ⟨hxOdd, hzOdd, hyEven⟩).1

lemma exists_theta12_reverse_pair_of_no_reflections {n x y : Nat}
    (hn : 3 <= n) (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hxOdd : Odd x) (hyEven : Even y)
    (hnoReflections : ¬ ((y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n))) :
    exists beta : List Nat, IsTheta12 n beta /\ OccursLeftOf beta y x := by
  have hxOddCopy := hxOdd
  have hyEvenCopy := hyEven
  rcases hxOdd with ⟨a, ha⟩
  rcases hyEven with ⟨b, hb⟩
  let oddCount := (n + 1) / 2
  let evenCount := n / 2
  have haSegment : a + 1 ∈ segment oddCount := by
    simp only [segment, Finset.mem_Icc, oddCount]
    simp only [segment, Finset.mem_Icc] at hxSegment
    omega
  have hbSegment : b ∈ segment evenCount := by
    simp only [segment, Finset.mem_Icc, evenCount]
    simp only [segment, Finset.mem_Icc] at hySegment
    omega
  obtain ⟨oddStartWord, hoddStartTheta, hoddStarts⟩ :=
    proposition_2_4_holds oddCount (a + 1) haSegment
  obtain ⟨evenWord, hevenTheta, hevenStarts⟩ :=
    proposition_2_4_holds evenCount b hbSegment
  let oddWord := reversal oddStartWord
  have hoddTheta : IsTheta oddCount oddWord := by
    simpa [oddWord] using isTheta_reversal hoddStartTheta
  have hoddEndsBase : EndsWith oddWord (a + 1) := by
    simpa [oddWord] using endsWith_reversal_of_startsWith hoddStarts
  have hoddEnds : EndsWith (oddLift oddWord) x := by
    have h := endsWith_oddLift hoddEndsBase
    convert h using 1 <;> omega
  have hevenStartsLifted : StartsWith (evenLift evenWord) y := by
    have h := startsWith_evenLift hevenStarts
    convert h using 1 <;> omega
  let alpha := oddLift oddWord ++ evenLift evenWord
  have halphaTheta : IsTheta n alpha := by
    rcases Nat.even_or_odd n with hnEven | hnOdd
    · rcases hnEven with ⟨k, hk⟩
      have hnEq : n = 2 * k := by omega
      have hoddCountEq : oddCount = k := by
        dsimp [oddCount]
        omega
      have hevenCountEq : evenCount = k := by
        dsimp [evenCount]
        omega
      rw [hoddCountEq] at hoddTheta
      rw [hevenCountEq] at hevenTheta
      simpa [alpha, hnEq] using
        isTheta_oddEvenLifts_even hoddTheta hevenTheta
    · rcases hnOdd with ⟨k, hk⟩
      have hnEq : n = 2 * k + 1 := by omega
      have hoddCountEq : oddCount = k + 1 := by
        dsimp [oddCount]
        omega
      have hevenCountEq : evenCount = k := by
        dsimp [evenCount]
        omega
      rw [hoddCountEq] at hoddTheta
      rw [hevenCountEq] at hevenTheta
      simpa [alpha, hnEq] using
        isTheta_oddEvenLifts_odd hoddTheta hevenTheta
  have hoddCountPos : 0 < oddCount := by
    dsimp [oddCount]
    omega
  have halpha12 : IsTheta12 n alpha :=
    ⟨halphaTheta, startsOdd_oddEvenLifts hoddTheta hoddCountPos⟩
  have hxyAdjacent : ImmediatelyLeftOf alpha x y := by
    exact immediatelyLeftOf_append_of_ends_starts hoddEnds hevenStartsLifted
  let beta := swapValues x y alpha
  have hbetaTheta : IsTheta n beta := by
    simpa [beta] using isTheta_swapValues_of_no_reflections halphaTheta
      (by simpa only [segment, Finset.mem_Icc] using hxSegment)
      (by simpa only [segment, Finset.mem_Icc] using hySegment)
      hxOddCopy hyEvenCopy hxyAdjacent hnoReflections
  have hxy : x ≠ y := by grind
  have honeSegment : 1 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have htwoSegment : 2 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have halphaOneTwo : OccursLeftOf alpha 1 2 :=
    (proposition_2_3_holds n alpha 1 halpha12 honeSegment htwoSegment).1 (by norm_num)
  have hnotPairOneTwo :
      ¬ ((1 = x /\ 2 = y) \/ (1 = y /\ 2 = x)) := by
    rintro (⟨hxOne, hyTwo⟩ | ⟨hyOne, hxTwo⟩)
    · subst x
      subst y
      apply hnoReflections
      right
      constructor
      · omega
      · simp only [segment, Finset.mem_Icc]
        omega
    · rcases hyEvenCopy with ⟨c, hc⟩
      omega
  have hbetaOneTwo : OccursLeftOf beta 1 2 := by
    apply (occursLeftOf_swapValues_preserved (isTheta_nodup halphaTheta)
      hxyAdjacent hxy (by omega) hnotPairOneTwo).mpr
    exact halphaOneTwo
  have hbeta12 : IsTheta12 n beta := proposition_2_2_holds n beta hbetaTheta hbetaOneTwo
  have hxyOccurs := immediatelyLeftOf_occursLeftOf hxyAdjacent
  have hyxBeta : OccursLeftOf beta y x := by
    apply (occursLeftOf_swapValues_iff hxy).2
    simpa [swapEntry, hxy, hxy.symm] using hxyOccurs
  exact ⟨beta, hbeta12, hyxBeta⟩

/-- **Theorem 2.2.** For `n >= 3`, an odd/even pair has forced order
exactly when one of its two affine reflections remains in `[n]`. -/
theorem theorem_2_2_holds : theorem_2_2 := by
  intro n x y hn hxSegment hySegment hxOdd hyEven
  constructor
  · intro hdoNotCommute
    by_contra hnoReflections
    obtain ⟨beta, hbeta12, hyx⟩ := exists_theta12_reverse_pair_of_no_reflections
      hn hxSegment hySegment hxOdd hyEven hnoReflections
    have hxy := hdoNotCommute beta hbeta12
    exact (occursLeftOf_asymm (isTheta_nodup hbeta12.1) hxy) hyx
  · exact doNotCommute_of_reflection hxSegment hySegment hxOdd hyEven

lemma isTheta12_swapValues_of_no_reflections {n x y : Nat} {word : List Nat}
    (hn : 3 <= n) (hword12 : IsTheta12 n word)
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hxOdd : Odd x) (hyEven : Even y) (hxyAdjacent : ImmediatelyLeftOf word x y)
    (hnoReflections : ¬ ((y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n))) :
    IsTheta12 n (swapValues x y word) := by
  have htheta := isTheta_swapValues_of_no_reflections hword12.1 hxSegment hySegment
    hxOdd hyEven hxyAdjacent hnoReflections
  have hxy : x ≠ y := by grind
  have honeSegment : 1 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have htwoSegment : 2 ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have honeTwo : OccursLeftOf word 1 2 :=
    (proposition_2_3_holds n word 1 hword12 honeSegment htwoSegment).1 (by norm_num)
  have hnotPairOneTwo :
      ¬ ((1 = x /\ 2 = y) \/ (1 = y /\ 2 = x)) := by
    rintro (⟨hxOne, hyTwo⟩ | ⟨hyOne, hxTwo⟩)
    · subst x
      subst y
      apply hnoReflections
      right
      constructor
      · omega
      · simp only [segment, Finset.mem_Icc]
        omega
    · rcases hyEven with ⟨c, hc⟩
      omega
  have honeTwoSwap : OccursLeftOf (swapValues x y word) 1 2 := by
    apply (occursLeftOf_swapValues_preserved (isTheta_nodup hword12.1)
      hxyAdjacent hxy (by omega) hnotPairOneTwo).mpr
    exact honeTwo
  exact proposition_2_2_holds n (swapValues x y word) htheta honeTwoSwap

/-- **Proposition 2.7.** Swapping an adjacent commuting odd/even pair
preserves membership in `Theta_12`. -/
theorem proposition_2_7_holds : proposition_2_7 := by
  intro n x y alpha hxSegment hySegment hxOdd hyEven halpha12 hcommute hxyAdjacent
  by_cases hn : 3 <= n
  · have hnotDoNotCommute : ¬ DoNotCommute n x y := by
      intro hdoNotCommute
      rcases hcommute with ⟨gamma, hgamma12, hyx⟩
      have hxy := hdoNotCommute gamma hgamma12
      exact (occursLeftOf_asymm (isTheta_nodup hgamma12.1) hxy) hyx
    have hnoReflections : ¬ ((y <= 2 * x /\ 2 * x - y ∈ segment n) \/
        (x <= 2 * y /\ 2 * y - x ∈ segment n)) := by
      intro hreflection
      apply hnotDoNotCommute
      exact (theorem_2_2_holds n x y hn hxSegment hySegment hxOdd hyEven).2 hreflection
    exact isTheta12_swapValues_of_no_reflections hn halpha12 hxSegment hySegment
      hxOdd hyEven hxyAdjacent hnoReflections
  · have hnSmall : n <= 2 := by omega
    have hxBounds := Finset.mem_Icc.mp (show x ∈ Finset.Icc 1 n from hxSegment)
    have hyBounds := Finset.mem_Icc.mp (show y ∈ Finset.Icc 1 n from hySegment)
    have hxOne : x = 1 := by
      rcases hxOdd with ⟨a, ha⟩
      omega
    have hyTwo : y = 2 := by
      rcases hyEven with ⟨b, hb⟩
      omega
    subst x
    subst y
    rcases hcommute with ⟨gamma, hgamma12, htwoOne⟩
    have honeSegment : 1 ∈ segment n := by
      simp only [segment, Finset.mem_Icc]
      omega
    have htwoSegment : 2 ∈ segment n := by
      simp only [segment, Finset.mem_Icc]
      omega
    have honeTwo :=
      (proposition_2_3_holds n gamma 1 hgamma12 honeSegment htwoSegment).1 (by norm_num)
    exact False.elim ((occursLeftOf_asymm (isTheta_nodup hgamma12.1) honeTwo) htwoOne)

/-- **Corollary 2.2.1.** Opposite-parity entries in one half have their
order forced in every `Theta_12` word. -/
theorem corollary_2_2_1_holds : corollary_2_2_1 := by
  intro n x y hxSegment hySegment hsame
  have hreflections :
      (y <= 2 * x /\ 2 * x - y ∈ segment n) \/
        (x <= 2 * y /\ 2 * y - x ∈ segment n) := by
    simp only [segment, SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hxSegment hySegment hsame ⊢
    omega
  constructor
  · intro hxOdd hyEven
    by_cases hn : 3 <= n
    · exact (theorem_2_2_holds n x y hn hxSegment hySegment hxOdd hyEven).2
        hreflections
    · simp only [segment, SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hxSegment hySegment hsame
      rcases hxOdd with ⟨a, ha⟩
      rcases hyEven with ⟨b, hb⟩
      omega
  · intro hxEven hyOdd
    by_cases hn : 3 <= n
    · have hreflections' :
          (x <= 2 * y /\ 2 * y - x ∈ segment n) \/
            (y <= 2 * x /\ 2 * x - y ∈ segment n) := by
          rcases hreflections with hleft | hright
          · exact Or.inr hleft
          · exact Or.inl hright
      exact (theorem_2_2_holds n y x hn hySegment hxSegment hyOdd hxEven).2
        hreflections'
    · simp only [segment, SameHalf, lowerHalf, upperHalf, Finset.mem_Icc] at hxSegment hySegment hsame
      rcases hxEven with ⟨a, ha⟩
      rcases hyOdd with ⟨b, hb⟩
      omega

lemma index_lower_bound_of_occursLeftOf_family {word : List Nat} {k i y : Nat}
    (hword : word.Nodup) (hy : word[i]? = some y)
    (f : Fin k → Nat) (hf : Function.Injective f)
    (hbefore : forall t : Fin k, OccursLeftOf word (f t) y) :
    k <= i := by
  let position : Fin k → Fin i := fun t =>
    ⟨(hbefore t).choose, by
      rcases (hbefore t).choose_spec with ⟨j, hlt, _, hj⟩
      have hji := getElem?_index_unique_of_nodup hword hj hy
      omega⟩
  have hpositionValue (t : Fin k) :
      word[(position t : Nat)]? = some (f t) := by
    exact (hbefore t).choose_spec.choose_spec.2.1
  have hpositionInjective : Function.Injective position := by
    intro a b hab
    apply hf
    apply Option.some.inj
    calc
      some (f a) = word[(position a : Nat)]? := (hpositionValue a).symm
      _ = word[(position b : Nat)]? := by rw [hab]
      _ = some (f b) := hpositionValue b
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective position hpositionInjective

lemma startsWith_reversal_of_endsWith {word : List Nat} {x : Nat}
    (h : EndsWith word x) : StartsWith (reversal word) x := by
  simpa [StartsWith, EndsWith, reversal] using h

lemma occursLeftOf_of_occursLeftOf_reversal {word : List Nat} {x y : Nat}
    (h : OccursLeftOf (reversal word) x y) : OccursLeftOf word y x := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  have hi' : word[word.length - 1 - i]? = some x := by
    exact getElem?_original_of_reverse (by simpa [reversal] using hi)
  have hj' : word[word.length - 1 - j]? = some y := by
    exact getElem?_original_of_reverse (by simpa [reversal] using hj)
  obtain ⟨hiLen, _⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, _⟩ := List.getElem?_eq_some_iff.mp hj
  have hiBound : i < word.length := by simpa [reversal] using hiLen
  have hjBound : j < word.length := by simpa [reversal] using hjLen
  exact ⟨word.length - 1 - j, word.length - 1 - i, by omega, hj', hi'⟩

lemma quarter_le_index_of_even_of_isTheta12 {n : Nat} {word : List Nat}
    {i y : Nat} (hword : IsTheta12 n word) (hy : word[i]? = some y)
    (hyEven : Even y) :
    (n + 1) / 4 <= i := by
  have hyMem : y ∈ word := List.mem_iff_getElem?.mpr ⟨i, hy⟩
  have hySegment := mem_segment_of_mem_of_isTheta hword.1 hyMem
  by_cases hyLower : y ∈ lowerHalf n
  · let f : Fin ((n + 1) / 4) → Nat := fun t => 2 * (t : Nat) + 1
    apply index_lower_bound_of_occursLeftOf_family (isTheta_nodup hword.1) hy f
    · intro a b hab
      apply Fin.ext
      simp only [f] at hab
      omega
    · intro t
      have hfSegment : f t ∈ segment n := by
        simp only [f, segment, Finset.mem_Icc]
        omega
      have hfLower : f t ∈ lowerHalf n := by
        simp only [f, lowerHalf, Finset.mem_Icc]
        omega
      have hfOdd : Odd (f t) := by
        exact ⟨t, by simp [f, Nat.mul_comm]⟩
      exact (corollary_2_2_1_holds n (f t) y hfSegment hySegment
        (Or.inl ⟨hfLower, hyLower⟩)).1 hfOdd hyEven word hword
  · have hyUpper : y ∈ upperHalf n := by
      simp only [segment, lowerHalf, upperHalf, Finset.mem_Icc] at hySegment hyLower ⊢
      omega
    let f : Fin ((n + 1) / 4) → Nat := fun t =>
      2 * ((n + 1) / 2 - (n + 1) / 4 + (t : Nat)) + 1
    apply index_lower_bound_of_occursLeftOf_family (isTheta_nodup hword.1) hy f
    · intro a b hab
      apply Fin.ext
      simp only [f] at hab
      omega
    · intro t
      have hfSegment : f t ∈ segment n := by
        simp only [f, segment, Finset.mem_Icc]
        omega
      have hfUpper : f t ∈ upperHalf n := by
        simp only [f, upperHalf, Finset.mem_Icc]
        omega
      have hfOdd : Odd (f t) := by
        exact ⟨(n + 1) / 2 - (n + 1) / 4 + (t : Nat), by
          simp [f, Nat.mul_comm]⟩
      exact (corollary_2_2_1_holds n (f t) y hfSegment hySegment
        (Or.inr ⟨hfUpper, hyUpper⟩)).1 hfOdd hyEven word hword

lemma quarter_le_index_of_odd_of_isTheta21 {n : Nat} {word : List Nat}
    {i y : Nat} (hword : IsTheta21 n word) (hy : word[i]? = some y)
    (hyOdd : Odd y) :
    (n + 1) / 4 <= i := by
  by_cases hk : (n + 1) / 4 = 0
  · omega
  have hn : 3 <= n := by omega
  rcases hword.2 with ⟨first, hfirst, hfirstEven⟩
  obtain ⟨first', last, hfirst', hlast, hfirstLast⟩ :=
    proposition_2_1_holds n word (by omega) hword.1
  have hfirstEq : first' = first := by
    unfold StartsWith at hfirst hfirst'
    exact Option.some.inj (hfirst'.symm.trans hfirst)
  subst first'
  have hlastOdd : Odd last := by
    rcases Nat.even_or_odd last with hlastEven | hlastOdd
    · exact False.elim (hfirstLast (by
        rcases hfirstEven with ⟨a, ha⟩
        rcases hlastEven with ⟨b, hb⟩
        unfold Nat.ModEq
        omega))
    · exact hlastOdd
  have hreverse12 : IsTheta12 n (reversal word) :=
    ⟨isTheta_reversal hword.1,
      ⟨last, startsWith_reversal_of_endsWith hlast, hlastOdd⟩⟩
  have hyMem : y ∈ word := List.mem_iff_getElem?.mpr ⟨i, hy⟩
  have hySegment := mem_segment_of_mem_of_isTheta hword.1 hyMem
  by_cases hyLower : y ∈ lowerHalf n
  · let f : Fin ((n + 1) / 4) → Nat := fun t => 2 * ((t : Nat) + 1)
    apply index_lower_bound_of_occursLeftOf_family (isTheta_nodup hword.1) hy f
    · intro a b hab
      apply Fin.ext
      simp only [f] at hab
      omega
    · intro t
      have hfSegment : f t ∈ segment n := by
        simp only [f, segment, Finset.mem_Icc]
        omega
      have hfEven : Even (f t) := ⟨(t : Nat) + 1, by simp only [f]; omega⟩
      have hforced : DoNotCommute n y (f t) := by
        by_cases hfLower : f t ∈ lowerHalf n
        · exact (corollary_2_2_1_holds n y (f t) hySegment hfSegment
            (Or.inl ⟨hyLower, hfLower⟩)).1 hyOdd hfEven
        · apply (theorem_2_2_holds n y (f t) hn hySegment hfSegment hyOdd hfEven).2
          right
          simp only [f, segment, lowerHalf, Finset.mem_Icc] at hySegment hyLower hfLower ⊢
          rcases hyOdd with ⟨a, ha⟩
          omega
      exact occursLeftOf_of_occursLeftOf_reversal (hforced (reversal word) hreverse12)
  · have hyUpper : y ∈ upperHalf n := by
      simp only [segment, lowerHalf, upperHalf, Finset.mem_Icc] at hySegment hyLower ⊢
      omega
    let f : Fin ((n + 1) / 4) → Nat := fun t =>
      2 * (n / 2 - (n + 1) / 4 + (t : Nat) + 1)
    apply index_lower_bound_of_occursLeftOf_family (isTheta_nodup hword.1) hy f
    · intro a b hab
      apply Fin.ext
      simp only [f] at hab
      omega
    · intro t
      have hfSegment : f t ∈ segment n := by
        simp only [f, segment, Finset.mem_Icc]
        omega
      have hfUpper : f t ∈ upperHalf n := by
        simp only [f, upperHalf, Finset.mem_Icc]
        omega
      have hfEven : Even (f t) :=
        ⟨n / 2 - (n + 1) / 4 + (t : Nat) + 1, by simp only [f]; omega⟩
      have hforced := (corollary_2_2_1_holds n y (f t) hySegment hfSegment
        (Or.inr ⟨hyUpper, hfUpper⟩)).1 hyOdd hfEven
      exact occursLeftOf_of_occursLeftOf_reversal (hforced (reversal word) hreverse12)

/-- **Corollary 2.2.2.** The first quarter-block of every `Theta` word has a
single parity. -/
theorem corollary_2_2_2_holds : corollary_2_2_2 := by
  intro n word hword
  constructor
  · rw [isTheta_length hword]
    omega
  · intro i hi j hj x y hx hy
    have hne : word ≠ [] := by
      intro hnil
      subst word
      simp at hx
    let first := word.head hne
    have hfirst : StartsWith word first := List.head?_eq_some_head hne
    rcases Nat.even_or_odd first with hfirstEven | hfirstOdd
    · have hword21 : IsTheta21 n word := ⟨hword, ⟨first, hfirst, hfirstEven⟩⟩
      have hxEven : Even x := by
        rcases Nat.even_or_odd x with hxEven | hxOdd
        · exact hxEven
        · have := quarter_le_index_of_odd_of_isTheta21 hword21 hx hxOdd
          omega
      have hyEven : Even y := by
        rcases Nat.even_or_odd y with hyEven | hyOdd
        · exact hyEven
        · have := quarter_le_index_of_odd_of_isTheta21 hword21 hy hyOdd
          omega
      rcases hxEven with ⟨a, ha⟩
      rcases hyEven with ⟨b, hb⟩
      unfold Nat.ModEq
      omega
    · have hword12 : IsTheta12 n word := ⟨hword, ⟨first, hfirst, hfirstOdd⟩⟩
      have hxOdd : Odd x := by
        rcases Nat.even_or_odd x with hxEven | hxOdd
        · have := quarter_le_index_of_even_of_isTheta12 hword12 hx hxEven
          omega
        · exact hxOdd
      have hyOdd : Odd y := by
        rcases Nat.even_or_odd y with hyEven | hyOdd
        · have := quarter_le_index_of_even_of_isTheta12 hword12 hy hyEven
          omega
        · exact hyOdd
      rcases hxOdd with ⟨a, ha⟩
      rcases hyOdd with ⟨b, hb⟩
      unfold Nat.ModEq
      omega

/-! ## Normalized parity traces -/

/-- Divide the even trace by two, as in the proof of Lemma 2.1. -/
def evenBase (word : List Nat) : List Nat :=
  (evenTrace word).map fun x => x / 2

/-- Apply `x ↦ (x + 1) / 2` to the odd trace, as in Lemma 2.1. -/
def oddBase (word : List Nat) : List Nat :=
  (oddTrace word).map fun x => (x + 1) / 2

lemma threeFree_of_sublist {small large : List Nat} (hlarge : ThreeFree large)
    (hsub : small.Sublist large) : ThreeFree small := by
  intro hsmall
  obtain ⟨embedding, hembedding⟩ :=
    List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
  rcases hsmall with ⟨indices, hindices, a, d, hd, hvalues⟩
  apply hlarge
  refine ⟨fun t => embedding (indices t), embedding.strictMono.comp hindices,
    a, d, hd, ?_⟩
  rcases hvalues with hvalues | hvalues
  · left
    intro t
    rw [← hembedding]
    exact hvalues t
  · right
    intro t
    rw [← hembedding]
    exact hvalues t

lemma threeFree_of_evenLift_threeFree {word : List Nat}
    (hword : ThreeFree (evenLift word)) : ThreeFree word := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    apply hword
    refine containsThreeAP_of_increasing_positions (a := 2 * a) (d := 2 * d)
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) (by omega) ?_ ?_ ?_
    · simp only [evenLift, List.getElem?_map, h0, Option.map_some]
    · simp only [evenLift, List.getElem?_map, h1, Option.map_some]
      congr 2
      omega
    · simp only [evenLift, List.getElem?_map, h2, Option.map_some]
      congr 2
      omega
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    apply hword
    refine containsThreeAP_of_decreasing_positions (a := 2 * a) (d := 2 * d)
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) (by omega) ?_ ?_ ?_
    · simp only [evenLift, List.getElem?_map, h0, Option.map_some]
      congr 2
      omega
    · simp only [evenLift, List.getElem?_map, h1, Option.map_some]
      congr 2
      omega
    · simp only [evenLift, List.getElem?_map, h2, Option.map_some]

lemma threeFree_of_oddLift_threeFree {word : List Nat}
    (hword : ThreeFree (oddLift word))
    (hpositive : forall x : Nat, x ∈ word -> 0 < x) : ThreeFree word := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    have haPos : 0 < a := hpositive a (List.mem_iff_getElem?.mpr ⟨indices 0, h0⟩)
    apply hword
    refine containsThreeAP_of_increasing_positions (a := 2 * a - 1) (d := 2 * d)
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) (by omega) ?_ ?_ ?_
    · simp only [oddLift, List.getElem?_map, h0, Option.map_some]
    · simp only [oddLift, List.getElem?_map, h1, Option.map_some]
      congr 2
      omega
    · simp only [oddLift, List.getElem?_map, h2, Option.map_some]
      congr 2
      omega
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    have haPos : 0 < a := hpositive a (List.mem_iff_getElem?.mpr ⟨indices 2, h2⟩)
    apply hword
    refine containsThreeAP_of_decreasing_positions (a := 2 * a - 1) (d := 2 * d)
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) (by omega) ?_ ?_ ?_
    · simp only [oddLift, List.getElem?_map, h0, Option.map_some]
      congr 2
      omega
    · simp only [oddLift, List.getElem?_map, h1, Option.map_some]
      congr 2
      omega
    · simp only [oddLift, List.getElem?_map, h2, Option.map_some]

lemma evenLift_evenBase (word : List Nat) : evenLift (evenBase word) = evenTrace word := by
  simp only [evenLift, evenBase, List.map_map]
  have hmap :
      List.map ((fun x => 2 * x) ∘ fun x => x / 2) (evenTrace word) =
        List.map id (evenTrace word) := by
    apply List.map_congr_left
    intro x hx
    have hxEven : Even x := by
      exact of_decide_eq_true (List.mem_filter.mp hx).2
    exact Nat.two_mul_div_two_of_even hxEven
  simpa only [List.map_id] using hmap

lemma oddLift_oddBase (word : List Nat) : oddLift (oddBase word) = oddTrace word := by
  simp only [oddLift, oddBase, List.map_map]
  have hmap :
      List.map ((fun x => 2 * x - 1) ∘ fun x => (x + 1) / 2) (oddTrace word) =
        List.map id (oddTrace word) := by
    apply List.map_congr_left
    intro x hx
    have hxOdd : Odd x := by
      exact of_decide_eq_true (List.mem_filter.mp hx).2
    rcases hxOdd with ⟨a, ha⟩
    change 2 * ((x + 1) / 2) - 1 = x
    omega
  simpa only [List.map_id] using hmap

lemma evenBase_toFinset {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    (evenBase word).toFinset = segment (n / 2) := by
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset]
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨z, hz, hzx⟩
    have hzFilter := List.mem_filter.mp hz
    have hzEven : Even z := of_decide_eq_true hzFilter.2
    have hzSegment := mem_segment_of_mem_of_isTheta hword hzFilter.1
    simp only [segment, Finset.mem_Icc] at hzSegment ⊢
    rw [← hzx]
    rcases hzEven with ⟨a, ha⟩
    omega
  · intro hx
    have hxBounds : 1 <= x ∧ x <= n / 2 := by
      simpa only [segment, Finset.mem_Icc] using hx
    let z := 2 * x
    have hzSegment : z ∈ segment n := by
      simp only [z, segment, Finset.mem_Icc]
      omega
    have hzMem := mem_of_mem_segment_of_isTheta hword hzSegment
    have hzEven : Even z := ⟨x, by simp only [z]; omega⟩
    have hzTrace : z ∈ evenTrace word := by
      exact List.mem_filter.mpr ⟨hzMem, decide_eq_true hzEven⟩
    exact List.mem_map.mpr ⟨z, hzTrace, by simp [z]⟩

lemma oddBase_toFinset {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    (oddBase word).toFinset = segment ((n + 1) / 2) := by
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset]
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨z, hz, hzx⟩
    have hzFilter := List.mem_filter.mp hz
    have hzOdd : Odd z := of_decide_eq_true hzFilter.2
    have hzSegment := mem_segment_of_mem_of_isTheta hword hzFilter.1
    simp only [segment, Finset.mem_Icc] at hzSegment ⊢
    rw [← hzx]
    rcases hzOdd with ⟨a, ha⟩
    omega
  · intro hx
    have hxBounds : 1 <= x ∧ x <= (n + 1) / 2 := by
      simpa only [segment, Finset.mem_Icc] using hx
    let z := 2 * x - 1
    have hzSegment : z ∈ segment n := by
      simp only [z, segment, Finset.mem_Icc]
      omega
    have hzMem := mem_of_mem_segment_of_isTheta hword hzSegment
    have hzOdd : Odd z := ⟨x - 1, by simp only [z]; omega⟩
    have hzTrace : z ∈ oddTrace word := by
      exact List.mem_filter.mpr ⟨hzMem, decide_eq_true hzOdd⟩
    exact List.mem_map.mpr ⟨z, hzTrace, by simp only [z]; omega⟩

lemma isTheta_evenBase {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    IsTheta (n / 2) (evenBase word) := by
  refine ⟨⟨?_, evenBase_toFinset hword⟩, ?_⟩
  · have htrace : (evenTrace word).Nodup := (isTheta_nodup hword).filter _
    rw [← evenLift_evenBase] at htrace
    exact (List.nodup_map_iff (by intro x y hxy; simp only at hxy; omega)).mp htrace
  · apply threeFree_of_evenLift_threeFree
    rw [evenLift_evenBase]
    exact threeFree_of_sublist (isTheta_threeFree hword) List.filter_sublist

lemma isTheta_oddBase {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    IsTheta ((n + 1) / 2) (oddBase word) := by
  refine ⟨⟨?_, oddBase_toFinset hword⟩, ?_⟩
  · have htrace : (oddTrace word).Nodup := (isTheta_nodup hword).filter _
    rw [← oddLift_oddBase] at htrace
    exact (List.nodup_map_iff oddLiftValue_injective).mp htrace
  · apply threeFree_of_oddLift_threeFree
    · rw [oddLift_oddBase]
      exact threeFree_of_sublist (isTheta_threeFree hword) List.filter_sublist
    · intro x hx
      have hxSegment : x ∈ segment ((n + 1) / 2) := by
        rw [← oddBase_toFinset hword, List.mem_toFinset]
        exact hx
      have hxOne := (Finset.mem_Icc.mp
        (show x ∈ Finset.Icc 1 ((n + 1) / 2) from hxSegment)).1
      omega

lemma getElem?_filter_of_prefix {p : Nat → Bool} {word : List Nat}
    {k i x : Nat} (hk : k <= word.length)
    (hp : forall r, r < k -> forall z : Nat, word[r]? = some z -> p z = true)
    (hi : i < k) (hx : word[i]? = some x) :
    (word.filter p)[i]? = some x := by
  have hfilterTake : (word.take k).filter p = word.take k := by
    apply List.filter_eq_self.mpr
    intro z hz
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hz
    obtain ⟨hrLen, _⟩ := List.getElem?_eq_some_iff.mp hr
    have hrk : r < k := by
      simpa [List.length_take, hk] using hrLen
    have hrWord : word[r]? = some z := by
      simpa [List.getElem?_take, hrk] using hr
    exact hp r hrk z hrWord
  calc
    (word.filter p)[i]? =
        ((word.take k ++ word.drop k).filter p)[i]? := by
          rw [List.take_append_drop]
    _ = ((word.take k).filter p ++ (word.drop k).filter p)[i]? := by
          rw [List.filter_append]
    _ = ((word.take k).filter p)[i]? := by
          rw [List.getElem?_append_left]
          simpa [hfilterTake, List.length_take, hk] using hi
    _ = (word.take k)[i]? := by rw [hfilterTake]
    _ = word[i]? := by simp [List.getElem?_take, hi]
    _ = some x := hx

lemma prefixCongruent_even_of_base {word : List Nat} {k m first : Nat}
    (hk : 0 < k) (hfirst : StartsWith word first) (hfirstEven : Even first)
    (hparity : PrefixCongruent word k 2)
    (hbase : PrefixCongruent (evenBase word) k m) :
    PrefixCongruent word k (2 * m) := by
  have hfirstAt : word[0]? = some first := by
    rw [← List.head?_eq_getElem?]
    exact hfirst
  have hprefixEven : forall r, r < k -> forall z : Nat,
      word[r]? = some z -> Even z := by
    intro r hr z hz
    have hmod := hparity.2 0 hk r hr first z hfirstAt hz
    rcases Nat.even_or_odd z with hzEven | hzOdd
    · exact hzEven
    · exfalso
      rcases hfirstEven with ⟨a, ha⟩
      rcases hzOdd with ⟨b, hb⟩
      unfold Nat.ModEq at hmod
      omega
  refine ⟨hparity.1, ?_⟩
  intro i hi j hj x y hx hy
  have hxEven := hprefixEven i hi x hx
  have hyEven := hprefixEven j hj y hy
  have hxTrace : (evenTrace word)[i]? = some x := by
    exact getElem?_filter_of_prefix hparity.1
      (fun r hr z hz => decide_eq_true (hprefixEven r hr z hz)) hi hx
  have hyTrace : (evenTrace word)[j]? = some y := by
    exact getElem?_filter_of_prefix hparity.1
      (fun r hr z hz => decide_eq_true (hprefixEven r hr z hz)) hj hy
  have hxBase : (evenBase word)[i]? = some (x / 2) := by
    simp only [evenBase, List.getElem?_map, hxTrace, Option.map_some]
  have hyBase : (evenBase word)[j]? = some (y / 2) := by
    simp only [evenBase, List.getElem?_map, hyTrace, Option.map_some]
  have hmod := hbase.2 i hi j hj (x / 2) (y / 2) hxBase hyBase
  simpa [Nat.two_mul_div_two_of_even hxEven,
    Nat.two_mul_div_two_of_even hyEven] using hmod.mul_left' 2

lemma prefixCongruent_odd_of_base {word : List Nat} {k m first : Nat}
    (hk : 0 < k) (hfirst : StartsWith word first) (hfirstOdd : Odd first)
    (hparity : PrefixCongruent word k 2)
    (hbase : PrefixCongruent (oddBase word) k m) :
    PrefixCongruent word k (2 * m) := by
  have hfirstAt : word[0]? = some first := by
    rw [← List.head?_eq_getElem?]
    exact hfirst
  have hprefixOdd : forall r, r < k -> forall z : Nat,
      word[r]? = some z -> Odd z := by
    intro r hr z hz
    have hmod := hparity.2 0 hk r hr first z hfirstAt hz
    rcases Nat.even_or_odd z with hzEven | hzOdd
    · exfalso
      rcases hfirstOdd with ⟨a, ha⟩
      rcases hzEven with ⟨b, hb⟩
      unfold Nat.ModEq at hmod
      omega
    · exact hzOdd
  refine ⟨hparity.1, ?_⟩
  intro i hi j hj x y hx hy
  have hxOdd := hprefixOdd i hi x hx
  have hyOdd := hprefixOdd j hj y hy
  have hxTrace : (oddTrace word)[i]? = some x := by
    exact getElem?_filter_of_prefix hparity.1
      (fun r hr z hz => decide_eq_true (hprefixOdd r hr z hz)) hi hx
  have hyTrace : (oddTrace word)[j]? = some y := by
    exact getElem?_filter_of_prefix hparity.1
      (fun r hr z hz => decide_eq_true (hprefixOdd r hr z hz)) hj hy
  have hxBase : (oddBase word)[i]? = some ((x + 1) / 2) := by
    simp only [oddBase, List.getElem?_map, hxTrace, Option.map_some]
  have hyBase : (oddBase word)[j]? = some ((y + 1) / 2) := by
    simp only [oddBase, List.getElem?_map, hyTrace, Option.map_some]
  have hmod := hbase.2 i hi j hj ((x + 1) / 2) ((y + 1) / 2) hxBase hyBase
  have hscaled := hmod.mul_left' 2
  apply Nat.ModEq.add_left_cancel' 1
  rcases hxOdd with ⟨a, ha⟩
  rcases hyOdd with ⟨b, hb⟩
  convert hscaled using 1 <;> omega

lemma PrefixCongruent.mono {word : List Nat} {k K m : Nat}
    (h : PrefixCongruent word K m) (hk : k <= K) :
    PrefixCongruent word k m := by
  refine ⟨hk.trans h.1, ?_⟩
  intro i hi j hj x y hx hy
  exact h.2 i (hi.trans_le hk) j (hj.trans_le hk) x y hx hy

lemma prefixCongruent_double_step {N k j : Nat} {word : List Nat}
    (hk : 0 < k) (hkQuarter : k <= (N + 1) / 4) (hword : IsTheta N word)
    (hodd : PrefixCongruent (oddBase word) k (2 ^ j))
    (heven : PrefixCongruent (evenBase word) k (2 ^ j)) :
    PrefixCongruent word k (2 ^ (j + 1)) := by
  have hparity := PrefixCongruent.mono (corollary_2_2_2_holds N word hword) hkQuarter
  have hne : word ≠ [] := by
    intro hnil
    subst word
    simp [PrefixCongruent] at hparity
    omega
  let first := word.head hne
  have hfirst : StartsWith word first := List.head?_eq_some_head hne
  rcases Nat.even_or_odd first with hfirstEven | hfirstOdd
  · have hresult := prefixCongruent_even_of_base hk hfirst hfirstEven hparity heven
    simpa [pow_succ, Nat.mul_comm] using hresult
  · have hresult := prefixCongruent_odd_of_base hk hfirst hfirstOdd hparity hodd
    simpa [pow_succ, Nat.mul_comm] using hresult

/-- **Lemma 2.1.** Congruence of the normalized parity traces lifts through
doubling the ambient interval. -/
theorem lemma_2_1_holds : lemma_2_1 := by
  intro n k j hn hk hj hkBound hnCong hnOneCong
  constructor
  · intro word hword
    have hoddTheta : IsTheta n (oddBase word) := by
      have h := isTheta_oddBase hword
      convert h using 1 <;> omega
    have hevenTheta : IsTheta n (evenBase word) := by
      have h := isTheta_evenBase hword
      convert h using 1 <;> omega
    apply prefixCongruent_double_step hk (hword := hword)
    · omega
    · exact hnCong (oddBase word) hoddTheta
    · exact hnCong (evenBase word) hevenTheta
  · intro word hword
    have hoddTheta : IsTheta (n + 1) (oddBase word) := by
      have h := isTheta_oddBase hword
      convert h using 1 <;> omega
    have hevenTheta : IsTheta n (evenBase word) := by
      have h := isTheta_evenBase hword
      convert h using 1 <;> omega
    apply prefixCongruent_double_step hk (hword := hword)
    · omega
    · exact hnOneCong (oddBase word) hoddTheta
    · exact hnCong (evenBase word) hevenTheta

lemma prefixCongruent_zero (word : List Nat) (m : Nat) :
    PrefixCongruent word 0 m := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  omega

lemma two_mul_div_pow_succ (m j : Nat) :
    2 * m / 2 ^ (j + 1) = m / 2 ^ j := by
  rw [pow_succ]
  simpa [Nat.mul_comm] using
    Nat.mul_div_mul_right m (2 ^ j) (by norm_num : 0 < 2)

lemma two_mul_add_one_div_pow_succ (m j : Nat) :
    (2 * m + 1) / 2 ^ (j + 1) = m / 2 ^ j := by
  rw [pow_succ]
  have hp : 0 < 2 ^ j := pow_pos (by norm_num) _
  have hquot : (2 * m + 1) / (2 * 2 ^ j) = m / 2 ^ j := by
    apply Nat.div_eq_of_lt_le
    · have h := Nat.div_mul_le_self m (2 ^ j)
      nlinarith
    · have h := Nat.lt_mul_div_succ m hp
      nlinarith
  simpa [Nat.mul_comm] using hquot

/-- **Theorem 2.3.** Iterating Lemma 2.1 yields the forced initial
congruence block modulo every power of two. -/
theorem theorem_2_3_holds : theorem_2_3 := by
  intro n j hn
  induction j generalizing n with
  | zero =>
      intro word hword
      simpa using corollary_2_2_2_holds n word hword
  | succ j ih =>
      intro word hword
      rcases Nat.even_or_odd n with hnEven | hnOdd
      · rcases hnEven with ⟨m, hm⟩
        have hnEq : n = 2 * m := by omega
        rw [hnEq] at hn hword ⊢
        let k := ((m / 2 ^ j) + 1) / 4
        have htarget : ((2 * m / 2 ^ (j + 1)) + 1) / 4 = k := by
          simp only [two_mul_div_pow_succ, k]
        rw [htarget]
        by_cases hkZero : k = 0
        · simpa only [hkZero] using
            prefixCongruent_zero word (2 ^ (j + 1 + 1))
        · have hmPos : 0 < m := by omega
          have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
          have hkBound : 4 * k <= m + 1 := by
            have hmul := Nat.div_mul_le_self (m / 2 ^ j + 1) 4
            have hdiv := Nat.div_le_self m (2 ^ j)
            dsimp [k]
            omega
          have hmCong : forall gamma : List Nat, IsTheta m gamma ->
              PrefixCongruent gamma k (2 ^ (j + 1)) := by
            intro gamma hgamma
            simpa only [k] using ih m hmPos gamma hgamma
          have hmOneCong : forall gamma : List Nat, IsTheta (m + 1) gamma ->
              PrefixCongruent gamma k (2 ^ (j + 1)) := by
            intro gamma hgamma
            apply PrefixCongruent.mono (ih (m + 1) (by omega) gamma hgamma)
            have hdiv : m / 2 ^ j <= (m + 1) / 2 ^ j :=
              Nat.div_le_div_right (by omega)
            dsimp [k]
            omega
          exact (lemma_2_1_holds m k (j + 1) hmPos hkPos (by omega) hkBound
            hmCong hmOneCong).1 word hword
      · rcases hnOdd with ⟨m, hm⟩
        have hnEq : n = 2 * m + 1 := by omega
        rw [hnEq] at hn hword ⊢
        let k := ((m / 2 ^ j) + 1) / 4
        have htarget : (((2 * m + 1) / 2 ^ (j + 1)) + 1) / 4 = k := by
          simp only [two_mul_add_one_div_pow_succ, k]
        rw [htarget]
        by_cases hkZero : k = 0
        · simpa only [hkZero] using
            prefixCongruent_zero word (2 ^ (j + 1 + 1))
        · have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
          have hmPos : 0 < m := by
            by_contra hmZero
            have hmEq : m = 0 := Nat.eq_zero_of_not_pos hmZero
            subst m
            simp [k] at hkZero
          have hkBound : 4 * k <= m + 1 := by
            have hmul := Nat.div_mul_le_self (m / 2 ^ j + 1) 4
            have hdiv := Nat.div_le_self m (2 ^ j)
            dsimp [k]
            omega
          have hmCong : forall gamma : List Nat, IsTheta m gamma ->
              PrefixCongruent gamma k (2 ^ (j + 1)) := by
            intro gamma hgamma
            simpa only [k] using ih m hmPos gamma hgamma
          have hmOneCong : forall gamma : List Nat, IsTheta (m + 1) gamma ->
              PrefixCongruent gamma k (2 ^ (j + 1)) := by
            intro gamma hgamma
            apply PrefixCongruent.mono (ih (m + 1) (by omega) gamma hgamma)
            have hdiv : m / 2 ^ j <= (m + 1) / 2 ^ j :=
              Nat.div_le_div_right (by omega)
            dsimp [k]
            omega
          exact (lemma_2_1_holds m k (j + 1) hmPos hkPos (by omega) hkBound
            hmCong hmOneCong).2 word hword

lemma binaryCongruenceDegree_evenBase {a b : Nat} (ha : Even a) (hb : Even b) (hne : a != b) :
    binaryCongruenceDegree (a / 2) (b / 2) + 1 = binaryCongruenceDegree a b := by
  rcases ha with ⟨A, ha⟩
  rcases hb with ⟨B, hb⟩
  have hdist : Nat.dist (a / 2) (b / 2) = Nat.dist a b / 2 := by
    unfold Nat.dist
    omega
  have hne' : a ≠ b := by simpa using hne
  have hdistNe : Nat.dist a b ≠ 0 := by
    intro hzero
    apply hne'
    exact Nat.eq_of_dist_eq_zero hzero
  have hdvd : 2 ∣ Nat.dist a b := by
    unfold Nat.dist
    omega
  unfold binaryCongruenceDegree
  rw [hdist]
  rw [Nat.factorization_div hdvd]
  have htwo : (Nat.factorization 2) 2 = 1 := by norm_num
  change (Nat.dist a b).factorization 2 - (Nat.factorization 2) 2 + 1 =
    (Nat.dist a b).factorization 2
  rw [htwo]
  have hone : 1 <= (Nat.dist a b).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization hdistNe).mp hdvd
  omega

lemma binaryCongruenceDegree_oddBase {a b : Nat} (ha : Odd a) (hb : Odd b) (hne : a != b) :
    binaryCongruenceDegree ((a + 1) / 2) ((b + 1) / 2) + 1 =
      binaryCongruenceDegree a b := by
  rcases ha with ⟨A, ha⟩
  rcases hb with ⟨B, hb⟩
  have hdist : Nat.dist ((a + 1) / 2) ((b + 1) / 2) = Nat.dist a b / 2 := by
    unfold Nat.dist
    omega
  have hne' : a ≠ b := by simpa using hne
  have hdistNe : Nat.dist a b ≠ 0 := by
    intro hzero
    exact hne' (Nat.eq_of_dist_eq_zero hzero)
  have hdvd : 2 ∣ Nat.dist a b := by
    unfold Nat.dist
    omega
  unfold binaryCongruenceDegree
  rw [hdist, Nat.factorization_div hdvd]
  have htwo : (Nat.factorization 2) 2 = 1 := by norm_num
  change (Nat.dist a b).factorization 2 - (Nat.factorization 2) 2 + 1 =
    (Nat.dist a b).factorization 2
  rw [htwo]
  have hone : 1 <= (Nat.dist a b).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization hdistNe).mp hdvd
  omega

lemma occursLeftOf_map {word : List Nat} {x y : Nat} (f : Nat -> Nat)
    (h : OccursLeftOf word x y) : OccursLeftOf (word.map f) (f x) (f y) := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, by simp [hi], by simp [hj]⟩

lemma occursLeftOf_of_sublist {small large : List Nat} {x y : Nat}
    (hsub : small.Sublist large) (h : OccursLeftOf small x y) :
    OccursLeftOf large x y := by
  obtain ⟨embedding, hembedding⟩ :=
    List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
  rcases h with ⟨i, j, hij, hi, hj⟩
  refine ⟨embedding i, embedding j, embedding.strictMono hij, ?_, ?_⟩
  · rw [← hembedding]
    exact hi
  · rw [← hembedding]
    exact hj

lemma startsWith_evenBase {word : List Nat} {a : Nat}
    (h : StartsWith word a) (ha : Even a) : StartsWith (evenBase word) (a / 2) := by
  cases word with
  | nil => simp [StartsWith] at h
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using h
      subst first
      simp [StartsWith, evenBase, evenTrace, trace, decide_eq_true ha]

lemma startsWith_oddBase {word : List Nat} {a : Nat}
    (h : StartsWith word a) (ha : Odd a) : StartsWith (oddBase word) ((a + 1) / 2) := by
  cases word with
  | nil => simp [StartsWith] at h
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using h
      subst first
      simp [StartsWith, oddBase, oddTrace, trace, decide_eq_true ha]

lemma sameParity_of_binaryCongruenceDegree_pos {a b : Nat}
    (hpos : 0 < binaryCongruenceDegree a b) :
    (Even a /\ Even b) \/ (Odd a /\ Odd b) := by
  have hdvd : 2 ∣ Nat.dist a b := by
    apply Nat.dvd_of_factorization_pos
    simpa [binaryCongruenceDegree] using hpos.ne'
  rcases Nat.even_or_odd a with haEven | haOdd
  · rcases Nat.even_or_odd b with hbEven | hbOdd
    · exact Or.inl ⟨haEven, hbEven⟩
    · rcases haEven with ⟨A, ha⟩
      rcases hbOdd with ⟨B, hb⟩
      exfalso
      unfold Nat.dist at hdvd
      omega
  · rcases Nat.even_or_odd b with hbEven | hbOdd
    · rcases haOdd with ⟨A, ha⟩
      rcases hbEven with ⟨B, hb⟩
      exfalso
      unfold Nat.dist at hdvd
      omega
    · exact Or.inr ⟨haOdd, hbOdd⟩

lemma oppositeParity_of_binaryCongruenceDegree_zero {a b : Nat} (hne : a != b)
    (hzero : binaryCongruenceDegree a b = 0) :
    (Even a /\ Odd b) \/ (Odd a /\ Even b) := by
  have hne' : a ≠ b := by simpa using hne
  have hdistNe : Nat.dist a b ≠ 0 := fun h => hne' (Nat.eq_of_dist_eq_zero h)
  rcases Nat.even_or_odd a with haEven | haOdd
  · rcases Nat.even_or_odd b with hbEven | hbOdd
    · exfalso
      have hdvd : 2 ∣ Nat.dist a b := by
        rcases haEven with ⟨A, ha⟩
        rcases hbEven with ⟨B, hb⟩
        unfold Nat.dist
        omega
      have hpos : 1 <= (Nat.dist a b).factorization 2 :=
        (Nat.prime_two.dvd_iff_one_le_factorization hdistNe).mp hdvd
      simp [binaryCongruenceDegree] at hzero
      omega
    · exact Or.inl ⟨haEven, hbOdd⟩
  · rcases Nat.even_or_odd b with hbEven | hbOdd
    · exact Or.inr ⟨haOdd, hbEven⟩
    · exfalso
      have hdvd : 2 ∣ Nat.dist a b := by
        rcases haOdd with ⟨A, ha⟩
        rcases hbOdd with ⟨B, hb⟩
        unfold Nat.dist
        omega
      have hpos : 1 <= (Nat.dist a b).factorization 2 :=
        (Nat.prime_two.dvd_iff_one_le_factorization hdistNe).mp hdvd
      simp [binaryCongruenceDegree] at hzero
      omega

lemma occursLeftOf_of_evenBase {word : List Nat} {x y : Nat}
    (hx : Even x) (hy : Even y)
    (h : OccursLeftOf (evenBase word) (x / 2) (y / 2)) :
    OccursLeftOf word x y := by
  have hlift := occursLeftOf_map (fun z : Nat => 2 * z) h
  change OccursLeftOf (evenLift (evenBase word)) (2 * (x / 2)) (2 * (y / 2)) at hlift
  rw [evenLift_evenBase] at hlift
  have htrace : OccursLeftOf (evenTrace word) x y := by
    simpa [Nat.two_mul_div_two_of_even hx, Nat.two_mul_div_two_of_even hy] using hlift
  exact occursLeftOf_of_sublist List.filter_sublist htrace

lemma occursLeftOf_of_oddBase {word : List Nat} {x y : Nat}
    (hx : Odd x) (hy : Odd y)
    (h : OccursLeftOf (oddBase word) ((x + 1) / 2) ((y + 1) / 2)) :
    OccursLeftOf word x y := by
  have hlift := occursLeftOf_map (fun z : Nat => 2 * z - 1) h
  change OccursLeftOf (oddLift (oddBase word))
    (2 * ((x + 1) / 2) - 1) (2 * ((y + 1) / 2) - 1) at hlift
  rw [oddLift_oddBase] at hlift
  rcases hx with ⟨X, hx⟩
  rcases hy with ⟨Y, hy⟩
  have htrace : OccursLeftOf (oddTrace word) x y := by
    convert hlift using 1 <;> omega
  exact occursLeftOf_of_sublist List.filter_sublist htrace

lemma sameParity_endpoints_of_mean {x y z : Nat} (hmean : x + y = 2 * z) :
    (Even x /\ Even y) \/ (Odd x /\ Odd y) := by
  rcases Nat.even_or_odd x with hxEven | hxOdd
  · rcases Nat.even_or_odd y with hyEven | hyOdd
    · exact Or.inl ⟨hxEven, hyEven⟩
    · rcases hxEven with ⟨X, hx⟩
      rcases hyOdd with ⟨Y, hy⟩
      exfalso
      omega
  · rcases Nat.even_or_odd y with hyEven | hyOdd
    · rcases hxOdd with ⟨X, hx⟩
      rcases hyEven with ⟨Y, hy⟩
      exfalso
      omega
    · exact Or.inr ⟨hxOdd, hyOdd⟩

lemma evenHalf_mem_segment {n x : Nat} (hx : x ∈ segment n) (heven : Even x) :
    x / 2 ∈ segment (n / 2) := by
  simp only [segment, Finset.mem_Icc] at hx ⊢
  rcases heven with ⟨X, hX⟩
  omega

lemma oddHalf_mem_segment {n x : Nat} (hx : x ∈ segment n) (hodd : Odd x) :
    (x + 1) / 2 ∈ segment ((n + 1) / 2) := by
  simp only [segment, Finset.mem_Icc] at hx ⊢
  rcases hodd with ⟨X, hX⟩
  omega

lemma binaryCongruence_forcing (e : Nat) :
    forall (n : Nat) (gamma : List Nat) (a1 x y z : Nat),
      IsTheta n gamma -> StartsWith gamma a1 ->
      x ∈ segment n -> y ∈ segment n -> z ∈ segment n ->
      x + y = 2 * z -> a1 != z -> a1 != x ->
      binaryCongruenceDegree a1 x = e ->
      binaryCongruenceDegree a1 x < binaryCongruenceDegree a1 z ->
        OccursLeftOf gamma z x /\ OccursLeftOf gamma z y := by
  induction e with
  | zero =>
      intro n gamma a1 x y z htheta hstart hxSegment hySegment hzSegment
        hmean haz hax hdegree hlt
      have hax' : a1 ≠ x := by simpa using hax
      have haz' : a1 ≠ z := by simpa using haz
      have hxy : x ≠ y := by
        intro hxy
        have hxz : x = z := by omega
        subst z
        exact (Nat.lt_irrefl _ hlt)
      have hxz : x ≠ z := by
        intro hxz
        subst z
        have hyx : y = x := by omega
        exact hxy hyx.symm
      have hxyBool : x != y := by simpa using hxy
      have hsameAZ := sameParity_of_binaryCongruenceDegree_pos (a := a1) (b := z) (by omega)
      have hoppAX := oppositeParity_of_binaryCongruenceDegree_zero hax hdegree
      rcases hoppAX with ⟨haEven, hxOdd⟩ | ⟨haOdd, hxEven⟩
      · have hzEven : Even z := by
          rcases hsameAZ with hEven | hOdd
          · exact hEven.2
          · rcases haEven with ⟨A, ha⟩
            rcases hOdd.1 with ⟨B, hb⟩
            exfalso
            omega
        have hyOdd : Odd y := by
          rcases sameParity_endpoints_of_mean hmean with hEven | hOdd
          · rcases hxOdd with ⟨X, hx⟩
            rcases hEven.1 with ⟨Y, hy⟩
            exfalso
            omega
          · exact hOdd.2
        have hnTwo : 2 <= n := by
          simp only [segment, Finset.mem_Icc] at hxSegment hzSegment
          omega
        obtain ⟨first, last, hfirst, hlast, hparity⟩ :=
          proposition_2_1_holds n gamma hnTwo htheta
        have hfirstEq : first = a1 := by
          unfold StartsWith at hfirst hstart
          exact Option.some.inj (hfirst.symm.trans hstart)
        subst first
        have hlastOdd : Odd last := by
          rcases Nat.even_or_odd last with hlastEven | hlastOdd
          · exfalso
            apply hparity
            rcases haEven with ⟨A, ha⟩
            rcases hlastEven with ⟨B, hb⟩
            unfold Nat.ModEq
            omega
          · exact hlastOdd
        have hreverse12 : IsTheta12 n (reversal gamma) :=
          ⟨isTheta_reversal htheta,
            ⟨last, startsWith_reversal_of_endsWith hlast, hlastOdd⟩⟩
        have hforced := (theorem_2_1_holds n (reversal gamma) hreverse12
          x y z hxSegment hySegment hzSegment hxyBool hmean).1
          ⟨hxOdd, hyOdd, hzEven⟩
        exact ⟨occursLeftOf_of_occursLeftOf_reversal hforced.1,
          occursLeftOf_of_occursLeftOf_reversal hforced.2⟩
      · have hzOdd : Odd z := by
          rcases hsameAZ with hEven | hOdd
          · rcases haOdd with ⟨A, ha⟩
            rcases hEven.1 with ⟨B, hb⟩
            exfalso
            omega
          · exact hOdd.2
        have hyEven : Even y := by
          rcases sameParity_endpoints_of_mean hmean with hEven | hOdd
          · exact hEven.2
          · rcases hxEven with ⟨X, hx⟩
            rcases hOdd.1 with ⟨Y, hy⟩
            exfalso
            omega
        have htheta12 : IsTheta12 n gamma := ⟨htheta, ⟨a1, hstart, haOdd⟩⟩
        exact (theorem_2_1_holds n gamma htheta12 x y z hxSegment hySegment
          hzSegment hxyBool hmean).2 ⟨hxEven, hyEven, hzOdd⟩
  | succ e ih =>
      intro n gamma a1 x y z htheta hstart hxSegment hySegment hzSegment
        hmean haz hax hdegree hlt
      have hsameAX := sameParity_of_binaryCongruenceDegree_pos (a := a1) (b := x) (by omega)
      have hsameAZ := sameParity_of_binaryCongruenceDegree_pos (a := a1) (b := z) (by omega)
      rcases hsameAX with ⟨haEven, hxEven⟩ | ⟨haOdd, hxOdd⟩
      · have hzEven : Even z := by
          rcases hsameAZ with hEven | hOdd
          · exact hEven.2
          · rcases haEven with ⟨A, ha⟩
            rcases hOdd.1 with ⟨B, hb⟩
            exfalso
            omega
        have hyEven : Even y := by
          rcases sameParity_endpoints_of_mean hmean with hEven | hOdd
          · exact hEven.2
          · rcases hxEven with ⟨X, hx⟩
            rcases hOdd.1 with ⟨Y, hy⟩
            exfalso
            omega
        have hthetaBase := isTheta_evenBase htheta
        have hstartBase := startsWith_evenBase hstart haEven
        have hxBase := evenHalf_mem_segment hxSegment hxEven
        have hyBase := evenHalf_mem_segment hySegment hyEven
        have hzBase := evenHalf_mem_segment hzSegment hzEven
        have hmeanBase : x / 2 + y / 2 = 2 * (z / 2) := by
          rcases hxEven with ⟨X, hx⟩
          rcases hyEven with ⟨Y, hy⟩
          rcases hzEven with ⟨Z, hz⟩
          omega
        have hazBase : a1 / 2 != z / 2 := by
          have haz' : a1 ≠ z := by simpa using haz
          have : a1 / 2 ≠ z / 2 := by
            intro h
            rcases haEven with ⟨A, ha⟩
            rcases hzEven with ⟨Z, hz⟩
            exact haz' (by omega)
          simpa using this
        have haxBase : a1 / 2 != x / 2 := by
          have hax' : a1 ≠ x := by simpa using hax
          have : a1 / 2 ≠ x / 2 := by
            intro h
            rcases haEven with ⟨A, ha⟩
            rcases hxEven with ⟨X, hx⟩
            exact hax' (by omega)
          simpa using this
        have hdegreeX := binaryCongruenceDegree_evenBase haEven hxEven hax
        have hdegreeZ := binaryCongruenceDegree_evenBase haEven hzEven haz
        have hdegreeBase : binaryCongruenceDegree (a1 / 2) (x / 2) = e := by
          omega
        have hltBase : binaryCongruenceDegree (a1 / 2) (x / 2) <
            binaryCongruenceDegree (a1 / 2) (z / 2) := by omega
        have hforced := ih (n / 2) (evenBase gamma) (a1 / 2) (x / 2) (y / 2)
          (z / 2) hthetaBase hstartBase hxBase hyBase hzBase hmeanBase hazBase
          haxBase hdegreeBase hltBase
        exact ⟨occursLeftOf_of_evenBase hzEven hxEven hforced.1,
          occursLeftOf_of_evenBase hzEven hyEven hforced.2⟩
      · have hzOdd : Odd z := by
          rcases hsameAZ with hEven | hOdd
          · rcases haOdd with ⟨A, ha⟩
            rcases hEven.1 with ⟨B, hb⟩
            exfalso
            omega
          · exact hOdd.2
        have hyOdd : Odd y := by
          rcases sameParity_endpoints_of_mean hmean with hEven | hOdd
          · rcases hxOdd with ⟨X, hx⟩
            rcases hEven.1 with ⟨Y, hy⟩
            exfalso
            omega
          · exact hOdd.2
        have hthetaBase := isTheta_oddBase htheta
        have hstartBase := startsWith_oddBase hstart haOdd
        have hxBase := oddHalf_mem_segment hxSegment hxOdd
        have hyBase := oddHalf_mem_segment hySegment hyOdd
        have hzBase := oddHalf_mem_segment hzSegment hzOdd
        have hmeanBase : (x + 1) / 2 + (y + 1) / 2 = 2 * ((z + 1) / 2) := by
          rcases hxOdd with ⟨X, hx⟩
          rcases hyOdd with ⟨Y, hy⟩
          rcases hzOdd with ⟨Z, hz⟩
          omega
        have hazBase : (a1 + 1) / 2 != (z + 1) / 2 := by
          have haz' : a1 ≠ z := by simpa using haz
          have : (a1 + 1) / 2 ≠ (z + 1) / 2 := by
            intro h
            rcases haOdd with ⟨A, ha⟩
            rcases hzOdd with ⟨Z, hz⟩
            exact haz' (by omega)
          simpa using this
        have haxBase : (a1 + 1) / 2 != (x + 1) / 2 := by
          have hax' : a1 ≠ x := by simpa using hax
          have : (a1 + 1) / 2 ≠ (x + 1) / 2 := by
            intro h
            rcases haOdd with ⟨A, ha⟩
            rcases hxOdd with ⟨X, hx⟩
            exact hax' (by omega)
          simpa using this
        have hdegreeX := binaryCongruenceDegree_oddBase haOdd hxOdd hax
        have hdegreeZ := binaryCongruenceDegree_oddBase haOdd hzOdd haz
        have hdegreeBase : binaryCongruenceDegree ((a1 + 1) / 2) ((x + 1) / 2) = e := by
          omega
        have hltBase : binaryCongruenceDegree ((a1 + 1) / 2) ((x + 1) / 2) <
            binaryCongruenceDegree ((a1 + 1) / 2) ((z + 1) / 2) := by omega
        have hforced := ih ((n + 1) / 2) (oddBase gamma) ((a1 + 1) / 2)
          ((x + 1) / 2) ((y + 1) / 2) ((z + 1) / 2) hthetaBase hstartBase
          hxBase hyBase hzBase hmeanBase hazBase haxBase hdegreeBase hltBase
        exact ⟨occursLeftOf_of_oddBase hzOdd hxOdd hforced.1,
          occursLeftOf_of_oddBase hzOdd hyOdd hforced.2⟩

theorem theorem_2_4_holds : theorem_2_4 := by
  intro n gamma a1 x y z htheta hstart hx hy hz hmean haz hax hlt
  exact binaryCongruence_forcing (binaryCongruenceDegree a1 x) n gamma a1 x y z
    htheta hstart hx hy hz hmean haz hax rfl hlt

lemma prefixCongruent_evenLift_of_base {word : List Nat} {k m : Nat}
    (h : PrefixCongruent word k m) :
    PrefixCongruent (evenLift word) k (2 * m) := by
  refine ⟨by simpa [evenLift] using h.1, ?_⟩
  intro i hi j hj x y hx hy
  obtain ⟨a, ha, hax⟩ := exists_of_getElem?_map_eq_some hx
  obtain ⟨b, hb, hby⟩ := exists_of_getElem?_map_eq_some hy
  have hab := h.2 i hi j hj a b ha hb
  subst x
  subst y
  exact hab.mul_left' 2

lemma prefixCongruent_oddLift_of_base {word : List Nat} {k m : Nat}
    (hpositive : forall x : Nat, x ∈ word -> 0 < x)
    (h : PrefixCongruent word k m) :
    PrefixCongruent (oddLift word) k (2 * m) := by
  refine ⟨by simpa [oddLift] using h.1, ?_⟩
  intro i hi j hj x y hx hy
  obtain ⟨a, ha, hax⟩ := exists_of_getElem?_map_eq_some hx
  obtain ⟨b, hb, hby⟩ := exists_of_getElem?_map_eq_some hy
  have haPos := hpositive a (List.mem_iff_getElem?.mpr ⟨i, ha⟩)
  have hbPos := hpositive b (List.mem_iff_getElem?.mpr ⟨j, hb⟩)
  have hab := h.2 i hi j hj a b ha hb
  have hscaled := hab.mul_left' 2
  rw [← hax, ← hby]
  apply Nat.ModEq.add_left_cancel' 1
  convert hscaled using 1 <;> omega

lemma forcedPrefixCongruent {N j k r : Nat} {word : List Nat}
    (hN : 0 < N) (hword : IsTheta N word)
    (hdenom : r * 2 ^ j <= N) (hk : 4 * k <= r + 1) :
    PrefixCongruent word k (2 ^ (j + 1)) := by
  apply PrefixCongruent.mono (theorem_2_3_holds N j hN word hword)
  have hquot : r <= N / 2 ^ j := by
    exact (Nat.le_div_iff_mul_le (pow_pos (by norm_num) j)).2 hdenom
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by omega)

lemma forcedEvenTracePrefixCongruent {N j k r : Nat} {word : List Nat}
    (hEvenN : 0 < N / 2) (hword : IsTheta N word)
    (hdenom : r * 2 ^ j <= N / 2) (hk : 4 * k <= r + 1) :
    PrefixCongruent (evenTrace word) k (2 * 2 ^ (j + 1)) := by
  have hbase := forcedPrefixCongruent (word := evenBase word)
    (N := N / 2) (j := j) (r := r) hEvenN (isTheta_evenBase hword) hdenom hk
  have hlift := prefixCongruent_evenLift_of_base hbase
  rw [evenLift_evenBase] at hlift
  exact hlift

lemma forcedOddTracePrefixCongruent {N j k r : Nat} {word : List Nat}
    (hN : 0 < N) (hword : IsTheta N word)
    (hdenom : r * 2 ^ j <= (N + 1) / 2) (hk : 4 * k <= r + 1) :
    PrefixCongruent (oddTrace word) k (2 * 2 ^ (j + 1)) := by
  have hbaseTheta := isTheta_oddBase hword
  have hbase := forcedPrefixCongruent (word := oddBase word)
    (N := (N + 1) / 2) (j := j) (r := r) (by omega) hbaseTheta hdenom hk
  have hpositive : forall x : Nat, x ∈ oddBase word -> 0 < x := by
    intro x hx
    exact positive_of_mem_of_isTheta hbaseTheta hx
  have hlift := prefixCongruent_oddLift_of_base hpositive hbase
  rw [oddLift_oddBase] at hlift
  exact hlift

lemma log_two_five_le {n : Nat} (hn : 32 <= n) : 5 <= Nat.log 2 n := by
  rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
  norm_num
  exact hn

lemma dyadicQ_pos (n : Nat) : 0 < dyadicQ n := by
  exact pow_pos (by norm_num) _

lemma dyadic_modulus_two {n : Nat} (hn : 32 <= n) :
    2 ^ ((Nat.log 2 n - 4) + 1) = 2 * dyadicQ n := by
  have hlog := log_two_five_le hn
  have hexponent : Nat.log 2 n - 3 = (Nat.log 2 n - 4) + 1 := by omega
  rw [← hexponent, show Nat.log 2 n - 3 = (Nat.log 2 n - 4) + 1 by omega,
    pow_add]
  simp [dyadicQ, Nat.mul_comm]

lemma dyadic_modulus_four {n : Nat} (hn : 32 <= n) :
    2 ^ ((Nat.log 2 n - 3) + 1) = 4 * dyadicQ n := by
  have hlog := log_two_five_le hn
  have hexponent : Nat.log 2 n - 2 = (Nat.log 2 n - 4) + 2 := by omega
  rw [show (Nat.log 2 n - 3) + 1 = Nat.log 2 n - 2 by omega,
    hexponent, pow_add]
  norm_num [dyadicQ]
  ring

lemma dyadic_modulus_eight {n : Nat} (hn : 32 <= n) :
    2 ^ ((Nat.log 2 n - 2) + 1) = 8 * dyadicQ n := by
  have hlog := log_two_five_le hn
  have hexponent : Nat.log 2 n - 1 = (Nat.log 2 n - 4) + 3 := by omega
  rw [show (Nat.log 2 n - 2) + 1 = Nat.log 2 n - 1 by omega,
    hexponent, pow_add]
  norm_num [dyadicQ]
  ring

lemma dyadic_modulus_one {n : Nat} (hn : 32 <= n) :
    2 ^ ((Nat.log 2 n - 5) + 1) = dyadicQ n := by
  have hlog := log_two_five_le hn
  rw [show (Nat.log 2 n - 5) + 1 = Nat.log 2 n - 4 by omega]
  rfl

lemma dyadic_denominator_two {n : Nat} (hn : 32 <= n) :
    2 ^ (Nat.log 2 n - 3) = 2 * dyadicQ n := by
  have hlog := log_two_five_le hn
  rw [show Nat.log 2 n - 3 = (Nat.log 2 n - 4) + 1 by omega, pow_add]
  simp [dyadicQ, Nat.mul_comm]

lemma dyadic_denominator_four {n : Nat} (hn : 32 <= n) :
    2 ^ (Nat.log 2 n - 2) = 4 * dyadicQ n := by
  have hlog := log_two_five_le hn
  simpa only [show (Nat.log 2 n - 3) + 1 = Nat.log 2 n - 2 by omega] using
    dyadic_modulus_four hn

lemma dyadic_denominator_half {n : Nat} (hn : 32 <= n) :
    2 * 2 ^ (Nat.log 2 n - 5) = dyadicQ n := by
  have hlog := log_two_five_le hn
  simp only [dyadicQ]
  rw [show Nat.log 2 n - 4 = (Nat.log 2 n - 5) + 1 by omega, pow_add]
  simp [Nat.mul_comm]

lemma dyadic_denominator_quarter {n : Nat} (hlog : 6 <= Nat.log 2 n) :
    4 * 2 ^ (Nat.log 2 n - 6) = dyadicQ n := by
  simp only [dyadicQ]
  rw [show Nat.log 2 n - 4 = (Nat.log 2 n - 6) + 2 by omega, pow_add]
  norm_num
  ring

lemma prefixCongruent_one_of_le_length {word : List Nat} {k : Nat}
    (hk : k <= word.length) : PrefixCongruent word k 1 := by
  refine ⟨hk, ?_⟩
  intro i hi j hj x y hx hy
  simp only [Nat.ModEq, Nat.mod_one]

/-- **Proposition 2.8.** The first dyadic-threshold congruence blocks, for the
word and for both of its parity traces. -/
theorem proposition_2_8_holds : proposition_2_8 := by
  intro n word hn hword
  dsimp only
  intro hthreshold
  have hnPos : 0 < n := by omega
  have hlog : 5 <= Nat.log 2 n := log_two_five_le hn
  have hhalf : 8 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have hhalfOdd : 8 * dyadicQ n <= (n + 1) / 2 := by omega
  have hwordFour : PrefixCongruent word 2 (4 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 2) (r := 8) hnPos hword (by
        rw [dyadic_denominator_two hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four hn] at h
    exact h
  have hwordTwo : PrefixCongruent word 4 (2 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 4) (r := 16) hnPos hword (by
        simpa only [dyadicQ] using hthreshold) (by norm_num)
    rw [dyadic_modulus_two hn] at h
    exact h
  have hwordOne : PrefixCongruent word 8 (dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 8) (r := 32) hnPos hword (by
        have hh := dyadic_denominator_half hn
        nlinarith) (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hoddFour : PrefixCongruent (oddTrace word) 2 (4 * dyadicQ n) := by
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 2) (r := 8) hnPos hword hhalfOdd (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hevenFour : PrefixCongruent (evenTrace word) 2 (4 * dyadicQ n) := by
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 2) (r := 8) (by omega) hword hhalf (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hoddTwo : PrefixCongruent (oddTrace word) 4 (2 * dyadicQ n) := by
    have hdenom : 16 * 2 ^ (Nat.log 2 n - 5) <= (n + 1) / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 4) (r := 16) hnPos hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hevenTwo : PrefixCongruent (evenTrace word) 4 (2 * dyadicQ n) := by
    have hdenom : 16 * 2 ^ (Nat.log 2 n - 5) <= n / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 4) (r := 16) (by omega) hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have traceOne :
      PrefixCongruent (oddTrace word) 8 (dyadicQ n) ∧
        PrefixCongruent (evenTrace word) 8 (dyadicQ n) := by
    by_cases hlogSix : 6 <= Nat.log 2 n
    · have hoddDenom :
          32 * 2 ^ (Nat.log 2 n - 6) <= (n + 1) / 2 := by
        have hh := dyadic_denominator_quarter (n := n) hlogSix
        nlinarith
      have hevenDenom : 32 * 2 ^ (Nat.log 2 n - 6) <= n / 2 := by
        have hh := dyadic_denominator_quarter (n := n) hlogSix
        nlinarith
      have hodd := forcedOddTracePrefixCongruent (N := n)
        (j := Nat.log 2 n - 6) (k := 8) (r := 32) hnPos hword hoddDenom
        (by norm_num)
      have heven := forcedEvenTracePrefixCongruent (N := n)
        (j := Nat.log 2 n - 6) (k := 8) (r := 32) (by omega) hword hevenDenom
        (by norm_num)
      have hexponent : (Nat.log 2 n - 6) + 1 = Nat.log 2 n - 5 := by omega
      rw [hexponent, dyadic_denominator_half hn] at hodd heven
      exact ⟨hodd, heven⟩
    · have hlogEq : Nat.log 2 n = 5 := by omega
      have hqEq : dyadicQ n = 2 := by simp [dyadicQ, hlogEq]
      have hoddTheta := isTheta_oddBase hword
      have hevenTheta := isTheta_evenBase hword
      have hoddLength : 8 <= (oddBase word).length := by
        rw [isTheta_length hoddTheta]
        have hqPos := dyadicQ_pos n
        omega
      have hevenLength : 8 <= (evenBase word).length := by
        rw [isTheta_length hevenTheta]
        have hqPos := dyadicQ_pos n
        omega
      have hoddBase := prefixCongruent_one_of_le_length hoddLength
      have hevenBase := prefixCongruent_one_of_le_length hevenLength
      have hodd := prefixCongruent_oddLift_of_base
        (fun x hx => positive_of_mem_of_isTheta hoddTheta hx) hoddBase
      have heven := prefixCongruent_evenLift_of_base hevenBase
      rw [oddLift_oddBase] at hodd
      rw [evenLift_evenBase] at heven
      constructor
      · simpa only [hqEq] using hodd
      · simpa only [hqEq] using heven
  exact ⟨⟨hwordFour, hwordTwo, hwordOne⟩,
    ⟨⟨hoddFour, hoddTwo, traceOne.1⟩,
      ⟨hevenFour, hevenTwo, traceOne.2⟩⟩⟩

lemma dyadicQ_trace_prefixes {n k s : Nat} {word : List Nat}
    (hn : 32 <= n) (hword : IsTheta n word)
    (hhalf : s * dyadicQ n <= n / 2) (hk : k <= s) :
    PrefixCongruent (oddTrace word) k (dyadicQ n) ∧
      PrefixCongruent (evenTrace word) k (dyadicQ n) := by
  have hnPos : 0 < n := by omega
  have hhalfOdd : s * dyadicQ n <= (n + 1) / 2 := by omega
  by_cases hlogSix : 6 <= Nat.log 2 n
  · have hoddDenom :
        (4 * s) * 2 ^ (Nat.log 2 n - 6) <= (n + 1) / 2 := by
      have hh := dyadic_denominator_quarter (n := n) hlogSix
      nlinarith
    have hevenDenom : (4 * s) * 2 ^ (Nat.log 2 n - 6) <= n / 2 := by
      have hh := dyadic_denominator_quarter (n := n) hlogSix
      nlinarith
    have hodd := forcedOddTracePrefixCongruent (N := n)
      (j := Nat.log 2 n - 6) (k := k) (r := 4 * s) hnPos hword hoddDenom
      (by omega)
    have heven := forcedEvenTracePrefixCongruent (N := n)
      (j := Nat.log 2 n - 6) (k := k) (r := 4 * s) (by omega) hword hevenDenom
      (by omega)
    have hlog := log_two_five_le hn
    have hexponent : (Nat.log 2 n - 6) + 1 = Nat.log 2 n - 5 := by omega
    rw [hexponent, dyadic_denominator_half hn] at hodd heven
    exact ⟨hodd, heven⟩
  · have hlog := log_two_five_le hn
    have hlogEq : Nat.log 2 n = 5 := by omega
    have hqEq : dyadicQ n = 2 := by simp [dyadicQ, hlogEq]
    have hqPos := dyadicQ_pos n
    have hsQ : s <= s * dyadicQ n := Nat.le_mul_of_pos_right s hqPos
    have hoddTheta := isTheta_oddBase hword
    have hevenTheta := isTheta_evenBase hword
    have hoddLength : k <= (oddBase word).length := by
      rw [isTheta_length hoddTheta]
      omega
    have hevenLength : k <= (evenBase word).length := by
      rw [isTheta_length hevenTheta]
      omega
    have hoddBase := prefixCongruent_one_of_le_length hoddLength
    have hevenBase := prefixCongruent_one_of_le_length hevenLength
    have hodd := prefixCongruent_oddLift_of_base
      (fun x hx => positive_of_mem_of_isTheta hoddTheta hx) hoddBase
    have heven := prefixCongruent_evenLift_of_base hevenBase
    rw [oddLift_oddBase] at hodd
    rw [evenLift_evenBase] at heven
    constructor
    · simpa only [hqEq] using hodd
    · simpa only [hqEq] using heven

/-- **Proposition 2.9.** The second dyadic-threshold congruence blocks. -/
theorem proposition_2_9_holds : proposition_2_9 := by
  intro n word hn hword
  dsimp only
  intro hthreshold
  have hnPos : 0 < n := by omega
  have hhalf : 11 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have hhalfOdd : 11 * dyadicQ n <= (n + 1) / 2 := by omega
  have hwordFour : PrefixCongruent word 3 (4 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 3) (r := 11) hnPos hword (by
        rw [dyadic_denominator_two hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four hn] at h
    exact h
  have hwordTwo : PrefixCongruent word 5 (2 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 5) (r := 22) hnPos hword (by
        simpa only [dyadicQ] using hthreshold) (by norm_num)
    rw [dyadic_modulus_two hn] at h
    exact h
  have hwordOne : PrefixCongruent word 11 (dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 11) (r := 44) hnPos hword (by
        have hh := dyadic_denominator_half hn
        nlinarith) (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hoddFour : PrefixCongruent (oddTrace word) 3 (4 * dyadicQ n) := by
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 3) (r := 11) hnPos hword hhalfOdd (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hevenFour : PrefixCongruent (evenTrace word) 3 (4 * dyadicQ n) := by
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 3) (r := 11) (by omega) hword hhalf (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hoddTwo : PrefixCongruent (oddTrace word) 5 (2 * dyadicQ n) := by
    have hdenom : 22 * 2 ^ (Nat.log 2 n - 5) <= (n + 1) / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 5) (r := 22) hnPos hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hevenTwo : PrefixCongruent (evenTrace word) 5 (2 * dyadicQ n) := by
    have hdenom : 22 * 2 ^ (Nat.log 2 n - 5) <= n / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 5) (r := 22) (by omega) hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have traceOne := dyadicQ_trace_prefixes (n := n) (word := word)
    (k := 11) (s := 11) hn hword hhalf (by norm_num)
  exact ⟨⟨hwordFour, hwordTwo, hwordOne⟩,
    ⟨⟨hoddFour, hoddTwo, traceOne.1⟩,
      ⟨hevenFour, hevenTwo, traceOne.2⟩⟩⟩

/-- **Proposition 2.10.** The third dyadic-threshold congruence blocks. -/
theorem proposition_2_10_holds : proposition_2_10 := by
  intro n word hn hword
  dsimp only
  intro hthreshold
  have hnPos : 0 < n := by omega
  have hhalf : 14 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have hhalfOdd : 14 * dyadicQ n <= (n + 1) / 2 := by omega
  have hwordEight : PrefixCongruent word 2 (8 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 2)
      (k := 2) (r := 7) hnPos hword (by
        rw [dyadic_denominator_four hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_eight hn] at h
    exact h
  have hwordFour : PrefixCongruent word 3 (4 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 3) (r := 14) hnPos hword (by
        rw [dyadic_denominator_two hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four hn] at h
    exact h
  have hwordTwo : PrefixCongruent word 7 (2 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 7) (r := 28) hnPos hword (by
        simpa only [dyadicQ] using hthreshold) (by norm_num)
    rw [dyadic_modulus_two hn] at h
    exact h
  have hwordOne : PrefixCongruent word 14 (dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 14) (r := 56) hnPos hword (by
        have hh := dyadic_denominator_half hn
        nlinarith) (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hoddEight : PrefixCongruent (oddTrace word) 2 (8 * dyadicQ n) := by
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 2) (r := 7) hnPos hword (by
        rw [dyadic_denominator_two hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four hn] at h
    convert h using 1 <;> omega
  have hevenEight : PrefixCongruent (evenTrace word) 2 (8 * dyadicQ n) := by
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 2) (r := 7) (by omega) hword (by
        rw [dyadic_denominator_two hn]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four hn] at h
    convert h using 1 <;> omega
  have hoddFour : PrefixCongruent (oddTrace word) 3 (4 * dyadicQ n) := by
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 3) (r := 14) hnPos hword hhalfOdd (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hevenFour : PrefixCongruent (evenTrace word) 3 (4 * dyadicQ n) := by
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 3) (r := 14) (by omega) hword hhalf (by norm_num)
    rw [dyadic_modulus_two hn] at h
    convert h using 1 <;> omega
  have hoddTwo : PrefixCongruent (oddTrace word) 7 (2 * dyadicQ n) := by
    have hdenom : 28 * 2 ^ (Nat.log 2 n - 5) <= (n + 1) / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 7) (r := 28) hnPos hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have hevenTwo : PrefixCongruent (evenTrace word) 7 (2 * dyadicQ n) := by
    have hdenom : 28 * 2 ^ (Nat.log 2 n - 5) <= n / 2 := by
      have hh := dyadic_denominator_half hn
      nlinarith
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := 7) (r := 28) (by omega) hword hdenom (by norm_num)
    rw [dyadic_modulus_one hn] at h
    exact h
  have traceOne := dyadicQ_trace_prefixes (n := n) (word := word)
    (k := 14) (s := 14) hn hword hhalf (by norm_num)
  exact ⟨⟨hwordEight, hwordFour, hwordTwo, hwordOne⟩,
    ⟨⟨hoddEight, hoddFour, hoddTwo, traceOne.1⟩,
      ⟨hevenEight, hevenFour, hevenTwo, traceOne.2⟩⟩⟩

end LeanProofs.Sharma2012
