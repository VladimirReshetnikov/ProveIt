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

lemma prologue_prefix (n : Nat) (word : List Nat) :
    prologue n word <+: word := by
  cases word with
  | nil => simp [prologue]
  | cons first tail =>
      simp only [prologue]
      exact (List.prefix_cons_inj first).2 (List.takeWhile_prefix _)

lemma mem_lowerHalf_of_mem_prologue {n : Nat} {word : List Nat} {a x : Nat}
    (hstart : StartsWith word a) (haLower : a ∈ lowerHalf n)
    (hx : x ∈ prologue n word) : x ∈ lowerHalf n := by
  cases word with
  | nil => simp [StartsWith] at hstart
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using hstart
      subst first
      simp only [prologue, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact haLower
      · have hsame : SameHalf n a x := by
          have hp := List.mem_takeWhile_imp
            (p := fun y : Nat => decide (SameHalf n a y)) (l := tail) hx
          exact of_decide_eq_true hp
        rcases hsame with hLower | hUpper
        · exact hLower.2
        · simp only [lowerHalf, upperHalf, Finset.mem_Icc] at haLower hUpper
          omega

lemma lowerPrologue_entry_le_first {n : Nat} {word : List Nat} {a : Nat}
    (htheta : IsTheta n word) (hstart : StartsWith word a)
    (haLower : a ∈ lowerHalf n) {i x : Nat}
    (hi : i < (prologue n word).length) (hx : (prologue n word)[i]? = some x) :
    x <= a := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
      by_contra hle
      have hax : a < x := by omega
      have hprefix := prologue_prefix n word
      obtain ⟨suffix, hwordEq⟩ := hprefix
      have hxWord : word[i]? = some x := by
        rw [← hwordEq, List.getElem?_append_left]
        exact hx
        exact hi
      have hxMemPro : x ∈ prologue n word := List.mem_iff_getElem?.mpr ⟨i, hx⟩
      have hxLower := mem_lowerHalf_of_mem_prologue hstart haLower hxMemPro
      have haSegment : a ∈ segment n := by
        have haMem : a ∈ word := by
          cases word with
          | nil => simp [StartsWith] at hstart
          | cons first tail =>
              have hfirst : first = a := by simpa [StartsWith] using hstart
              simp [hfirst]
        exact mem_segment_of_mem_of_isTheta htheta haMem
      let r := 2 * x - a
      have hrSegment : r ∈ segment n := by
        simp only [r, segment, lowerHalf, Finset.mem_Icc] at haSegment hxLower ⊢
        omega
      have hrMem := mem_of_mem_segment_of_isTheta htheta hrSegment
      obtain ⟨j, hjWord⟩ := List.mem_iff_getElem?.mp hrMem
      have hzero : word[0]? = some a := by
        rw [← List.head?_eq_getElem?]
        exact hstart
      have hiPos : 0 < i := by
        by_contra hiZero
        have hiEq : i = 0 := by omega
        subst i
        have haxEq : a = x := Option.some.inj (hzero.symm.trans hxWord)
        omega
      have hrEq : r = a + 2 * (x - a) := by
        dsimp [r]
        omega
      have hxEq : x = a + (x - a) := by omega
      have hji : j < i := by
        by_contra hnot
        have hij : i < j := by
          obtain ⟨hjLen, _⟩ := List.getElem?_eq_some_iff.mp hjWord
          have hjiNe : j ≠ i := by
            intro hji
            subst j
            have hrx : r = x := Option.some.inj (hjWord.symm.trans hxWord)
            dsimp [r] at hrx
            omega
          omega
        apply isTheta_threeFree htheta
        apply containsThreeAP_of_increasing_positions hiPos hij (by omega : 0 < x - a)
          hzero
        · rw [← hxEq]
          exact hxWord
        · rw [← hrEq]
          exact hjWord
      have hjProBound : j < (prologue n word).length := hji.trans hi
      have hjPro : (prologue n word)[j]? = some r := by
        rw [← hwordEq, List.getElem?_append_left hjProBound] at hjWord
        exact hjWord
      have hrLe := ih j hji hjProBound hjPro
      dsimp [r] at hrLe
      omega

lemma first_le_upperPrologue_entry {n : Nat} {word : List Nat} {a : Nat}
    (htheta : IsTheta n word) (hstart : StartsWith word a)
    (hupper : forall x : Nat, x ∈ prologue n word -> x ∈ upperHalf n)
    {i x : Nat} (hi : i < (prologue n word).length)
    (hx : (prologue n word)[i]? = some x) : a <= x := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
      by_contra hle
      have hxa : x < a := by omega
      have hprefix := prologue_prefix n word
      obtain ⟨suffix, hwordEq⟩ := hprefix
      have hxWord : word[i]? = some x := by
        rw [← hwordEq, List.getElem?_append_left]
        exact hx
        exact hi
      have hxMemPro : x ∈ prologue n word := List.mem_iff_getElem?.mpr ⟨i, hx⟩
      have hxUpper := hupper x hxMemPro
      have haSegment : a ∈ segment n := by
        have haMem : a ∈ word := by
          cases word with
          | nil => simp [StartsWith] at hstart
          | cons first tail =>
              have hfirst : first = a := by simpa [StartsWith] using hstart
              simp [hfirst]
        exact mem_segment_of_mem_of_isTheta htheta haMem
      let r := 2 * x - a
      have hrSegment : r ∈ segment n := by
        simp only [r, segment, upperHalf, Finset.mem_Icc] at haSegment hxUpper ⊢
        omega
      have hrMem := mem_of_mem_segment_of_isTheta htheta hrSegment
      obtain ⟨j, hjWord⟩ := List.mem_iff_getElem?.mp hrMem
      have hzero : word[0]? = some a := by
        rw [← List.head?_eq_getElem?]
        exact hstart
      have hiPos : 0 < i := by
        by_contra hiZero
        have hiEq : i = 0 := by omega
        subst i
        have haxEq : a = x := Option.some.inj (hzero.symm.trans hxWord)
        omega
      have haTwoX : a <= 2 * x := by
        simp only [segment, upperHalf, Finset.mem_Icc] at haSegment hxUpper
        omega
      have haEq : a = r + 2 * (a - x) := by
        dsimp [r]
        omega
      have hxEq : x = r + (a - x) := by
        dsimp [r]
        omega
      have hji : j < i := by
        by_contra hnot
        have hij : i < j := by
          obtain ⟨hjLen, _⟩ := List.getElem?_eq_some_iff.mp hjWord
          have hjiNe : j ≠ i := by
            intro hji
            subst j
            have hrx : r = x := Option.some.inj (hjWord.symm.trans hxWord)
            dsimp [r] at hrx
            omega
          omega
        apply isTheta_threeFree htheta
        apply containsThreeAP_of_decreasing_positions hiPos hij (by omega : 0 < a - x)
        · rw [← haEq]
          exact hzero
        · rw [← hxEq]
          exact hxWord
        · exact hjWord
      have hjProBound : j < (prologue n word).length := hji.trans hi
      have hjPro : (prologue n word)[j]? = some r := by
        rw [← hwordEq, List.getElem?_append_left hjProBound] at hjWord
        exact hjWord
      have haLeR := ih j hji hjProBound hjPro
      dsimp [r] at haLeR
      omega

theorem lemma_2_2_holds : lemma_2_2 := by
  intro n gamma a htheta hstart
  constructor
  · intro haLower x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨hiLen, _⟩ := List.getElem?_eq_some_iff.mp hi
    exact lowerPrologue_entry_le_first htheta hstart haLower hiLen hi
  · intro hupper x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨hiLen, _⟩ := List.getElem?_eq_some_iff.mp hi
    exact first_le_upperPrologue_entry htheta hstart hupper hiLen hi

lemma occursLeftOf_of_startsWith_of_mem {word : List Nat} {first x : Nat}
    (hword : word.Nodup) (hstart : StartsWith word first) (hx : x ∈ word)
    (hne : first ≠ x) : OccursLeftOf word first x := by
  have hfirstMem : first ∈ word := by
    cases word with
    | nil => simp [StartsWith] at hstart
    | cons a tail =>
        have ha : a = first := by simpa [StartsWith] using hstart
        simp [ha]
  rcases occursLeftOf_total_of_mem hword hfirstMem hx hne with hleft | hright
  · exact hleft
  · have hfirstAt : word[0]? = some first := by
      rw [← List.head?_eq_getElem?]
      exact hstart
    exact False.elim ((not_occursLeftOf_to_head hword hfirstAt) hright)

lemma left_endpoint_left_of_middle_of_right_endpoint {n : Nat} {word : List Nat}
    (hword : IsTheta n word) {a d : Nat} (hd : 0 < d)
    (ha : a ∈ word) (hm : a + d ∈ word) (_hc : a + 2 * d ∈ word)
    (hcm : OccursLeftOf word (a + 2 * d) (a + d)) :
    OccursLeftOf word a (a + d) := by
  rcases occursLeftOf_total_of_mem (isTheta_nodup hword) ha hm (by omega) with ham | hma
  · exact ham
  · rcases hcm with ⟨i, j, hij, hi, hj⟩
    rcases hma with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' :=
      getElem?_index_unique_of_nodup (isTheta_nodup hword) hj hj'
    subst j'
    exfalso
    exact (isTheta_threeFree hword)
      (containsThreeAP_of_decreasing_positions hij hjk hd hi hj hk)

lemma factorization_three_mul_pow_two (k : Nat) :
    (3 * 2 ^ k).factorization 2 = k := by
  rw [Nat.factorization_mul (by norm_num : 3 ≠ 0)
    (pow_ne_zero k (by norm_num : 2 ≠ 0))]
  norm_num [Nat.factorization_pow]

lemma factorization_two_mul_pow_two (k : Nat) :
    (2 * 2 ^ k).factorization 2 = k + 1 := by
  rw [Nat.factorization_mul (by norm_num : 2 ≠ 0)
    (pow_ne_zero k (by norm_num : 2 ≠ 0))]
  norm_num [Nat.factorization_pow]
  omega

theorem lemma_2_3_holds : lemma_2_3 := by
  intro n gamma a1 t htheta hstart ha1Four htLower htUpper
  dsimp only
  let u := 2 ^ (t - 2)
  have htTwo : 2 <= t := by
    by_contra ht
    have htCases : t = 0 \/ t = 1 := by omega
    rcases htCases with rfl | rfl
    · norm_num at htUpper
      omega
    · norm_num at htUpper
      omega
  have huPos : 0 < u := by exact pow_pos (by norm_num) _
  have hfourU : 4 * u = 2 ^ t := by
    dsimp [u]
    conv_rhs => rw [show t = (t - 2) + 2 by omega]
    rw [pow_add]
    norm_num [Nat.mul_comm]
  have heightU : 8 * u = 2 ^ (t + 1) := by
    dsimp [u]
    conv_rhs => rw [show t + 1 = (t - 2) + 3 by omega]
    rw [pow_add]
    norm_num [Nat.mul_comm]
  have hfourLess : 4 * u < a1 := by omega
  have ha1Eight : a1 <= 8 * u := by omega
  have ha1Mem : a1 ∈ gamma := by
    cases gamma with
    | nil => simp [StartsWith] at hstart
    | cons first tail =>
        have hfirst : first = a1 := by simpa [StartsWith] using hstart
        simp [hfirst]
  have ha1Segment := mem_segment_of_mem_of_isTheta htheta ha1Mem
  have hsubFourSegment : a1 - 4 * u ∈ segment n := by
    simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
    omega
  have hsubTwoSegment : a1 - 2 * u ∈ segment n := by
    simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
    omega
  have hsubOneSegment : a1 - u ∈ segment n := by
    simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
    omega
  have hsubFourMem := mem_of_mem_segment_of_isTheta htheta hsubFourSegment
  have hsubTwoMem := mem_of_mem_segment_of_isTheta htheta hsubTwoSegment
  have hsubOneMem := mem_of_mem_segment_of_isTheta htheta hsubOneSegment
  have hstartSubFour := occursLeftOf_of_startsWith_of_mem
    (isTheta_nodup htheta) hstart hsubFourMem (by omega)
  have hstartSubTwo := occursLeftOf_of_startsWith_of_mem
    (isTheta_nodup htheta) hstart hsubTwoMem (by omega)
  have hstartSubOne := occursLeftOf_of_startsWith_of_mem
    (isTheta_nodup htheta) hstart hsubOneMem (by omega)
  have hsubTwoSubOne : OccursLeftOf gamma (a1 - 2 * u) (a1 - u) := by
    have hforced := left_endpoint_left_of_middle_of_right_endpoint htheta
      (a := a1 - 2 * u) (d := u) huPos hsubTwoMem
      (by convert hsubOneMem using 1 <;> omega)
      (by convert ha1Mem using 1; omega)
      (by convert hstartSubOne using 1 <;> omega)
    convert hforced using 1; omega
  have hsubFourSubTwo : OccursLeftOf gamma (a1 - 4 * u) (a1 - 2 * u) := by
    have hforced := left_endpoint_left_of_middle_of_right_endpoint htheta
      (a := a1 - 4 * u) (d := 2 * u) (by omega) hsubFourMem
      (by convert hsubTwoMem using 1 <;> omega)
      (by convert ha1Mem using 1; omega)
      (by convert hstartSubTwo using 1 <;> omega)
    convert hforced using 1; omega
  refine ⟨hstartSubFour, hsubFourSubTwo, hsubTwoSubOne, ?_, ?_⟩
  · intro hnPlusTwo
    have hplusTwoSegment : a1 + 2 * u ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
      omega
    have hplusTwoMem := mem_of_mem_segment_of_isTheta htheta hplusTwoSegment
    have hforced := right_endpoint_left_of_middle_of_left_endpoint htheta
      (a := a1 - 4 * u) (d := 3 * u) (by omega) hsubFourMem
      (by convert hsubOneMem using 1; omega)
      (by convert hplusTwoMem using 1; omega)
      (by
        have hchain := occursLeftOf_trans (isTheta_nodup htheta)
          hsubFourSubTwo hsubTwoSubOne
        convert hchain using 1; omega)
    convert hforced using 1 <;> omega
  · intro hnPlusSeven
    have hplusTwoSegment : a1 + 2 * u ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
      omega
    have hsubThreeSegment : a1 - 3 * u ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
      omega
    have hplusSevenSegment : a1 + 7 * u ∈ segment n := by
      simp only [segment, Finset.mem_Icc] at ha1Segment ⊢
      omega
    have hdistX : Nat.dist a1 (a1 - 3 * u) = 3 * u := by
      unfold Nat.dist
      omega
    have hdistZ : Nat.dist a1 (a1 + 2 * u) = 2 * u := by
      unfold Nat.dist
      omega
    have hdegreeX : binaryCongruenceDegree a1 (a1 - 3 * u) = t - 2 := by
      unfold binaryCongruenceDegree
      rw [hdistX]
      exact factorization_three_mul_pow_two (t - 2)
    have hdegreeZ : binaryCongruenceDegree a1 (a1 + 2 * u) = (t - 2) + 1 := by
      unfold binaryCongruenceDegree
      rw [hdistZ]
      exact factorization_two_mul_pow_two (t - 2)
    have hforced := theorem_2_4_holds n gamma a1 (a1 - 3 * u) (a1 + 7 * u)
      (a1 + 2 * u) htheta hstart hsubThreeSegment hplusSevenSegment hplusTwoSegment
      (by omega) (by simpa using (show a1 ≠ a1 + 2 * u by omega))
      (by simpa using (show a1 ≠ a1 - 3 * u by omega)) (by omega)
    exact hforced

lemma mem_prologue_of_occursLeftOf_mem_prologue {n : Nat} {word : List Nat}
    {x y : Nat} (hword : word.Nodup) (hy : y ∈ prologue n word)
    (hxy : OccursLeftOf word x y) :
    x ∈ prologue n word := by
  obtain ⟨j, hjPro⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨hjBound, _⟩ := List.getElem?_eq_some_iff.mp hjPro
  rcases hxy with ⟨i, j', hij, hiWord, hjWord⟩
  have hprefix := prologue_prefix n word
  obtain ⟨suffix, hwordEq⟩ := hprefix
  have hjWord' : word[j]? = some y := by
    rw [← hwordEq, List.getElem?_append_left hjBound]
    exact hjPro
  have hjEq : j' = j := by
    exact getElem?_index_unique_of_nodup hword hjWord hjWord'
  subst j'
  have hiBound : i < (prologue n word).length := hij.trans hjBound
  have hiPro : (prologue n word)[i]? = some x := by
    rw [← hwordEq, List.getElem?_append_left hiBound] at hiWord
    exact hiWord
  exact List.mem_iff_getElem?.mpr ⟨i, hiPro⟩

theorem lemma_2_4_holds : lemma_2_4 := by
  intro n gamma a1 htheta hstart haLower
  have hproNodup : (prologue n gamma).Nodup :=
    List.Nodup.sublist (prologue_prefix n gamma).sublist (isTheta_nodup htheta)
  have hextreme := (lemma_2_2_holds n gamma a1 htheta hstart).1 haLower
  by_cases haSmall : a1 <= 6
  · have hsubset : (prologue n gamma).toFinset ⊆ segment a1 := by
      intro x hx
      have hxPro : x ∈ prologue n gamma := by simpa using hx
      have hxWord := (prologue_prefix n gamma).mem hxPro
      have hxSegment := mem_segment_of_mem_of_isTheta htheta hxWord
      simp only [segment, Finset.mem_Icc] at hxSegment ⊢
      exact ⟨hxSegment.1, hextreme x hxPro⟩
    calc
      (prologue n gamma).length = (prologue n gamma).toFinset.card :=
        (List.toFinset_card_of_nodup hproNodup).symm
      _ <= (segment a1).card := Finset.card_le_card hsubset
      _ = a1 := by simp [segment]
      _ <= 6 := haSmall
  · have haSeven : 7 <= a1 := by omega
    let t := Nat.log 2 (a1 - 1)
    let u := 2 ^ (t - 2)
    have haPredNe : a1 - 1 ≠ 0 := by omega
    have htLower : 2 ^ t < a1 := by
      have h := Nat.pow_log_le_self 2 haPredNe
      dsimp [t] at h ⊢
      omega
    have htUpper : a1 <= 2 ^ (t + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (a1 - 1)
      dsimp [t] at h ⊢
      omega
    have htTwo : 2 <= t := by
      by_contra ht
      have htCases : t = 0 \/ t = 1 := by omega
      rcases htCases with htZero | htOne
      · rw [htZero] at htUpper
        norm_num at htUpper
        omega
      · rw [htOne] at htUpper
        norm_num at htUpper
        omega
    have huPos : 0 < u := pow_pos (by norm_num) _
    have hfourU : 4 * u = 2 ^ t := by
      dsimp [u]
      conv_rhs => rw [show t = (t - 2) + 2 by omega]
      rw [pow_add]
      norm_num [Nat.mul_comm]
    have heightU : 8 * u = 2 ^ (t + 1) := by
      dsimp [u]
      conv_rhs => rw [show t + 1 = (t - 2) + 3 by omega]
      rw [pow_add]
      norm_num [Nat.mul_comm]
    have hfourLess : 4 * u < a1 := by omega
    have haEight : a1 <= 8 * u := by omega
    have haSegment : a1 ∈ segment n := by
      have haMem : a1 ∈ gamma := by
        cases gamma with
        | nil => simp [StartsWith] at hstart
        | cons first tail =>
            have hfirst : first = a1 := by simpa [StartsWith] using hstart
            simp [hfirst]
      exact mem_segment_of_mem_of_isTheta htheta haMem
    have hnTwoA : 2 * a1 <= n := by
      simp only [lowerHalf, Finset.mem_Icc] at haLower
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp haLower.2
    have hlemma := lemma_2_3_holds n gamma a1 t htheta hstart (by omega)
      htLower htUpper
    dsimp only at hlemma
    rcases hlemma with ⟨hstartFour, hfourTwo, htwoOne, hpartTwo, hpartThree⟩
    have hnPlusTwo : a1 + 2 * u <= n := by omega
    have hplusTwoBeforeOne := hpartTwo hnPlusTwo
    have hsubOneNotPro : a1 - u ∉ prologue n gamma := by
      intro hsubOne
      have hplusTwoPro := mem_prologue_of_occursLeftOf_mem_prologue
        (isTheta_nodup htheta) hsubOne hplusTwoBeforeOne
      have hplusTwoLe := hextreme (a1 + 2 * u) hplusTwoPro
      omega
    have hcongruent : forall x : Nat, x ∈ prologue n gamma -> Nat.ModEq u x a1 := by
      intro x hxPro
      have hxLe := hextreme x hxPro
      have hxWord := (prologue_prefix n gamma).mem hxPro
      have hxSegment := mem_segment_of_mem_of_isTheta htheta hxWord
      by_contra hnotMod
      have hxa : x < a1 := by
        by_contra hnot
        have hxaEq : x = a1 := by omega
        subst x
        exact hnotMod (Nat.ModEq.refl a1)
      let y := 2 * a1 - 2 * u - x
      let z := a1 - u
      have hzSegment : z ∈ segment n := by
        simp only [z, segment, Finset.mem_Icc] at haSegment ⊢
        omega
      have hySegment : y ∈ segment n := by
        simp only [y, segment, Finset.mem_Icc] at hxSegment haSegment ⊢
        omega
      have hdistX : Nat.dist a1 x = a1 - x := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hxa.le]
      have hdistXNe : Nat.dist a1 x ≠ 0 := by
        rw [hdistX]
        omega
      have hdegreeX : binaryCongruenceDegree a1 x < t - 2 := by
        by_contra hnotLess
        have hpowDvd : 2 ^ (t - 2) ∣ Nat.dist a1 x :=
          (Nat.prime_two.pow_dvd_iff_le_factorization hdistXNe).2 (by
            unfold binaryCongruenceDegree at hnotLess
            omega)
        have hmod : Nat.ModEq u x a1 := by
          apply (Nat.modEq_iff_dvd' hxa.le).2
          simpa only [u, hdistX] using hpowDvd
        exact hnotMod hmod
      have hdistZ : Nat.dist a1 z = u := by
        simp only [z]
        unfold Nat.dist
        omega
      have hdegreeZ : binaryCongruenceDegree a1 z = t - 2 := by
        unfold binaryCongruenceDegree
        rw [hdistZ]
        dsimp only [u]
        exact Nat.factorization_pow_self Nat.prime_two
      have haz : a1 != z := by
        have : a1 ≠ z := by simp only [z]; omega
        simpa using this
      have hax : a1 != x := by simpa using hxa.ne'
      have hforced := theorem_2_4_holds n gamma a1 x y z htheta hstart
        hxSegment hySegment hzSegment (by simp only [y, z]; omega) haz hax (by omega)
      have hzPro := mem_prologue_of_occursLeftOf_mem_prologue
        (isTheta_nodup htheta) hxPro hforced.1
      exact hsubOneNotPro (by simpa only [z] using hzPro)
    have hparameter : forall x : Nat, x ∈ prologue n gamma ->
        exists d : Nat, d <= 7 /\ x = a1 - d * u := by
      intro x hxPro
      have hxLe := hextreme x hxPro
      have hxWord := (prologue_prefix n gamma).mem hxPro
      have hxSegment := mem_segment_of_mem_of_isTheta htheta hxWord
      obtain ⟨d, had⟩ := (Nat.modEq_iff_exists_eq_add hxLe).mp (hcongruent x hxPro)
      have had' : a1 = x + d * u := by simpa [Nat.mul_comm] using had
      have hd : d <= 7 := by
        by_contra hd
        have h8d : 8 <= d := by omega
        have hmul : 8 * u <= d * u := Nat.mul_le_mul_right u h8d
        simp only [segment, Finset.mem_Icc] at hxSegment
        omega
      refine ⟨d, hd, ?_⟩
      omega
    by_cases haSevenU : a1 <= 7 * u
    · let candidates :=
        [a1, a1 - 2 * u, a1 - 3 * u, a1 - 4 * u, a1 - 5 * u, a1 - 6 * u]
      have hsubset : (prologue n gamma).toFinset ⊆ candidates.toFinset := by
        intro x hx
        have hxPro : x ∈ prologue n gamma := by simpa using hx
        obtain ⟨d, hd, hxd⟩ := hparameter x hxPro
        have hxWord := (prologue_prefix n gamma).mem hxPro
        have hxSegment := mem_segment_of_mem_of_isTheta htheta hxWord
        have hdOne : d ≠ 1 := by
          intro hdEq
          subst d
          have hxEq : x = a1 - u := by simpa using hxd
          rw [hxEq] at hxPro
          exact hsubOneNotPro hxPro
        have hdSeven : d ≠ 7 := by
          intro hdEq
          subst d
          simp only [segment, Finset.mem_Icc] at hxSegment
          omega
        interval_cases d <;> simp [candidates] at * <;> omega
      calc
        (prologue n gamma).length = (prologue n gamma).toFinset.card :=
          (List.toFinset_card_of_nodup hproNodup).symm
        _ <= candidates.toFinset.card := Finset.card_le_card hsubset
        _ <= candidates.length := List.toFinset_card_le candidates
        _ = 6 := by simp [candidates]
    · have haSevenLess : 7 * u < a1 := by omega
      have hnPlusSeven : a1 + 7 * u <= n := by omega
      have hplusTwoBeforeThree := (hpartThree hnPlusSeven).1
      have hsubThreeNotPro : a1 - 3 * u ∉ prologue n gamma := by
        intro hsubThree
        have hplusTwoPro := mem_prologue_of_occursLeftOf_mem_prologue
          (isTheta_nodup htheta) hsubThree hplusTwoBeforeThree
        have hplusTwoLe := hextreme (a1 + 2 * u) hplusTwoPro
        omega
      let candidates :=
        [a1, a1 - 2 * u, a1 - 4 * u, a1 - 5 * u, a1 - 6 * u, a1 - 7 * u]
      have hsubset : (prologue n gamma).toFinset ⊆ candidates.toFinset := by
        intro x hx
        have hxPro : x ∈ prologue n gamma := by simpa using hx
        obtain ⟨d, hd, hxd⟩ := hparameter x hxPro
        have hdOne : d ≠ 1 := by
          intro hdEq
          subst d
          have hxEq : x = a1 - u := by simpa using hxd
          rw [hxEq] at hxPro
          exact hsubOneNotPro hxPro
        have hdThree : d ≠ 3 := by
          intro hdEq
          subst d
          have hxEq : x = a1 - 3 * u := by simpa using hxd
          rw [hxEq] at hxPro
          exact hsubThreeNotPro hxPro
        interval_cases d <;> simp [candidates] at * <;> omega
      calc
        (prologue n gamma).length = (prologue n gamma).toFinset.card :=
          (List.toFinset_card_of_nodup hproNodup).symm
        _ <= candidates.toFinset.card := Finset.card_le_card hsubset
        _ <= candidates.length := List.toFinset_card_le candidates
        _ = 6 := by simp [candidates]

lemma threeFree_complement {n : Nat} {word : List Nat}
    (hword : IsTheta n word) : ThreeFree (complement n word) := by
  intro hap
  rcases hap with ⟨indices, hindices, a, d, hd, hvalues | hvalues⟩
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h0)
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h1)
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h2)
    have hx0Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 0, hx0⟩)
    have hx1Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 1, hx1⟩)
    have hx2Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 2, hx2⟩)
    have hx0Eq : x0 = x2 + 2 * d := by
      simp only [segment, Finset.mem_Icc] at hx0Segment hx1Segment hx2Segment
      omega
    have hx1Eq : x1 = x2 + d := by
      simp only [segment, Finset.mem_Icc] at hx0Segment hx1Segment hx2Segment
      omega
    apply isTheta_threeFree hword
    apply containsThreeAP_of_decreasing_positions
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) hd
    · rw [← hx0Eq]
      exact hx0
    · rw [← hx1Eq]
      exact hx1
    · exact hx2
  · have h0 := hvalues (0 : Fin 3)
    have h1 := hvalues (1 : Fin 3)
    have h2 := hvalues (2 : Fin 3)
    norm_num at h0 h1 h2
    obtain ⟨x0, hx0, hx0Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h0)
    obtain ⟨x1, hx1, hx1Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h1)
    obtain ⟨x2, hx2, hx2Value⟩ :=
      exists_of_getElem?_map_eq_some (f := fun x => n + 1 - x) (by simpa [complement] using h2)
    have hx0Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 0, hx0⟩)
    have hx1Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 1, hx1⟩)
    have hx2Segment := mem_segment_of_mem_of_isTheta hword
      (List.mem_iff_getElem?.mpr ⟨indices 2, hx2⟩)
    have hx1Eq : x1 = x0 + d := by
      simp only [segment, Finset.mem_Icc] at hx0Segment hx1Segment hx2Segment
      omega
    have hx2Eq : x2 = x0 + 2 * d := by
      simp only [segment, Finset.mem_Icc] at hx0Segment hx1Segment hx2Segment
      omega
    apply isTheta_threeFree hword
    apply containsThreeAP_of_increasing_positions
      (hindices (show (0 : Fin 3) < 1 by decide))
      (hindices (show (1 : Fin 3) < 2 by decide)) hd hx0
    · rw [← hx1Eq]
      exact hx1
    · rw [← hx2Eq]
      exact hx2

lemma isTheta_complement {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    IsTheta n (complement n word) := by
  refine ⟨⟨?_, ?_⟩, threeFree_complement hword⟩
  · apply List.Nodup.map_on _ (isTheta_nodup hword)
    intro x hx y hy hxy
    have hxSegment := mem_segment_of_mem_of_isTheta hword hx
    have hySegment := mem_segment_of_mem_of_isTheta hword hy
    simp only [segment, Finset.mem_Icc] at hxSegment hySegment
    omega
  · apply Finset.ext
    intro z
    simp only [List.mem_toFinset, complement, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact complementValue_mem_segment (mem_segment_of_mem_of_isTheta hword hx)
    · intro hzSegment
      let x := n + 1 - z
      have hxSegment : x ∈ segment n := complementValue_mem_segment hzSegment
      have hxMem := mem_of_mem_segment_of_isTheta hword hxSegment
      refine ⟨x, hxMem, ?_⟩
      simp only [segment, Finset.mem_Icc] at hzSegment
      omega

lemma startsWith_complement {n : Nat} {word : List Nat} {x : Nat}
    (hstart : StartsWith word x) : StartsWith (complement n word) (n + 1 - x) := by
  unfold StartsWith at hstart ⊢
  simp only [complement, List.head?_map, hstart, Option.map_some]

theorem theorem_2_5_holds : theorem_2_5 := by
  intro n gamma htheta
  cases gamma with
  | nil => simp [prologue]
  | cons a tail =>
      have hstart : StartsWith (a :: tail) a := by simp [StartsWith]
      have haSegment : a ∈ segment n :=
        mem_segment_of_mem_of_isTheta htheta (by simp)
      by_cases haLower : a ∈ lowerHalf n
      · exact lemma_2_4_holds n (a :: tail) a htheta hstart haLower
      · have haUpper : a ∈ upperHalf n := by
          simp only [segment, lowerHalf, upperHalf, Finset.mem_Icc] at haSegment haLower ⊢
          omega
        let delta := doubledEvenOdd (a :: tail)
        have hconstruction := proposition_2_6_holds n (a :: tail) htheta
        have hdelta : IsTheta (2 * n) delta := by simpa only [delta] using hconstruction.1
        have hdeltaStart : StartsWith delta (2 * a) := by
          apply StartsWith.append
          exact startsWith_evenLift hstart
        let deltaStar := complement (2 * n) delta
        have hstarTheta : IsTheta (2 * n) deltaStar := by
          exact isTheta_complement hdelta
        have hstarStart : StartsWith deltaStar (2 * n + 1 - 2 * a) := by
          exact startsWith_complement hdeltaStart
        have hstarLower : 2 * n + 1 - 2 * a ∈ lowerHalf (2 * n) := by
          simp only [segment, upperHalf, lowerHalf, Finset.mem_Icc] at haSegment haUpper ⊢
          omega
        have hstarBound := lemma_2_4_holds (2 * n) deltaStar (2 * n + 1 - 2 * a)
          hstarTheta hstarStart hstarLower
        calc
          (prologue n (a :: tail)).length = (prologue (2 * n) delta).length := by
            simpa only [delta] using hconstruction.2.1
          _ = (prologue (2 * n) deltaStar).length := by
            simpa only [delta, deltaStar] using hconstruction.2.2
          _ <= 6 := hstarBound

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

/-! ## Interleaving-class enumeration -/

def listInterleavings {α : Type*} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys =>
      (listInterleavings xs (y :: ys)).map (x :: ·) ++
        (listInterleavings (x :: xs) ys).map (y :: ·)
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf


lemma length_listInterleavings {α : Type*} (xs ys : List α) :
    (listInterleavings xs ys).length = Nat.choose (xs.length + ys.length) ys.length := by
  induction xs, ys using listInterleavings.induct with
  | case1 ys => simp [listInterleavings]
  | case2 xs => simp [listInterleavings]
  | case3 x xs y ys ihLeft ihRight =>
      simp only [listInterleavings, List.length_append, List.length_map, ihLeft, ihRight,
        List.length_cons]
      rw [show xs.length + (ys.length + 1) = (xs.length + ys.length) + 1 by omega,
        show xs.length + 1 + ys.length = (xs.length + ys.length) + 1 by omega,
        show xs.length + 1 + (ys.length + 1) = (xs.length + ys.length + 1) + 1 by omega]
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.choose_succ_succ (xs.length + ys.length + 1) ys.length).symm


lemma filters_of_mem_listInterleavings {α : Type*} {p : α → Bool}
    {xs ys word : List α}
    (hxs : ∀ x ∈ xs, p x = true) (hys : ∀ y ∈ ys, p y = false)
    (hword : word ∈ listInterleavings xs ys) :
    word.filter p = xs ∧ word.filter (fun z => !p z) = ys := by
  induction xs, ys using listInterleavings.induct generalizing word with
  | case1 ys =>
      simp only [listInterleavings, List.mem_singleton] at hword
      subst word
      constructor
      · apply List.filter_eq_nil_iff.2
        intro y hy
        simp [hys y hy]
      · apply List.filter_eq_self.2
        intro y hy
        simp [hys y hy]
  | case2 xs =>
      simp only [listInterleavings, List.mem_singleton] at hword
      subst word
      constructor
      · exact List.filter_eq_self.2 hxs
      · apply List.filter_eq_nil_iff.2
        intro x hx
        simp [hxs x hx]
  | case3 x xs y ys ihLeft ihRight =>
      simp only [listInterleavings, List.mem_append, List.mem_map] at hword
      rcases hword with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩
      · have hrec := ihLeft (fun z hz => hxs z (by simp [hz])) hys htail
        simp [hxs x (by simp), hrec]
      · have hrec := ihRight hxs (fun z hz => hys z (by simp [hz])) htail
        simp [hys y (by simp), hrec]

lemma mem_listInterleavings_of_filters {α : Type*} {p : α → Bool}
    {xs ys word : List α}
    (hxs : ∀ x ∈ xs, p x = true) (hys : ∀ y ∈ ys, p y = false)
    (hfirst : word.filter p = xs) (hsecond : word.filter (fun z => !p z) = ys) :
    word ∈ listInterleavings xs ys := by
  induction xs, ys using listInterleavings.induct generalizing word with
  | case1 ys =>
      have hpFalse : ∀ z ∈ word, p z = false := by
        intro z hz
        by_contra hp
        have hpTrue : p z = true := Bool.eq_true_of_not_eq_false hp
        have : z ∈ word.filter p := List.mem_filter.2 ⟨hz, hpTrue⟩
        simp [hfirst] at this
      have hcomp : word.filter (fun z => !p z) = word := by
        apply List.filter_eq_self.2
        intro z hz
        simp [hpFalse z hz]
      have : word = ys := hcomp.symm.trans hsecond
      subst word
      simp [listInterleavings]
  | case2 xs =>
      have hpTrue : ∀ z ∈ word, p z = true := by
        intro z hz
        by_contra hp
        have hpFalse : p z = false := Bool.eq_false_of_not_eq_true hp
        have : z ∈ word.filter (fun a => !p a) := by
          exact List.mem_filter.2 ⟨hz, by simp [hpFalse]⟩
        simp [hsecond] at this
      have : word = xs := (List.filter_eq_self.2 hpTrue).symm.trans hfirst
      subst word
      simp [listInterleavings]
  | case3 x xs y ys ihLeft ihRight =>
      cases word with
      | nil => simp at hfirst
      | cons z word =>
          by_cases hz : p z = true
          · simp only [List.filter_cons_of_pos hz] at hfirst
            have hzx : z = x := by exact List.cons.inj hfirst |>.1
            have htailFirst : word.filter p = xs := List.cons.inj hfirst |>.2
            have htailSecond : word.filter (fun a => !p a) = y :: ys := by
              simpa [hz] using hsecond
            subst z
            simp only [listInterleavings, List.mem_append, List.mem_map]
            left
            exact ⟨word, ihLeft (fun a ha => hxs a (by simp [ha])) hys
              htailFirst htailSecond, rfl⟩
          · have hzFalse : p z = false := Bool.eq_false_of_not_eq_true hz
            have htailFirst : word.filter p = x :: xs := by
              simpa [hzFalse] using hfirst
            have hsecondCons : z :: word.filter (fun a => !p a) = y :: ys := by
              simpa [hzFalse] using hsecond
            have hzy : z = y := by exact List.cons.inj hsecondCons |>.1
            have htailSecond : word.filter (fun a => !p a) = ys :=
              List.cons.inj hsecondCons |>.2
            subst z
            simp only [listInterleavings, List.mem_append, List.mem_map]
            right
            exact ⟨word, ihRight hxs (fun a ha => hys a (by simp [ha]))
              htailFirst htailSecond, rfl⟩

lemma mem_listInterleavings_iff_filters {α : Type*} {p : α → Bool}
    {xs ys word : List α}
    (hxs : ∀ x ∈ xs, p x = true) (hys : ∀ y ∈ ys, p y = false) :
    word ∈ listInterleavings xs ys ↔
      word.filter p = xs ∧ word.filter (fun z => !p z) = ys :=
  ⟨filters_of_mem_listInterleavings hxs hys,
    fun h => mem_listInterleavings_of_filters hxs hys h.1 h.2⟩

lemma nodup_listInterleavings {α : Type*} [DecidableEq α] {xs ys : List α}
    (hxs : xs.Nodup) (hys : ys.Nodup) (hdisjoint : List.Disjoint xs ys) :
    (listInterleavings xs ys).Nodup := by
  revert hxs hys hdisjoint
  induction xs, ys using listInterleavings.induct with
  | case1 ys => intro; simp [listInterleavings]
  | case2 xs => intro; simp [listInterleavings]
  | case3 x xs y ys ihLeft ihRight =>
      intro hxs hys hdisjoint
      have hxNodup := hxs.of_cons
      have hyNodup := hys.of_cons
      have hxNotXs := (List.nodup_cons.1 hxs).1
      have hyNotYs := (List.nodup_cons.1 hys).1
      have hxNotY : x ≠ y := by
        intro hxy
        subst y
        have hxMemLeft : x ∈ x :: xs := by simp
        have hxNotRight : x ∉ x :: ys := List.disjoint_left.1 hdisjoint hxMemLeft
        exact hxNotRight (by simp)
      have hdisjointLeft : List.Disjoint xs (y :: ys) := by
        apply List.disjoint_left.2
        intro a ha hmem
        exact List.disjoint_left.1 hdisjoint (by simp [ha]) hmem
      have hdisjointRight : List.Disjoint (x :: xs) ys := by
        apply List.disjoint_left.2
        intro a hmem ha
        exact List.disjoint_left.1 hdisjoint hmem (by simp [ha])
      have hleft := ihLeft hxNodup hys hdisjointLeft
      have hright := ihRight hxs hyNodup hdisjointRight
      rw [listInterleavings]
      apply List.nodup_append.2
      refine ⟨hleft.map ?_, hright.map ?_, ?_⟩
      · intro a b hab
        exact List.cons.inj hab |>.2
      · intro a b hab
        exact List.cons.inj hab |>.2
      · intro left hleftMem right hrightMem heq
        obtain ⟨leftTail, _, rfl⟩ := List.mem_map.1 hleftMem
        obtain ⟨rightTail, _, rfl⟩ := List.mem_map.1 hrightMem
        exact hxNotY (List.cons.inj heq).1

lemma permutationWord_injective {n : Nat} :
    Function.Injective (@permutationWord n) := by
  intro sigma tau hword
  apply Equiv.ext
  intro i
  have hi : (sigma i : Nat) + 1 = (tau i : Nat) + 1 := by
    simpa [permutationWord] using
      congr_arg (fun word : List Nat => word[i.val]?) hword
  apply Fin.ext
  omega

lemma exists_permutationWord_eq_of_isTheta {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    ∃ sigma : Equiv.Perm (Fin n), permutationWord sigma = word := by
  have hnLength : word.length = n := isTheta_length hword
  let f : Fin word.length → Fin n := fun i =>
    ⟨word.get i - 1, by
      have hmem : word.get i ∈ word := List.get_mem word i
      have hsegment := mem_segment_of_mem_of_isTheta hword hmem
      simp only [segment, Finset.mem_Icc] at hsegment
      omega⟩
  have hfInjective : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hiPositive := positive_of_mem_of_isTheta hword (List.get_mem word i)
    have hjPositive := positive_of_mem_of_isTheta hword (List.get_mem word j)
    have hvalues : word.get i = word.get j := by
      have := congr_arg Fin.val hij
      dsimp only [f] at this
      omega
    exact congr_arg Fin.val ((isTheta_nodup hword).get_inj_iff.mp hvalues)
  have hfSurjective : Function.Surjective f := by
    intro z
    have hzSegment : z.val + 1 ∈ segment n := by
      simp only [segment, Finset.mem_Icc]
      omega
    have hzMem := mem_of_mem_segment_of_isTheta hword hzSegment
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hzMem
    refine ⟨i, ?_⟩
    apply Fin.ext
    dsimp only [f]
    rw [hi]
    omega
  let e : Fin word.length ≃ Fin n := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
  let sigma : Equiv.Perm (Fin n) := (finCongr hnLength.symm).trans e
  refine ⟨sigma, ?_⟩
  apply List.ext_get
  · simp [permutationWord, hnLength]
  · intro i hiPermutation hiWord
    have hiFin : i < n := by simpa [permutationWord] using hiPermutation
    have hiEq : (⟨i, hiWord⟩ : Fin word.length) =
        finCongr hnLength.symm ⟨i, hiFin⟩ := by
      apply Fin.ext
      simp
    have heValue : (e (finCongr hnLength.symm ⟨i, hiFin⟩) : Nat) + 1 = word[i] := by
      rw [← hiEq]
      change (word.get ⟨i, hiWord⟩ - 1) + 1 = word[i]
      have hpositive := positive_of_mem_of_isTheta hword (List.get_mem word ⟨i, hiWord⟩)
      have hpositive' : 0 < word[i] := by
        simpa only [List.get_eq_getElem] using hpositive
      simp only [List.get_eq_getElem]
      omega
    simpa [permutationWord, sigma] using heValue

lemma occursLeftOf_cons_iff_of_ne {a x y : Nat} {word : List Nat}
    (hax : a ≠ x) :
    OccursLeftOf (a :: word) x y ↔ OccursLeftOf word x y := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero] at hi
        exact False.elim (hax (Option.some.inj hi))
    | succ i =>
        cases j with
        | zero => omega
        | succ j =>
            refine ⟨i, j, by omega, ?_, ?_⟩
            · simpa only [List.getElem?_cons_succ] using hi
            · simpa only [List.getElem?_cons_succ] using hj
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨i + 1, j + 1, by omega, ?_, ?_⟩
    · simpa only [List.getElem?_cons_succ, Nat.add_eq] using hi
    · simpa only [List.getElem?_cons_succ, Nat.add_eq] using hj

lemma prefix_of_filters_of_allLeft {p : Nat → Bool}
    {xs rest ys word : List Nat}
    (hword : word.Nodup)
    (hxs : ∀ x ∈ xs, p x = true)
    (_hys : ∀ y ∈ ys, p y = false)
    (hfirst : word.filter p = xs ++ rest)
    (hsecond : word.filter (fun z => !p z) = ys)
    (hleft : ∀ x ∈ xs, ∀ y ∈ ys, OccursLeftOf word x y) :
    xs <+: word := by
  induction xs generalizing word with
  | nil => exact List.nil_prefix
  | cons x xs ih =>
      cases word with
      | nil => simp at hfirst
      | cons z word =>
          have hxsTail : ∀ a ∈ xs, p a = true := fun a ha => hxs a (by simp [ha])
          by_cases hz : p z = true
          · have hfirstCons : z :: word.filter p = x :: (xs ++ rest) := by
              simpa [hz] using hfirst
            have hzx : z = x := (List.cons.inj hfirstCons).1
            have hfirstTail : word.filter p = xs ++ rest := (List.cons.inj hfirstCons).2
            have hxHead : p x = true := hxs x (by simp)
            have hsecondTail : word.filter (fun a => !p a) = ys := by
              simpa [hz] using hsecond
            subst z
            have hleftTail : ∀ a ∈ xs, ∀ y ∈ ys, OccursLeftOf word a y := by
              intro a ha y hy
              have haWord : a ∈ word := by
                have haFilter : a ∈ word.filter p := by
                  rw [hfirstTail]
                  simp [ha]
                exact (List.mem_filter.1 haFilter).1
              have hxa : x ≠ a := by
                intro hxa
                subst a
                exact (List.nodup_cons.1 hword).1 haWord
              exact (occursLeftOf_cons_iff_of_ne hxa).1
                (hleft a (by simp [ha]) y hy)
            obtain ⟨tail, htail⟩ :=
              ih hword.of_cons hxsTail hfirstTail hsecondTail hleftTail
            exact ⟨tail, by simp [htail]⟩
          · have hzFalse : p z = false := Bool.eq_false_of_not_eq_true hz
            have hsecondCons : z :: word.filter (fun a => !p a) = ys := by
              simpa [hzFalse] using hsecond
            have hzMem : z ∈ ys := by
              rw [← hsecondCons]
              simp
            have hforced := hleft x (by simp) z hzMem
            have hzHead : (z :: word)[0]? = some z := by simp
            exact False.elim ((not_occursLeftOf_to_head hword hzHead) hforced)

lemma occursLeftOf_reversal_of_occursLeftOf {word : List Nat} {x y : Nat}
    (h : OccursLeftOf word x y) : OccursLeftOf (reversal word) y x := by
  apply occursLeftOf_of_occursLeftOf_reversal (word := reversal word)
  simpa [reversal] using h

lemma suffix_of_filters_of_allLeft {p : Nat → Bool}
    {xs lead suffix word : List Nat}
    (hword : word.Nodup)
    (hxs : ∀ x ∈ xs, p x = true)
    (hsuffix : ∀ y ∈ suffix, p y = false)
    (hfirst : word.filter p = xs)
    (hsecond : word.filter (fun z => !p z) = lead ++ suffix)
    (hleft : ∀ x ∈ xs, ∀ y ∈ suffix, OccursLeftOf word x y) :
    suffix <:+ word := by
  let q : Nat → Bool := fun z => !p z
  have hsuffixQ : ∀ y ∈ suffix.reverse, q y = true := by
    intro y hy
    have hy' : y ∈ suffix := by simpa using hy
    simp [q, hsuffix y hy']
  have hxsQ : ∀ x ∈ xs.reverse, q x = false := by
    intro x hx
    have hx' : x ∈ xs := by simpa using hx
    simp [q, hxs x hx']
  have hfilterQ : (reversal word).filter q = suffix.reverse ++ lead.reverse := by
    simp [q, reversal, hsecond]
  have hfilterNotQ : (reversal word).filter (fun z => !q z) = xs.reverse := by
    simpa [q, reversal] using congr_arg List.reverse hfirst
  have hleftReverse : ∀ y ∈ suffix.reverse, ∀ x ∈ xs.reverse,
      OccursLeftOf (reversal word) y x := by
    intro y hy x hx
    apply occursLeftOf_reversal_of_occursLeftOf
    exact hleft x (by simpa using hx) y (by simpa using hy)
  have hpref : suffix.reverse <+: reversal word :=
    prefix_of_filters_of_allLeft (p := q) (rest := lead.reverse) (ys := xs.reverse)
      (by simpa [reversal] using (List.nodup_reverse.mpr hword)) hsuffixQ hxsQ hfilterQ
      hfilterNotQ hleftReverse
  obtain ⟨front, hfront⟩ := hpref
  refine ⟨front.reverse, ?_⟩
  have := congr_arg List.reverse hfront
  simpa [reversal] using this

lemma eq_fixedPrefix_interleaving_fixedSuffix {p : Nat → Bool}
    {oddFixed oddActive evenActive evenFixed word : List Nat}
    (hword : word.Nodup)
    (hoddFixed : ∀ x ∈ oddFixed, p x = true)
    (hoddActive : ∀ x ∈ oddActive, p x = true)
    (hevenActive : ∀ y ∈ evenActive, p y = false)
    (hevenFixed : ∀ y ∈ evenFixed, p y = false)
    (hoddTrace : word.filter p = oddFixed ++ oddActive)
    (hevenTrace : word.filter (fun z => !p z) = evenActive ++ evenFixed)
    (hfixedBefore : ∀ x ∈ oddFixed, ∀ y ∈ evenActive ++ evenFixed,
      OccursLeftOf word x y)
    (hbeforeFixed : ∀ x ∈ oddFixed ++ oddActive, ∀ y ∈ evenFixed,
      OccursLeftOf word x y) :
    ∃ middle ∈ listInterleavings oddActive evenActive,
      word = oddFixed ++ middle ++ evenFixed := by
  have hprefix : oddFixed <+: word :=
    prefix_of_filters_of_allLeft hword hoddFixed
      (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hevenActive y hy
        · exact hevenFixed y hy)
      hoddTrace hevenTrace hfixedBefore
  have hsuffix : evenFixed <:+ word :=
    suffix_of_filters_of_allLeft hword
      (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hoddFixed x hx
        · exact hoddActive x hx)
      hevenFixed hoddTrace hevenTrace hbeforeFixed
  obtain ⟨after, hafter⟩ := hprefix
  obtain ⟨before, hbefore⟩ := hsuffix
  have hlengthPartition := word.length_eq_length_filter_add p
  rw [hoddTrace, hevenTrace] at hlengthPartition
  have hfixedLength : oddFixed.length + evenFixed.length <= word.length := by
    simp only [List.length_append] at hlengthPartition
    omega
  have hbeforeLength : oddFixed.length <= before.length := by
    have hbeforeTotal := congr_arg List.length hbefore
    simp only [List.length_append] at hbeforeTotal
    omega
  have htakeBefore : before.take oddFixed.length = oddFixed := by
    have htakeWord : word.take oddFixed.length = oddFixed := by
      rw [← hafter]
      simp
    rw [← htakeWord, ← hbefore]
    simp [List.take_append_of_le_length hbeforeLength]
  let middle := before.drop oddFixed.length
  have hbeforeSplit : before = oddFixed ++ middle := by
    calc
      before = before.take oddFixed.length ++ before.drop oddFixed.length :=
        (List.take_append_drop oddFixed.length before).symm
      _ = oddFixed ++ middle := by rw [htakeBefore]
  have hwordSplit : word = oddFixed ++ middle ++ evenFixed := by
    rw [← hbefore, hbeforeSplit, List.append_assoc]
  have hmiddleOdd : middle.filter p = oddActive := by
    rw [hwordSplit, List.filter_append, List.filter_append,
      List.filter_eq_self.2 hoddFixed] at hoddTrace
    have hevenNil : evenFixed.filter p = [] := by
      apply List.filter_eq_nil_iff.2
      intro y hy
      simp [hevenFixed y hy]
    rw [hevenNil, List.append_nil] at hoddTrace
    exact List.append_right_injective oddFixed hoddTrace
  have hmiddleEven : middle.filter (fun z => !p z) = evenActive := by
    rw [hwordSplit, List.filter_append, List.filter_append] at hevenTrace
    have hoddNil : oddFixed.filter (fun z => !p z) = [] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      simp [hoddFixed x hx]
    have hevenSelf : evenFixed.filter (fun z => !p z) = evenFixed := by
      apply List.filter_eq_self.2
      intro y hy
      simp [hevenFixed y hy]
    rw [hoddNil, List.nil_append, hevenSelf] at hevenTrace
    exact List.append_left_injective evenFixed hevenTrace
  refine ⟨middle, ?_, hwordSplit⟩
  exact mem_listInterleavings_of_filters hoddActive hevenActive hmiddleOdd hmiddleEven

lemma lowerPrologue_entry_le_first_of_reflection_mem {n : Nat} {word : List Nat}
    {a : Nat} (hfree : ThreeFree word)
    (hstart : StartsWith word a)
    (hreflect : ∀ x ∈ prologue n word, a < x → 2 * x - a ∈ word)
    {i x : Nat} (hi : i < (prologue n word).length)
    (hx : (prologue n word)[i]? = some x) : x <= a := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
      by_contra hle
      have hax : a < x := by omega
      obtain ⟨suffix, hwordEq⟩ := prologue_prefix n word
      have hxWord : word[i]? = some x := by
        rw [← hwordEq, List.getElem?_append_left hi]
        exact hx
      have hxMemPro : x ∈ prologue n word := List.mem_iff_getElem?.mpr ⟨i, hx⟩
      let r := 2 * x - a
      have hrMem : r ∈ word := hreflect x hxMemPro hax
      obtain ⟨j, hjWord⟩ := List.mem_iff_getElem?.mp hrMem
      have hzero : word[0]? = some a := by
        rw [← List.head?_eq_getElem?]
        exact hstart
      have hiPos : 0 < i := by
        by_contra hiZero
        have hiEq : i = 0 := by omega
        subst i
        have haxEq : a = x := Option.some.inj (hzero.symm.trans hxWord)
        omega
      have hrEq : r = a + 2 * (x - a) := by
        dsimp [r]
        omega
      have hxEq : x = a + (x - a) := by omega
      have hji : j < i := by
        by_contra hnot
        have hij : i < j := by
          obtain ⟨hjLen, _⟩ := List.getElem?_eq_some_iff.mp hjWord
          have hjiNe : j ≠ i := by
            intro hji
            subst j
            have hrx : r = x := Option.some.inj (hjWord.symm.trans hxWord)
            dsimp [r] at hrx
            omega
          omega
        apply hfree
        apply containsThreeAP_of_increasing_positions hiPos hij (by omega : 0 < x - a)
          hzero
        · rw [← hxEq]
          exact hxWord
        · rw [← hrEq]
          exact hjWord
      have hjProBound : j < (prologue n word).length := hji.trans hi
      have hjPro : (prologue n word)[j]? = some r := by
        rw [← hwordEq, List.getElem?_append_left hjProBound] at hjWord
        exact hjWord
      have hrLe := ih j hji hjProBound hjPro
      dsimp [r] at hrLe
      omega

lemma first_le_upperPrologue_entry_of_reflection_mem {n : Nat} {word : List Nat}
    {a : Nat} (hfree : ThreeFree word)
    (hstart : StartsWith word a)
    (haLeN : a <= n)
    (hupper : ∀ z ∈ prologue n word, z ∈ upperHalf n)
    (hreflect : ∀ x ∈ prologue n word, x < a → a <= 2 * x → 2 * x - a ∈ word)
    {i x : Nat} (hi : i < (prologue n word).length)
    (hx : (prologue n word)[i]? = some x) (haTwoX : a <= 2 * x) : a <= x := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
      by_contra hle
      have hxa : x < a := by omega
      obtain ⟨suffix, hwordEq⟩ := prologue_prefix n word
      have hxWord : word[i]? = some x := by
        rw [← hwordEq, List.getElem?_append_left hi]
        exact hx
      have hxMemPro : x ∈ prologue n word := List.mem_iff_getElem?.mpr ⟨i, hx⟩
      let r := 2 * x - a
      have hrMem : r ∈ word := hreflect x hxMemPro hxa haTwoX
      obtain ⟨j, hjWord⟩ := List.mem_iff_getElem?.mp hrMem
      have hzero : word[0]? = some a := by
        rw [← List.head?_eq_getElem?]
        exact hstart
      have hiPos : 0 < i := by
        by_contra hiZero
        have hiEq : i = 0 := by omega
        subst i
        have haxEq : a = x := Option.some.inj (hzero.symm.trans hxWord)
        omega
      have haEq : a = r + 2 * (a - x) := by
        dsimp [r]
        omega
      have hxEq : x = r + (a - x) := by
        dsimp [r]
        omega
      have hji : j < i := by
        by_contra hnot
        have hij : i < j := by
          obtain ⟨hjLen, _⟩ := List.getElem?_eq_some_iff.mp hjWord
          have hjiNe : j ≠ i := by
            intro hji
            subst j
            have hrx : r = x := Option.some.inj (hjWord.symm.trans hxWord)
            dsimp [r] at hrx
            omega
          omega
        apply hfree
        apply containsThreeAP_of_decreasing_positions hiPos hij (by omega : 0 < a - x)
        · rw [← haEq]
          exact hzero
        · rw [← hxEq]
          exact hxWord
        · exact hjWord
      have hjProBound : j < (prologue n word).length := hji.trans hi
      have hjPro : (prologue n word)[j]? = some r := by
        rw [← hwordEq, List.getElem?_append_left hjProBound] at hjWord
        exact hjWord
      have hrUpper := hupper r (List.mem_iff_getElem?.mpr ⟨j, hjPro⟩)
      have haLeR : a <= r := ih j hji hjProBound hjPro (by
        simp only [upperHalf, Finset.mem_Icc] at hrUpper
        omega)
      dsimp [r] at haLeR
      omega

lemma mem_upperHalf_of_mem_prologue {n : Nat} {word : List Nat} {a x : Nat}
    (hstart : StartsWith word a) (haUpper : a ∈ upperHalf n)
    (hx : x ∈ prologue n word) : x ∈ upperHalf n := by
  classical
  cases word with
  | nil => simp [StartsWith] at hstart
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using hstart
      subst first
      simp only [prologue, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact haUpper
      · have hsame : SameHalf n a x := by
          have hp := List.mem_takeWhile_imp
            (p := fun y : Nat => decide (SameHalf n a y)) (l := tail) hx
          exact of_decide_eq_true hp
        rcases hsame with hLower | hUpper
        · simp only [lowerHalf, upperHalf, Finset.mem_Icc] at haUpper hLower
          omega
        · exact hUpper.2

lemma oddTrace_threeFree {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    ThreeFree (oddTrace word) := by
  rw [← oddLift_oddBase]
  apply threeFree_oddLift (isTheta_threeFree (isTheta_oddBase hword))
  intro x hx
  exact positive_of_mem_of_isTheta (isTheta_oddBase hword) hx

lemma evenTrace_threeFree {n : Nat} {word : List Nat} (hword : IsTheta n word) :
    ThreeFree (evenTrace word) := by
  rw [← evenLift_evenBase]
  exact threeFree_evenLift (isTheta_threeFree (isTheta_evenBase hword))

lemma oddEpilogue_entry_le_last {n : Nat} {gamma : List Nat} {last x : Nat}
    (htheta : IsTheta n gamma) (hlast : EndsWith (oddTrace gamma) last)
    (hlastLower : last ∈ lowerHalf n) (hx : x ∈ epilogue n (oddTrace gamma)) :
    x <= last := by
  let word := reversal (oddTrace gamma)
  have hstart : StartsWith word last := startsWith_reversal_of_endsWith hlast
  have hfree : ThreeFree word := by
    exact threeFree_reverse (oddTrace_threeFree htheta)
  have hxWord : x ∈ prologue n word := by simpa [word, epilogue] using hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxWord
  obtain ⟨hiLength, _⟩ := List.getElem?_eq_some_iff.mp hi
  refine lowerPrologue_entry_le_first_of_reflection_mem hfree hstart
    (i := i) ?_ hiLength hi
  intro z hz hlz
  have hzLower := mem_lowerHalf_of_mem_prologue hstart hlastLower hz
  have hlastOdd : Odd last := by
    have hlastMem : last ∈ oddTrace gamma := by
      apply List.mem_of_mem_getLast?
      rw [hlast]
      simp
    exact of_decide_eq_true (List.mem_filter.1 hlastMem).2
  have hzOdd : Odd z := by
    have hzReverse : z ∈ reversal (oddTrace gamma) :=
      (prologue_prefix n word).mem (by simpa [word] using hz)
    have hzTrace : z ∈ oddTrace gamma := by simpa [reversal] using hzReverse
    exact of_decide_eq_true (List.mem_filter.1 hzTrace).2
  have hreflectSegment : 2 * z - last ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hzLower hlastLower ⊢
    omega
  have hreflectOdd : Odd (2 * z - last) := by
    rcases hlastOdd with ⟨a, ha⟩
    rcases hzOdd with ⟨b, hb⟩
    refine ⟨2 * b - a, ?_⟩
    omega
  have hreflectGamma := mem_of_mem_segment_of_isTheta htheta hreflectSegment
  have hreflectTrace : 2 * z - last ∈ oddTrace gamma := by
    exact List.mem_filter.2 ⟨hreflectGamma, decide_eq_true hreflectOdd⟩
  dsimp only [word, reversal]
  simpa using hreflectTrace

lemma evenPrologue_first_le_entry {n : Nat} {gamma : List Nat} {first y : Nat}
    (htheta : IsTheta n gamma) (hfirst : StartsWith (evenTrace gamma) first)
    (hfirstUpper : first ∈ upperHalf n) (hy : y ∈ prologue n (evenTrace gamma)) :
    first <= y := by
  have hfree := evenTrace_threeFree htheta
  have hupper : ∀ z ∈ prologue n (evenTrace gamma), z ∈ upperHalf n :=
    fun z hz => mem_upperHalf_of_mem_prologue hfirst hfirstUpper hz
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨hiLength, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hfirstBounds := Finset.mem_Icc.1
    (show first ∈ Finset.Icc (n / 2 + 1) n from hfirstUpper)
  refine first_le_upperPrologue_entry_of_reflection_mem hfree hfirst
    hfirstBounds.2 hupper ?_ (i := i) hiLength hi ?_
  · intro z hz hzf hfirstTwo
    have hzUpper := hupper z hz
    have hfirstEven : Even first := by
      have hfirstMem : first ∈ evenTrace gamma := by
        cases h : evenTrace gamma with
        | nil => simp [StartsWith, h] at hfirst
        | cons a as =>
            have ha : a = first := by simpa [StartsWith, h] using hfirst
            simp [ha]
      exact of_decide_eq_true (List.mem_filter.1 hfirstMem).2
    have hzEven : Even z := by
      have hzTrace := (prologue_prefix n (evenTrace gamma)).mem hz
      exact of_decide_eq_true (List.mem_filter.1 hzTrace).2
    have hreflectSegment : 2 * z - first ∈ segment n := by
      simp only [upperHalf, segment, Finset.mem_Icc] at hzUpper hfirstUpper ⊢
      omega
    have hreflectEven : Even (2 * z - first) := by
      rcases hfirstEven with ⟨a, ha⟩
      rcases hzEven with ⟨b, hb⟩
      refine ⟨2 * b - a, ?_⟩
      omega
    unfold evenTrace trace
    exact List.mem_filter.2
      ⟨mem_of_mem_segment_of_isTheta htheta hreflectSegment,
        decide_eq_true hreflectEven⟩
  · simp only [upperHalf, Finset.mem_Icc] at hfirstUpper
    have hyUpper := hupper y hy
    simp only [upperHalf, Finset.mem_Icc] at hyUpper
    omega

def oddFixedBlock (n : Nat) (gammaOdd : List Nat) : List Nat :=
  ((reversal gammaOdd).drop (epilogue n gammaOdd).length).reverse

def oddActiveBlock (n : Nat) (gammaOdd : List Nat) : List Nat :=
  (epilogue n gammaOdd).reverse

def evenActiveBlock (n : Nat) (gammaEven : List Nat) : List Nat :=
  prologue n gammaEven

def evenFixedBlock (n : Nat) (gammaEven : List Nat) : List Nat :=
  gammaEven.drop (prologue n gammaEven).length

def admissibleInterleavingWords (n : Nat) (gammaOdd gammaEven : List Nat) :
    List (List Nat) :=
  (listInterleavings (oddActiveBlock n gammaOdd) (evenActiveBlock n gammaEven)).map
    fun middle => oddFixedBlock n gammaOdd ++ middle ++ evenFixedBlock n gammaEven

lemma prologue_append_drop (n : Nat) (word : List Nat) :
    prologue n word ++ word.drop (prologue n word).length = word := by
  obtain ⟨suffix, hsuffix⟩ := prologue_prefix n word
  have hdrop : word.drop (prologue n word).length = suffix := by
    calc
      word.drop (prologue n word).length =
          (prologue n word ++ suffix).drop (prologue n word).length :=
        congr_arg (fun list => list.drop (prologue n word).length) hsuffix.symm
      _ = suffix := List.drop_left
  rw [hdrop, hsuffix]

lemma oddFixed_append_oddActive (n : Nat) (gammaOdd : List Nat) :
    oddFixedBlock n gammaOdd ++ oddActiveBlock n gammaOdd = gammaOdd := by
  have hsplit := prologue_append_drop n (reversal gammaOdd)
  have hreverse := congr_arg List.reverse hsplit
  simpa [oddFixedBlock, oddActiveBlock, epilogue, reversal] using hreverse

lemma evenActive_append_evenFixed (n : Nat) (gammaEven : List Nat) :
    evenActiveBlock n gammaEven ++ evenFixedBlock n gammaEven = gammaEven := by
  exact prologue_append_drop n gammaEven

lemma oddActiveBlock_length (n : Nat) (gammaOdd : List Nat) :
    (oddActiveBlock n gammaOdd).length = (epilogue n gammaOdd).length := by
  simp [oddActiveBlock]

lemma evenActiveBlock_length (n : Nat) (gammaEven : List Nat) :
    (evenActiveBlock n gammaEven).length = (prologue n gammaEven).length := by
  rfl

lemma first_after_prologue_not_sameHalf {n : Nat} {word : List Nat} {first next : Nat}
    (hfirst : StartsWith word first)
    (hnext : StartsWith (word.drop (prologue n word).length) next) :
    ¬ SameHalf n first next := by
  classical
  cases word with
  | nil => simp [StartsWith] at hfirst
  | cons a tail =>
      have ha : a = first := by simpa [StartsWith] using hfirst
      subst a
      let p := fun y : Nat => decide (SameHalf n first y)
      have hdrop : (first :: tail).drop (prologue n (first :: tail)).length =
          tail.dropWhile p := by
        simp only [prologue, List.length_cons, List.drop_succ_cons]
        dsimp only [p]
        let q := fun y : Nat => decide (SameHalf n first y)
        have hsplit : tail.takeWhile q ++ tail.dropWhile q = tail :=
          List.takeWhile_append_dropWhile
        have hdropTail : tail.drop (tail.takeWhile q).length = tail.dropWhile q := by
          calc
            tail.drop (tail.takeWhile q).length =
                (tail.takeWhile q ++ tail.dropWhile q).drop (tail.takeWhile q).length :=
              congr_arg (fun list => list.drop (tail.takeWhile q).length) hsplit.symm
            _ = tail.dropWhile q := by
              exact List.drop_left
        simpa [q] using hdropTail
      rw [hdrop] at hnext
      have hzero : (tail.dropWhile p)[0]? = some next := by
        rw [← List.head?_eq_getElem?]
        exact hnext
      obtain ⟨hpos, hget⟩ := List.getElem?_eq_some_iff.mp hzero
      have hnot := List.dropWhile_get_zero_not p tail hpos
      have hget' : (tail.dropWhile p).get ⟨0, hpos⟩ = next := by
        simpa only [List.get_eq_getElem] using hget
      rw [hget'] at hnot
      intro hsame
      exact hnot (by simpa [p] using decide_eq_true hsame)

/-! ## Connectivity of binary interleavings -/

inductive CrossSwapReach {α : Type*} (xs ys : List α) :
    List α → List α → Prop
  | refl (word : List α) : CrossSwapReach xs ys word word
  | step {start current pre tail : List α} {x y : α} :
      CrossSwapReach xs ys start current →
      x ∈ xs → y ∈ ys →
      current = pre ++ x :: y :: tail →
      CrossSwapReach xs ys start (pre ++ y :: x :: tail)

lemma CrossSwapReach.trans {α : Type*} {xs ys a b c : List α}
    (hab : CrossSwapReach xs ys a b) (hbc : CrossSwapReach xs ys b c) :
    CrossSwapReach xs ys a c := by
  induction hbc with
  | refl => exact hab
  | step h hx hy hcurrent ih =>
      exact CrossSwapReach.step ih hx hy hcurrent

lemma CrossSwapReach.cons {α : Type*} {xs ys a b : List α} (z : α)
    (hab : CrossSwapReach xs ys a b) :
    CrossSwapReach xs ys (z :: a) (z :: b) := by
  induction hab with
  | refl => exact CrossSwapReach.refl _
  | @step current pre tail x y h hx hy hcurrent ih =>
      apply CrossSwapReach.step (pre := z :: pre) ih hx hy
      simpa only [List.cons_append] using congrArg (List.cons z) hcurrent

lemma CrossSwapReach.prefix {α : Type*} {xs ys a b : List α} (pre : List α)
    (hab : CrossSwapReach xs ys a b) :
    CrossSwapReach xs ys (pre ++ a) (pre ++ b) := by
  induction pre with
  | nil => simpa using hab
  | cons z pre ih => simpa only [List.cons_append] using CrossSwapReach.cons z ih

lemma CrossSwapReach.suffix {α : Type*} {xs ys a b : List α} (tail : List α)
    (hab : CrossSwapReach xs ys a b) :
    CrossSwapReach xs ys (a ++ tail) (b ++ tail) := by
  induction hab with
  | refl => exact CrossSwapReach.refl _
  | @step current pre rest x y h hx hy hcurrent ih =>
      have hstep := CrossSwapReach.step (pre := pre) (tail := rest ++ tail) ih hx hy (by
        rw [hcurrent]
        simp only [List.append_assoc, List.cons_append])
      simpa only [List.append_assoc, List.cons_append] using hstep

lemma CrossSwapReach.mono {α : Type*}
    {xs ys xs' ys' a b : List α}
    (hxs : ∀ x ∈ xs, x ∈ xs') (hys : ∀ y ∈ ys, y ∈ ys')
    (hab : CrossSwapReach xs ys a b) : CrossSwapReach xs' ys' a b := by
  induction hab with
  | refl => exact CrossSwapReach.refl _
  | step h hx hy hcurrent ih =>
      exact CrossSwapReach.step ih (hxs _ hx) (hys _ hy) hcurrent

lemma CrossSwapReach.bubble {α : Type*} {allXs allYs xs suffix : List α}
    {y : α} (hxs : ∀ x ∈ xs, x ∈ allXs) (hy : y ∈ allYs) :
    CrossSwapReach allXs allYs (xs ++ y :: suffix) (y :: xs ++ suffix) := by
  induction xs with
  | nil => exact CrossSwapReach.refl _
  | cons x xs ih =>
      have htail := CrossSwapReach.cons x
        (ih (fun z hz => hxs z (by simp [hz])))
      have hstep : CrossSwapReach allXs allYs
          (x :: (xs ++ y :: suffix)) (y :: x :: xs ++ suffix) := by
        apply CrossSwapReach.step (pre := []) htail (hxs x (by simp)) hy
        rfl
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using hstep

lemma crossSwapReach_of_mem_listInterleavings {α : Type*}
    {xs ys word : List α} (hword : word ∈ listInterleavings xs ys) :
    CrossSwapReach xs ys (xs ++ ys) word := by
  induction xs, ys using listInterleavings.induct generalizing word with
  | case1 ys =>
      simp only [listInterleavings, List.mem_singleton] at hword
      subst word
      exact CrossSwapReach.refl _
  | case2 xs =>
      simp only [listInterleavings, List.mem_singleton] at hword
      subst word
      simpa using (CrossSwapReach.refl xs : CrossSwapReach xs [] xs xs)
  | case3 x xs y ys ihLeft ihRight =>
      simp only [listInterleavings, List.mem_append, List.mem_map] at hword
      rcases hword with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩
      · have hreach := CrossSwapReach.cons x
          ((ihLeft htail).mono (fun z hz => List.mem_cons_of_mem x hz) (fun z hz => hz))
        simpa only [List.cons_append] using hreach
      · have hbubble : CrossSwapReach (x :: xs) (y :: ys)
            ((x :: xs) ++ y :: ys) (y :: (x :: xs) ++ ys) :=
          CrossSwapReach.bubble
            (allXs := x :: xs) (allYs := y :: ys)
            (fun z hz => hz) (by simp)
        have htailReach := CrossSwapReach.cons y
          ((ihRight htail).mono (fun z hz => hz) (fun z hz => List.mem_cons_of_mem y hz))
        exact hbubble.trans htailReach

lemma swapValues_adjacent_eq {pre tail : List Nat} {x y : Nat}
    (hnodup : (pre ++ x :: y :: tail).Nodup) :
    swapValues x y (pre ++ x :: y :: tail) =
      pre ++ y :: x :: tail := by
  have happ := List.nodup_append.mp hnodup
  have htail := List.nodup_cons.mp happ.2.1
  have hytail := List.nodup_cons.mp htail.2
  have hxy : x ≠ y := by
    intro h
    apply htail.1
    simp [h]
  have hprefixX : ∀ z ∈ pre, z ≠ x := by
    intro z hz
    exact happ.2.2 z hz x (by simp)
  have hprefixY : ∀ z ∈ pre, z ≠ y := by
    intro z hz
    exact happ.2.2 z hz y (by simp)
  have hsuffixX : ∀ z ∈ tail, z ≠ x := by
    intro z hz hzx
    subst z
    exact htail.1 (by simp [hz])
  have hsuffixY : ∀ z ∈ tail, z ≠ y := by
    intro z hz hzy
    subst z
    exact hytail.1 hz
  have hprefixMap : pre.map (swapEntry x y) = pre := by
    calc
      pre.map (swapEntry x y) = pre.map id := by
        apply List.map_congr_left
        intro z hz
        simp [swapEntry, hprefixX z hz, hprefixY z hz]
      _ = pre := List.map_id pre
  have hsuffixMap : tail.map (swapEntry x y) = tail := by
    calc
      tail.map (swapEntry x y) = tail.map id := by
        apply List.map_congr_left
        intro z hz
        simp [swapEntry, hsuffixX z hz, hsuffixY z hz]
      _ = tail := List.map_id tail
  simp [swapValues_eq_map_swapEntry, hprefixMap, hsuffixMap, hxy]

lemma isTheta12_of_crossSwapReach {n : Nat} {xs ys start word : List Nat}
    (hreach : CrossSwapReach xs ys start word)
    (hstart : IsTheta12 n start)
    (hxsSegment : ∀ x ∈ xs, x ∈ segment n)
    (hysSegment : ∀ y ∈ ys, y ∈ segment n)
    (hxsOdd : ∀ x ∈ xs, Odd x)
    (hysEven : ∀ y ∈ ys, Even y)
    (hcommute : ∀ x ∈ xs, ∀ y ∈ ys, Commute n x y) :
    IsTheta12 n word := by
  induction hreach with
  | refl => exact hstart
  | @step current pre tail x y h hx hy hcurrent ih =>
      have hadjacent : ImmediatelyLeftOf current x y := by
        rw [hcurrent]
        refine ⟨pre.length, ?_, ?_⟩ <;> simp
      have hswapped := proposition_2_7_holds n x y current
        (hxsSegment x hx) (hysSegment y hy) (hxsOdd x hx) (hysEven y hy)
        ih (hcommute x hx y hy) hadjacent
      have hnodupCurrent := isTheta_nodup ih.1
      rw [hcurrent] at hnodupCurrent
      have hswapEq : swapValues x y current = pre ++ y :: x :: tail := by
        rw [hcurrent]
        exact swapValues_adjacent_eq hnodupCurrent
      rwa [hswapEq] at hswapped

lemma isTheta12_of_mem_listInterleavings {n : Nat}
    {fixedPrefix fixedSuffix xs ys word : List Nat}
    (hcanonical : IsTheta12 n (fixedPrefix ++ (xs ++ ys) ++ fixedSuffix))
    (hxsSegment : ∀ x ∈ xs, x ∈ segment n)
    (hysSegment : ∀ y ∈ ys, y ∈ segment n)
    (hxsOdd : ∀ x ∈ xs, Odd x)
    (hysEven : ∀ y ∈ ys, Even y)
    (hcommute : ∀ x ∈ xs, ∀ y ∈ ys, Commute n x y)
    (hword : word ∈ listInterleavings xs ys) :
    IsTheta12 n (fixedPrefix ++ word ++ fixedSuffix) := by
  have hreach := (crossSwapReach_of_mem_listInterleavings hword).prefix fixedPrefix
  have hreach' := hreach.suffix fixedSuffix
  simpa only [List.append_assoc] using
    isTheta12_of_crossSwapReach hreach' hcanonical hxsSegment hysSegment
      hxsOdd hysEven hcommute

lemma odd_even_not_modEq_two {x y : Nat} (hx : Odd x) (hy : Even y) :
    ¬ Nat.ModEq 2 x y := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  unfold Nat.ModEq
  omega

lemma isTheta12_oddTrace_append_evenTrace {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta12 n gamma) :
    IsTheta12 n (oddTrace gamma ++ evenTrace gamma) := by
  have hoddNodup : (oddTrace gamma).Nodup := (isTheta_nodup hgamma.1).filter _
  have hevenNodup : (evenTrace gamma).Nodup := (isTheta_nodup hgamma.1).filter _
  have hdisjoint : ∀ x ∈ oddTrace gamma, ∀ y ∈ evenTrace gamma, x ≠ y := by
    intro x hx y hy hxy
    subst y
    have hxOdd : Odd x := of_decide_eq_true (List.mem_filter.mp hx).2
    have hxEven : Even x := of_decide_eq_true (List.mem_filter.mp hy).2
    exact (Nat.not_even_iff_odd.mpr hxOdd) hxEven
  have hperm : Permutes (segment n) (oddTrace gamma ++ evenTrace gamma) := by
    constructor
    · exact List.nodup_append.mpr ⟨hoddNodup, hevenNodup, hdisjoint⟩
    · apply Finset.ext
      intro z
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset]
      rw [← hgamma.1.1.2, List.mem_toFinset]
      simp only [oddTrace, evenTrace, trace, List.mem_filter]
      constructor
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
      · intro hz
        rcases Nat.even_or_odd z with hzEven | hzOdd
        · exact Or.inr ⟨hz, decide_eq_true hzEven⟩
        · exact Or.inl ⟨hz, decide_eq_true hzOdd⟩
  have hfree : ThreeFree (oddTrace gamma ++ evenTrace gamma) := by
    apply threeFree_append_of_mod_two_separated
    · exact oddTrace_threeFree hgamma.1
    · exact evenTrace_threeFree hgamma.1
    · intro x hx y hy
      exact odd_even_not_modEq_two
        (of_decide_eq_true (List.mem_filter.mp hx).2)
        (of_decide_eq_true (List.mem_filter.mp hy).2)
  refine ⟨⟨hperm, hfree⟩, ?_⟩
  rcases hgamma.2 with ⟨first, hfirst, hfirstOdd⟩
  have htraceFirst : StartsWith (oddTrace gamma) first := by
    cases gamma with
    | nil => simp [StartsWith] at hfirst
    | cons x xs =>
        have hx : x = first := by simpa [StartsWith] using hfirst
        subst x
        simp [StartsWith, oddTrace, trace, decide_eq_true hfirstOdd]
  exact ⟨first, htraceFirst.append, hfirstOdd⟩

lemma mem_of_startsWith {word : List Nat} {x : Nat} (h : StartsWith word x) :
    x ∈ word := by
  cases word with
  | nil => simp [StartsWith] at h
  | cons y ys =>
      have hy : y = x := by simpa [StartsWith] using h
      simp [hy]

lemma mem_of_endsWith {word : List Nat} {x : Nat} (h : EndsWith word x) :
    x ∈ word := by
  apply List.mem_of_mem_getLast?
  rw [h]
  simp

lemma occursLeftOf_of_mem_of_endsWith {word : List Nat} {last x : Nat}
    (hword : word.Nodup) (hlast : EndsWith word last) (hx : x ∈ word)
    (hne : x ≠ last) : OccursLeftOf word x last := by
  have hreverseNodup : (reversal word).Nodup := by
    simpa [reversal] using List.nodup_reverse.mpr hword
  have hxReverse : x ∈ reversal word := by simpa [reversal] using hx
  have hreverse := occursLeftOf_of_startsWith_of_mem hreverseNodup
    (startsWith_reversal_of_endsWith hlast) hxReverse hne.symm
  exact occursLeftOf_of_occursLeftOf_reversal hreverse

lemma three_le_of_standingInterleavingHypotheses {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) : 3 ≤ n := by
  rcases hstanding with
    ⟨hgamma12, b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hbSegment : b1 ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
    omega
  have hcSegment : c1 ∈ segment n := by
    simp only [upperHalf, segment, Finset.mem_Icc] at hcUpper ⊢
    omega
  have hbOdd : Odd b1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hcEven : Even c1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_startsWith hcStart)).2
  by_contra hn
  have hnTwo : n = 2 := by
    simp only [lowerHalf, Finset.mem_Icc] at hbLower
    omega
  have hbOne : b1 = 1 := by
    simp only [hnTwo, segment, Finset.mem_Icc] at hbSegment
    rcases hbOdd with ⟨b, hb⟩
    omega
  have hcTwo : c1 = 2 := by
    simp only [hnTwo, segment, Finset.mem_Icc] at hcSegment
    rcases hcEven with ⟨c, hc⟩
    omega
  subst b1
  subst c1
  rcases hcommute with ⟨beta, hbeta12, htwoOne⟩
  have honeSegment : 1 ∈ segment n := by simp [hnTwo, segment]
  have htwoSegment : 2 ∈ segment n := by simp [hnTwo, segment]
  have honeTwo :=
    (proposition_2_3_holds n beta 1 hbeta12 honeSegment htwoSegment).1 (by norm_num)
  exact (occursLeftOf_asymm (isTheta_nodup hbeta12.1) honeTwo) htwoOne

lemma oddActiveBlock_mem_oddTrace {n : Nat} {word : List Nat} {x : Nat}
    (hx : x ∈ oddActiveBlock n (oddTrace word)) : x ∈ oddTrace word := by
  have hxEpilogue : x ∈ epilogue n (oddTrace word) := by
    simpa [oddActiveBlock] using hx
  have hxReverse : x ∈ reversal (oddTrace word) :=
    (prologue_prefix n (reversal (oddTrace word))).mem (by
      simpa [epilogue] using hxEpilogue)
  simpa [reversal] using hxReverse

lemma evenActiveBlock_mem_evenTrace {n : Nat} {word : List Nat} {y : Nat}
    (hy : y ∈ evenActiveBlock n (evenTrace word)) : y ∈ evenTrace word := by
  exact (prologue_prefix n (evenTrace word)).mem (by
    simpa [evenActiveBlock] using hy)

lemma activeBlocks_commute {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ oddActiveBlock n (oddTrace gamma),
      ∀ y ∈ evenActiveBlock n (evenTrace gamma), Commute n x y := by
  rcases hstanding with
    ⟨hgamma12, b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hn : 3 ≤ n := three_le_of_standingInterleavingHypotheses
    ⟨hgamma12, b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hbSegment : b1 ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
    omega
  have hcSegment : c1 ∈ segment n := by
    simp only [upperHalf, segment, Finset.mem_Icc] at hcUpper ⊢
    omega
  have hbOdd : Odd b1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hcEven : Even c1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_startsWith hcStart)).2
  have hnotDoNotCommute : ¬ DoNotCommute n b1 c1 := by
    intro hdo
    rcases hcommute with ⟨witness, hwitness12, hreverse⟩
    exact (occursLeftOf_asymm (isTheta_nodup hwitness12.1)
      (hdo witness hwitness12)) hreverse
  have hnoBoundaryReflections :
      ¬ ((c1 ≤ 2 * b1 ∧ 2 * b1 - c1 ∈ segment n) ∨
        (b1 ≤ 2 * c1 ∧ 2 * c1 - b1 ∈ segment n)) := by
    intro hreflections
    exact hnotDoNotCommute
      ((theorem_2_2_holds n b1 c1 hn hbSegment hcSegment hbOdd hcEven).2 hreflections)
  have hseparated : 2 * b1 ≤ c1 := by
    by_contra hnot
    apply hnoBoundaryReflections
    left
    constructor
    · omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, Finset.mem_Icc] at hbLower
      rcases hbOdd with ⟨b, hb⟩
      rcases hcEven with ⟨c, hc⟩
      omega
  have hreflectionAbove : n < 2 * c1 - b1 := by
    by_contra hnot
    apply hnoBoundaryReflections
    right
    constructor
    · simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hbLower hcUpper
      omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hbLower hcUpper
      omega
  intro x hx y hy
  have hxTrace := oddActiveBlock_mem_oddTrace hx
  have hyTrace := evenActiveBlock_mem_evenTrace hy
  have hxGamma : x ∈ gamma := (List.mem_filter.mp hxTrace).1
  have hyGamma : y ∈ gamma := (List.mem_filter.mp hyTrace).1
  have hxSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hxGamma
  have hySegment := mem_segment_of_mem_of_isTheta hgamma12.1 hyGamma
  have hxOdd : Odd x := of_decide_eq_true (List.mem_filter.mp hxTrace).2
  have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hyTrace).2
  have hxLe : x ≤ b1 := oddEpilogue_entry_le_last hgamma12.1 hbEnd hbLower (by
    simpa [oddActiveBlock] using hx)
  have hyLe : c1 ≤ y := evenPrologue_first_le_entry hgamma12.1 hcStart hcUpper (by
    simpa [evenActiveBlock] using hy)
  have hnoReflections :
      ¬ ((y ≤ 2 * x ∧ 2 * x - y ∈ segment n) ∨
        (x ≤ 2 * y ∧ 2 * y - x ∈ segment n)) := by
    rintro (⟨_, hreflect⟩ | ⟨_, hreflect⟩)
    · simp only [segment, Finset.mem_Icc] at hreflect
      omega
    · simp only [segment, Finset.mem_Icc] at hreflect
      omega
  exact exists_theta12_reverse_pair_of_no_reflections hn hxSegment hySegment
    hxOdd hyEven hnoReflections

lemma admissibleInterleaving_isTheta12 {n : Nat} {gamma middle : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hmiddle : middle ∈ listInterleavings
      (oddActiveBlock n (oddTrace gamma))
      (evenActiveBlock n (evenTrace gamma))) :
    IsTheta12 n
      (oddFixedBlock n (oddTrace gamma) ++ middle ++
        evenFixedBlock n (evenTrace gamma)) := by
  have hgamma12 := hstanding.1
  have hcanonicalTrace := isTheta12_oddTrace_append_evenTrace hgamma12
  have hcanonical : IsTheta12 n
      (oddFixedBlock n (oddTrace gamma) ++
        (oddActiveBlock n (oddTrace gamma) ++
          evenActiveBlock n (evenTrace gamma)) ++
        evenFixedBlock n (evenTrace gamma)) := by
    rw [← List.append_assoc (oddFixedBlock n (oddTrace gamma)),
      oddFixed_append_oddActive, List.append_assoc,
      evenActive_append_evenFixed]
    exact hcanonicalTrace
  apply isTheta12_of_mem_listInterleavings hcanonical
  · intro x hx
    have hxTrace := oddActiveBlock_mem_oddTrace hx
    exact mem_segment_of_mem_of_isTheta hgamma12.1 (List.mem_filter.mp hxTrace).1
  · intro y hy
    have hyTrace := evenActiveBlock_mem_evenTrace hy
    exact mem_segment_of_mem_of_isTheta hgamma12.1 (List.mem_filter.mp hyTrace).1
  · intro x hx
    exact of_decide_eq_true (List.mem_filter.mp (oddActiveBlock_mem_oddTrace hx)).2
  · intro y hy
    exact of_decide_eq_true (List.mem_filter.mp (evenActiveBlock_mem_evenTrace hy)).2
  · exact activeBlocks_commute hstanding
  · exact hmiddle

lemma oddFixed_before_evenTrace {n : Nat} {gamma beta : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hbeta12 : IsTheta12 n beta)
    (hoddTrace : oddTrace beta = oddTrace gamma)
    (hevenTrace : evenTrace beta = evenTrace gamma) :
    ∀ x ∈ oddFixedBlock n (oddTrace gamma),
      ∀ y ∈ evenTrace gamma, OccursLeftOf beta x y := by
  rcases hstanding with
    ⟨hgamma12, b1, c1, hbEnd, hcStart, _hcommute, hbLower, hcUpper⟩
  intro x hx y hy
  let remainder :=
    (reversal (oddTrace gamma)).drop (epilogue n (oddTrace gamma)).length
  cases hremainder : remainder with
  | nil =>
      have : oddFixedBlock n (oddTrace gamma) = [] := by
        simp [oddFixedBlock, remainder, hremainder]
      simp [this] at hx
  | cons d ds =>
      have hfixedEq : oddFixedBlock n (oddTrace gamma) = (d :: ds).reverse := by
        simp [oddFixedBlock, remainder, hremainder]
      have hdRemainder : d ∈ remainder := by simp [hremainder]
      have hdReverse : d ∈ reversal (oddTrace gamma) :=
        (List.drop_sublist _ _).mem (by simpa [remainder] using hdRemainder)
      have hdTrace : d ∈ oddTrace gamma := by simpa [reversal] using hdReverse
      have hdGamma : d ∈ gamma := (List.mem_filter.mp hdTrace).1
      have hdSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hdGamma
      have hdOdd : Odd d := of_decide_eq_true (List.mem_filter.mp hdTrace).2
      have hcTrace : c1 ∈ evenTrace gamma := mem_of_startsWith hcStart
      have hcGamma : c1 ∈ gamma := (List.mem_filter.mp hcTrace).1
      have hcSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hcGamma
      have hcEven : Even c1 := of_decide_eq_true (List.mem_filter.mp hcTrace).2
      have hreverseStart : StartsWith (reversal (oddTrace gamma)) b1 :=
        startsWith_reversal_of_endsWith hbEnd
      have hremainderStart : StartsWith remainder d := by simp [hremainder, StartsWith]
      have hnotSame : ¬ SameHalf n b1 d :=
        first_after_prologue_not_sameHalf hreverseStart (by
          simpa [remainder, epilogue] using hremainderStart)
      have hdUpper : d ∈ upperHalf n := by
        simp only [SameHalf, lowerHalf, upperHalf, segment, Finset.mem_Icc] at hnotSame hbLower hdSegment ⊢
        omega
      have hsameDC : SameHalf n d c1 := Or.inr ⟨hdUpper, hcUpper⟩
      have hdBeforeC : OccursLeftOf beta d c1 :=
        (corollary_2_2_1_holds n d c1 hdSegment hcSegment hsameDC).1 hdOdd hcEven
          beta hbeta12
      have hfixedNodup : (oddFixedBlock n (oddTrace gamma)).Nodup := by
        rw [hfixedEq]
        apply List.nodup_reverse.mpr
        have hreverseNodup : (reversal (oddTrace gamma)).Nodup := by
          change (oddTrace gamma).reverse.Nodup
          apply List.nodup_reverse.mpr
          exact (isTheta_nodup hgamma12.1).filter _
        have hremainderNodup : remainder.Nodup := by
          dsimp only [remainder]
          exact (List.drop_sublist _ _).nodup hreverseNodup
        rw [hremainder] at hremainderNodup
        exact hremainderNodup
      have hdEndsFixed : EndsWith (oddFixedBlock n (oddTrace gamma)) d := by
        simp [hfixedEq, EndsWith]
      have hxBeforeOrEq : x = d ∨ OccursLeftOf beta x d := by
        by_cases hxd : x = d
        · exact Or.inl hxd
        · right
          have hxdFixed := occursLeftOf_of_mem_of_endsWith hfixedNodup hdEndsFixed hx hxd
          have hfixedPrefix : oddFixedBlock n (oddTrace gamma) <+: oddTrace gamma :=
            ⟨oddActiveBlock n (oddTrace gamma),
              oddFixed_append_oddActive n (oddTrace gamma)⟩
          have hxdGammaTrace := occursLeftOf_of_sublist hfixedPrefix.sublist hxdFixed
          apply occursLeftOf_of_sublist
            (small := oddTrace beta) (large := beta) List.filter_sublist
          rw [hoddTrace]
          exact hxdGammaTrace
      have hcBeforeOrEq : c1 = y ∨ OccursLeftOf beta c1 y := by
        by_cases hcy : c1 = y
        · exact Or.inl hcy
        · right
          have hcyGammaTrace := occursLeftOf_of_startsWith_of_mem
            ((isTheta_nodup hgamma12.1).filter _) hcStart hy hcy
          apply occursLeftOf_of_sublist
            (small := evenTrace beta) (large := beta) List.filter_sublist
          rw [hevenTrace]
          exact hcyGammaTrace
      rcases hxBeforeOrEq with rfl | hxd <;>
        rcases hcBeforeOrEq with rfl | hcy
      · exact hdBeforeC
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1) hdBeforeC hcy
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1) hxd hdBeforeC
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1)
          (occursLeftOf_trans (isTheta_nodup hbeta12.1) hxd hdBeforeC) hcy

lemma oddTrace_before_evenFixed {n : Nat} {gamma beta : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hbeta12 : IsTheta12 n beta)
    (hoddTrace : oddTrace beta = oddTrace gamma)
    (hevenTrace : evenTrace beta = evenTrace gamma) :
    ∀ x ∈ oddTrace gamma,
      ∀ y ∈ evenFixedBlock n (evenTrace gamma), OccursLeftOf beta x y := by
  rcases hstanding with
    ⟨hgamma12, b1, c1, hbEnd, hcStart, _hcommute, hbLower, hcUpper⟩
  intro x hx y hy
  cases hfixed : evenFixedBlock n (evenTrace gamma) with
  | nil => simp [hfixed] at hy
  | cons e es =>
      have heFixed : e ∈ evenFixedBlock n (evenTrace gamma) := by simp [hfixed]
      have heTrace : e ∈ evenTrace gamma := by
        have hfixedSuffix : evenFixedBlock n (evenTrace gamma) <:+ evenTrace gamma :=
          ⟨evenActiveBlock n (evenTrace gamma),
            evenActive_append_evenFixed n (evenTrace gamma)⟩
        exact hfixedSuffix.sublist.mem heFixed
      have heGamma : e ∈ gamma := (List.mem_filter.mp heTrace).1
      have heSegment := mem_segment_of_mem_of_isTheta hgamma12.1 heGamma
      have heEven : Even e := of_decide_eq_true (List.mem_filter.mp heTrace).2
      have hbTrace : b1 ∈ oddTrace gamma := mem_of_endsWith hbEnd
      have hbGamma : b1 ∈ gamma := (List.mem_filter.mp hbTrace).1
      have hbSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hbGamma
      have hbOdd : Odd b1 := of_decide_eq_true (List.mem_filter.mp hbTrace).2
      have heStartsFixed : StartsWith (evenFixedBlock n (evenTrace gamma)) e := by
        simp [hfixed, StartsWith]
      have hnotSame : ¬ SameHalf n c1 e :=
        first_after_prologue_not_sameHalf hcStart (by
          simpa [evenFixedBlock] using heStartsFixed)
      have heLower : e ∈ lowerHalf n := by
        simp only [SameHalf, lowerHalf, upperHalf, segment, Finset.mem_Icc] at hnotSame hcUpper heSegment ⊢
        omega
      have hsameBE : SameHalf n b1 e := Or.inl ⟨hbLower, heLower⟩
      have hbBeforeE : OccursLeftOf beta b1 e :=
        (corollary_2_2_1_holds n b1 e hbSegment heSegment hsameBE).1 hbOdd heEven
          beta hbeta12
      have hxBeforeOrEq : x = b1 ∨ OccursLeftOf beta x b1 := by
        by_cases hxb : x = b1
        · exact Or.inl hxb
        · right
          have hxbGammaTrace := occursLeftOf_of_mem_of_endsWith
            ((isTheta_nodup hgamma12.1).filter _) hbEnd hx hxb
          apply occursLeftOf_of_sublist
            (small := oddTrace beta) (large := beta) List.filter_sublist
          rw [hoddTrace]
          exact hxbGammaTrace
      have heBeforeOrEq : e = y ∨ OccursLeftOf beta e y := by
        by_cases hey : e = y
        · exact Or.inl hey
        · right
          have hevenFixedNodup : (evenFixedBlock n (evenTrace gamma)).Nodup := by
            unfold evenFixedBlock
            exact (List.drop_sublist _ _).nodup ((isTheta_nodup hgamma12.1).filter _)
          have heyFixed := occursLeftOf_of_startsWith_of_mem
            hevenFixedNodup heStartsFixed hy hey
          have hfixedSuffix : evenFixedBlock n (evenTrace gamma) <:+ evenTrace gamma :=
            ⟨evenActiveBlock n (evenTrace gamma),
              evenActive_append_evenFixed n (evenTrace gamma)⟩
          have heyGammaTrace := occursLeftOf_of_sublist hfixedSuffix.sublist heyFixed
          apply occursLeftOf_of_sublist
            (small := evenTrace beta) (large := beta) List.filter_sublist
          rw [hevenTrace]
          exact heyGammaTrace
      rcases hxBeforeOrEq with rfl | hxb <;>
        rcases heBeforeOrEq with rfl | hey
      · exact hbBeforeE
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1) hbBeforeE hey
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1) hxb hbBeforeE
      · exact occursLeftOf_trans (isTheta_nodup hbeta12.1)
          (occursLeftOf_trans (isTheta_nodup hbeta12.1) hxb hbBeforeE) hey

lemma oddFixedBlock_mem_oddTrace {n : Nat} {word : List Nat} {x : Nat}
    (hx : x ∈ oddFixedBlock n (oddTrace word)) : x ∈ oddTrace word := by
  have hprefix : oddFixedBlock n (oddTrace word) <+: oddTrace word :=
    ⟨oddActiveBlock n (oddTrace word),
      oddFixed_append_oddActive n (oddTrace word)⟩
  exact hprefix.mem hx

lemma evenFixedBlock_mem_evenTrace {n : Nat} {word : List Nat} {y : Nat}
    (hy : y ∈ evenFixedBlock n (evenTrace word)) : y ∈ evenTrace word := by
  have hsuffix : evenFixedBlock n (evenTrace word) <:+ evenTrace word :=
    ⟨evenActiveBlock n (evenTrace word),
      evenActive_append_evenFixed n (evenTrace word)⟩
  exact hsuffix.mem hy

lemma filter_not_odd_eq_evenTrace (word : List Nat) :
    word.filter (fun z => !(decide (Odd z))) = evenTrace word := by
  unfold evenTrace trace
  apply List.filter_congr
  intro z _hz
  by_cases hzOdd : Odd z
  · have hzNotEven : ¬ Even z := Nat.not_even_iff_odd.mpr hzOdd
    simp [decide_eq_true hzOdd, decide_eq_false hzNotEven]
  · have hzEven : Even z := Nat.not_odd_iff_even.mp hzOdd
    simp [decide_eq_false hzOdd, decide_eq_true hzEven]

lemma fixedBlocks_interleaving_decomposition {n : Nat} {gamma beta : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hbeta12 : IsTheta12 n beta)
    (hoddTrace : oddTrace beta = oddTrace gamma)
    (hevenTrace : evenTrace beta = evenTrace gamma) :
    ∃ middle ∈ listInterleavings
        (oddActiveBlock n (oddTrace gamma))
        (evenActiveBlock n (evenTrace gamma)),
      beta = oddFixedBlock n (oddTrace gamma) ++ middle ++
        evenFixedBlock n (evenTrace gamma) := by
  let p : Nat → Bool := fun z => decide (Odd z)
  apply eq_fixedPrefix_interleaving_fixedSuffix
    (p := p) (hword := isTheta_nodup hbeta12.1)
  · intro x hx
    have hxTrace := oddFixedBlock_mem_oddTrace hx
    exact (List.mem_filter.mp hxTrace).2
  · intro x hx
    have hxTrace := oddActiveBlock_mem_oddTrace hx
    exact (List.mem_filter.mp hxTrace).2
  · intro y hy
    have hyTrace := evenActiveBlock_mem_evenTrace hy
    have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hyTrace).2
    exact decide_eq_false (Nat.not_odd_iff_even.mpr hyEven)
  · intro y hy
    have hyTrace := evenFixedBlock_mem_evenTrace hy
    have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hyTrace).2
    exact decide_eq_false (Nat.not_odd_iff_even.mpr hyEven)
  · change oddTrace beta = _
    exact hoddTrace.trans (oddFixed_append_oddActive n (oddTrace gamma)).symm
  · rw [filter_not_odd_eq_evenTrace, hevenTrace]
    exact (evenActive_append_evenFixed n (evenTrace gamma)).symm
  · intro x hx y hy
    apply oddFixed_before_evenTrace hstanding hbeta12 hoddTrace hevenTrace x hx y
    rw [← evenActive_append_evenFixed n (evenTrace gamma)]
    exact hy
  · intro x hx y hy
    apply oddTrace_before_evenFixed hstanding hbeta12 hoddTrace hevenTrace x _ y hy
    rw [← oddFixed_append_oddActive n (oddTrace gamma)]
    exact hx

lemma traces_of_admissibleInterleaving {n : Nat} {gammaOdd gammaEven middle : List Nat}
    (hoddParity : ∀ x ∈ gammaOdd, Odd x)
    (hevenParity : ∀ y ∈ gammaEven, Even y)
    (hmiddle : middle ∈ listInterleavings
      (oddActiveBlock n gammaOdd) (evenActiveBlock n gammaEven)) :
    let word := oddFixedBlock n gammaOdd ++ middle ++ evenFixedBlock n gammaEven
    oddTrace word = gammaOdd ∧ evenTrace word = gammaEven := by
  dsimp only
  let p : Nat → Bool := fun z => decide (Odd z)
  have hoddFixed : ∀ x ∈ oddFixedBlock n gammaOdd, p x = true := by
    intro x hx
    apply decide_eq_true
    apply hoddParity x
    exact (show oddFixedBlock n gammaOdd <+: gammaOdd from
      ⟨oddActiveBlock n gammaOdd, oddFixed_append_oddActive n gammaOdd⟩).mem hx
  have hoddActive : ∀ x ∈ oddActiveBlock n gammaOdd, p x = true := by
    intro x hx
    apply decide_eq_true
    apply hoddParity x
    rw [← oddFixed_append_oddActive n gammaOdd]
    simp [hx]
  have hevenActive : ∀ y ∈ evenActiveBlock n gammaEven, p y = false := by
    intro y hy
    apply decide_eq_false
    apply Nat.not_odd_iff_even.mpr
    apply hevenParity y
    rw [← evenActive_append_evenFixed n gammaEven]
    simp [hy]
  have hevenFixed : ∀ y ∈ evenFixedBlock n gammaEven, p y = false := by
    intro y hy
    apply decide_eq_false
    apply Nat.not_odd_iff_even.mpr
    apply hevenParity y
    exact (show evenFixedBlock n gammaEven <:+ gammaEven from
      ⟨evenActiveBlock n gammaEven, evenActive_append_evenFixed n gammaEven⟩).mem hy
  have hmiddleFilters := filters_of_mem_listInterleavings
    hoddActive hevenActive hmiddle
  constructor
  · unfold oddTrace trace
    rw [List.filter_append, List.filter_append,
      List.filter_eq_self.mpr hoddFixed, hmiddleFilters.1]
    have hevenFixedNil : (evenFixedBlock n gammaEven).filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      rw [hevenFixed y hy]
      simp
    rw [hevenFixedNil, List.append_nil, oddFixed_append_oddActive]
  · rw [← filter_not_odd_eq_evenTrace]
    rw [List.filter_append, List.filter_append]
    have hoddFixedNil : (oddFixedBlock n gammaOdd).filter (fun z => !p z) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      rw [hoddFixed x hx]
      simp
    have hevenFixedSelf :
        (evenFixedBlock n gammaEven).filter (fun z => !p z) =
          evenFixedBlock n gammaEven := by
      apply List.filter_eq_self.mpr
      intro y hy
      rw [hevenFixed y hy]
      simp
    rw [hoddFixedNil, List.nil_append, hmiddleFilters.2,
      hevenFixedSelf, evenActive_append_evenFixed]

lemma nodup_admissibleInterleavingWords {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) :
    (admissibleInterleavingWords n (oddTrace gamma) (evenTrace gamma)).Nodup := by
  have hoddTraceNodup : (oddTrace gamma).Nodup := (isTheta_nodup hgamma).filter _
  have hevenTraceNodup : (evenTrace gamma).Nodup := (isTheta_nodup hgamma).filter _
  have hoddActiveNodup : (oddActiveBlock n (oddTrace gamma)).Nodup := by
    unfold oddActiveBlock epilogue
    apply List.nodup_reverse.mpr
    exact (prologue_prefix n (reversal (oddTrace gamma))).sublist.nodup (by
      change (oddTrace gamma).reverse.Nodup
      exact List.nodup_reverse.mpr hoddTraceNodup)
  have hevenActiveNodup : (evenActiveBlock n (evenTrace gamma)).Nodup := by
    unfold evenActiveBlock
    exact (prologue_prefix n (evenTrace gamma)).sublist.nodup hevenTraceNodup
  have hdisjoint : List.Disjoint
      (oddActiveBlock n (oddTrace gamma))
      (evenActiveBlock n (evenTrace gamma)) := by
    rw [List.disjoint_left]
    intro x hx hy
    have hxOdd : Odd x := of_decide_eq_true
      (List.mem_filter.mp (oddActiveBlock_mem_oddTrace hx)).2
    have hxEven : Even x := of_decide_eq_true
      (List.mem_filter.mp (evenActiveBlock_mem_evenTrace hy)).2
    exact (Nat.not_even_iff_odd.mpr hxOdd) hxEven
  have hinterleavings := nodup_listInterleavings
    hoddActiveNodup hevenActiveNodup hdisjoint
  unfold admissibleInterleavingWords
  apply hinterleavings.map
  intro left right heq
  have hcancelSuffix := List.append_left_injective
    (evenFixedBlock n (evenTrace gamma)) heq
  exact List.append_right_injective (oddFixedBlock n (oddTrace gamma)) hcancelSuffix

lemma length_admissibleInterleavingWords (n : Nat) (gammaOdd gammaEven : List Nat) :
    (admissibleInterleavingWords n gammaOdd gammaEven).length =
      Nat.choose
        ((epilogue n gammaOdd).length + (prologue n gammaEven).length)
        (prologue n gammaEven).length := by
  unfold admissibleInterleavingWords
  rw [List.length_map, length_listInterleavings,
    oddActiveBlock_length, evenActiveBlock_length]

lemma interleavingClass_card_eq_admissibleWords {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card =
      (admissibleInterleavingWords n (oddTrace gamma) (evenTrace gamma)).toFinset.card := by
  classical
  apply Finset.card_bij
    (s := interleavingClass n (oddTrace gamma) (evenTrace gamma))
    (t := (admissibleInterleavingWords n (oddTrace gamma) (evenTrace gamma)).toFinset)
    (fun sigma _ => permutationWord sigma)
  · intro sigma hsigma
    have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
        oddTrace (permutationWord sigma) = oddTrace gamma ∧
        evenTrace (permutationWord sigma) = evenTrace gamma := by
      simpa [interleavingClass] using hsigma
    obtain ⟨middle, hmiddle, hword⟩ := fixedBlocks_interleaving_decomposition
      hstanding hsigmaData.1 hsigmaData.2.1 hsigmaData.2.2
    rw [List.mem_toFinset]
    unfold admissibleInterleavingWords
    apply List.mem_map.mpr
    exact ⟨middle, hmiddle, hword.symm⟩
  · intro sigma _ tau _ heq
    exact permutationWord_injective heq
  · intro word hword
    rw [List.mem_toFinset] at hword
    unfold admissibleInterleavingWords at hword
    rcases List.mem_map.mp hword with ⟨middle, hmiddle, hwordEq⟩
    subst word
    let candidate := oddFixedBlock n (oddTrace gamma) ++ middle ++
      evenFixedBlock n (evenTrace gamma)
    have hcandidate12 : IsTheta12 n candidate := by
      exact admissibleInterleaving_isTheta12 hstanding hmiddle
    have hoddParity : ∀ x ∈ oddTrace gamma, Odd x := by
      intro x hx
      exact of_decide_eq_true (List.mem_filter.mp hx).2
    have hevenParity : ∀ y ∈ evenTrace gamma, Even y := by
      intro y hy
      exact of_decide_eq_true (List.mem_filter.mp hy).2
    have hcandidateTraces : oddTrace candidate = oddTrace gamma ∧
        evenTrace candidate = evenTrace gamma := by
      simpa only [candidate] using traces_of_admissibleInterleaving
        hoddParity hevenParity hmiddle
    obtain ⟨sigma, hsigmaWord⟩ := exists_permutationWord_eq_of_isTheta hcandidate12.1
    have hsigmaMem : sigma ∈ interleavingClass n (oddTrace gamma) (evenTrace gamma) := by
      simp only [interleavingClass, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hsigmaWord]
      exact ⟨hcandidate12, hcandidateTraces⟩
    exact ⟨sigma, hsigmaMem, hsigmaWord⟩

/-- **Lemma 2.5.** The independent active odd/even shuffles give precisely
the standing interleaving class, hence its binomial cardinality. -/
theorem lemma_2_5_holds : lemma_2_5 := by
  intro n gamma hstanding
  dsimp only
  rw [interleavingClass_card_eq_admissibleWords hstanding,
    List.toFinset_card_of_nodup (nodup_admissibleInterleavingWords hstanding.1.1),
    length_admissibleInterleavingWords]

lemma log_two_four_le_of_dyadic_threshold {n : Nat}
    (hthreshold : 16 * dyadicQ n <= n) : 4 <= Nat.log 2 n := by
  have hn : 16 <= n := by
    have hq := dyadicQ_pos n
    nlinarith
  rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
  norm_num
  exact hn

lemma dyadic_modulus_two_of_log_four {n : Nat} (_hlog : 4 <= Nat.log 2 n) :
    2 ^ ((Nat.log 2 n - 4) + 1) = 2 * dyadicQ n := by
  rw [pow_add]
  simp [dyadicQ, Nat.mul_comm]

lemma dyadic_modulus_four_of_log_four {n : Nat} (hlog : 4 <= Nat.log 2 n) :
    2 ^ ((Nat.log 2 n - 3) + 1) = 4 * dyadicQ n := by
  have hexponent : (Nat.log 2 n - 3) + 1 = (Nat.log 2 n - 4) + 2 := by omega
  rw [hexponent, pow_add]
  norm_num [dyadicQ]
  ring

lemma dyadic_modulus_eight_of_log_four {n : Nat} (hlog : 4 <= Nat.log 2 n) :
    2 ^ ((Nat.log 2 n - 2) + 1) = 8 * dyadicQ n := by
  have hexponent : (Nat.log 2 n - 2) + 1 = (Nat.log 2 n - 4) + 3 := by omega
  rw [hexponent, pow_add]
  norm_num [dyadicQ]
  ring

lemma dyadic_denominator_two_of_log_four {n : Nat} (hlog : 4 <= Nat.log 2 n) :
    2 ^ (Nat.log 2 n - 3) = 2 * dyadicQ n := by
  have hexponent : Nat.log 2 n - 3 = (Nat.log 2 n - 4) + 1 := by omega
  rw [hexponent, pow_add]
  simp [dyadicQ, Nat.mul_comm]

lemma dyadic_denominator_four_of_log_four {n : Nat} (hlog : 4 <= Nat.log 2 n) :
    2 ^ (Nat.log 2 n - 2) = 4 * dyadicQ n := by
  have hexponent : Nat.log 2 n - 2 = (Nat.log 2 n - 4) + 2 := by omega
  rw [hexponent, pow_add]
  norm_num [dyadicQ]
  ring

lemma dyadicQ_eq_one_of_log_eq_four {n : Nat} (hlog : Nat.log 2 n = 4) :
    dyadicQ n = 1 := by simp [dyadicQ, hlog]

lemma dyadicQ_word_prefix {n k s : Nat} {word : List Nat}
    (hthreshold : 16 * dyadicQ n <= n) (hword : IsTheta n word)
    (hscale : 4 * k <= 2 * s + 1) (hs : s * dyadicQ n <= n) :
    PrefixCongruent word k (dyadicQ n) := by
  have hlogFour := log_two_four_le_of_dyadic_threshold hthreshold
  have hnPos : 0 < n := by
    have hq := dyadicQ_pos n
    nlinarith
  by_cases hlogFive : 5 <= Nat.log 2 n
  · have hdenom : (2 * s) * 2 ^ (Nat.log 2 n - 5) <= n := by
      have hhalf := dyadic_denominator_half (n := n) (by
        rw [Nat.le_log_iff_pow_le (by norm_num) (Nat.ne_of_gt hnPos)] at hlogFive
        norm_num at hlogFive
        exact hlogFive)
      nlinarith
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 5)
      (k := k) (r := 2 * s) hnPos hword hdenom hscale
    rw [show (Nat.log 2 n - 5) + 1 = Nat.log 2 n - 4 by omega]
      at h
    exact h
  · have hlogEq : Nat.log 2 n = 4 := by omega
    rw [dyadicQ_eq_one_of_log_eq_four hlogEq]
    apply prefixCongruent_one_of_le_length
    rw [isTheta_length hword]
    have hk : k <= s := by omega
    have hs' : s <= n := by
      simpa [dyadicQ_eq_one_of_log_eq_four hlogEq] using hs
    omega

lemma dyadicQ_trace_prefixes_of_threshold {n k s : Nat} {word : List Nat}
    (hthreshold : 16 * dyadicQ n <= n) (hword : IsTheta n word)
    (hhalf : s * dyadicQ n <= n / 2) (hk : k <= s) :
    PrefixCongruent (oddTrace word) k (dyadicQ n) ∧
      PrefixCongruent (evenTrace word) k (dyadicQ n) := by
  have hlogFour := log_two_four_le_of_dyadic_threshold hthreshold
  have hnPos : 0 < n := by
    have hq := dyadicQ_pos n
    nlinarith
  by_cases hlogFive : 5 <= Nat.log 2 n
  · have hn : 32 <= n := by
      rw [Nat.le_log_iff_pow_le (by norm_num) (Nat.ne_of_gt hnPos)] at hlogFive
      norm_num at hlogFive
      exact hlogFive
    exact dyadicQ_trace_prefixes hn hword hhalf hk
  · have hlogEq : Nat.log 2 n = 4 := by omega
    have hqEq : dyadicQ n = 1 := dyadicQ_eq_one_of_log_eq_four hlogEq
    have hoddTheta := isTheta_oddBase hword
    have hevenTheta := isTheta_evenBase hword
    have hsBound : s <= n / 2 := by simpa only [hqEq, Nat.mul_one] using hhalf
    have hoddLength : k <= (oddTrace word).length := by
      have hlength := isTheta_length hoddTheta
      simp only [oddBase, List.length_map] at hlength
      omega
    have hevenLength : k <= (evenTrace word).length := by
      have hlength := isTheta_length hevenTheta
      simp only [evenBase, List.length_map] at hlength
      omega
    rw [hqEq]
    exact ⟨prefixCongruent_one_of_le_length hoddLength,
      prefixCongruent_one_of_le_length hevenLength⟩

lemma dyadic_pattern_sixteen {n : Nat} {word : List Nat}
    (hword : IsTheta n word) (hthreshold : 16 * dyadicQ n <= n) :
    let pattern := fun w : List Nat =>
      PrefixCongruent w 2 (4 * dyadicQ n) ∧
      PrefixCongruent w 4 (2 * dyadicQ n) ∧
      PrefixCongruent w 8 (dyadicQ n)
    pattern word ∧ pattern (oddTrace word) ∧ pattern (evenTrace word) := by
  dsimp only
  have hnPos : 0 < n := by
    have hq := dyadicQ_pos n
    nlinarith
  have hnSixteen : 16 <= n := by
    have hq := dyadicQ_pos n
    nlinarith
  have hlog := log_two_four_le_of_dyadic_threshold hthreshold
  have hhalf : 8 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have hhalfOdd : 8 * dyadicQ n <= (n + 1) / 2 := by omega
  have hwordFour : PrefixCongruent word 2 (4 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 3)
      (k := 2) (r := 8) hnPos hword (by
        rw [dyadic_denominator_two_of_log_four hlog]
        nlinarith) (by norm_num)
    rw [dyadic_modulus_four_of_log_four hlog] at h
    exact h
  have hwordTwo : PrefixCongruent word 4 (2 * dyadicQ n) := by
    have h := forcedPrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 4) (r := 16) hnPos hword (by
        simpa only [dyadicQ] using hthreshold) (by norm_num)
    rw [dyadic_modulus_two_of_log_four hlog] at h
    exact h
  have hwordOne : PrefixCongruent word 8 (dyadicQ n) :=
    dyadicQ_word_prefix hthreshold hword (s := 16) (by norm_num) hthreshold
  have hoddFour : PrefixCongruent (oddTrace word) 2 (4 * dyadicQ n) := by
    have h := forcedOddTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 2) (r := 8) hnPos hword hhalfOdd (by norm_num)
    rw [dyadic_modulus_two_of_log_four hlog] at h
    convert h using 1
    all_goals omega
  have hevenFour : PrefixCongruent (evenTrace word) 2 (4 * dyadicQ n) := by
    have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
      (k := 2) (r := 8) (by omega) hword hhalf (by norm_num)
    rw [dyadic_modulus_two_of_log_four hlog] at h
    convert h using 1
    all_goals omega
  have traceTwo : PrefixCongruent (oddTrace word) 4 (2 * dyadicQ n) ∧
      PrefixCongruent (evenTrace word) 4 (2 * dyadicQ n) := by
    by_cases hlogFive : 5 <= Nat.log 2 n
    · have hn : 32 <= n := by
        rw [Nat.le_log_iff_pow_le (by norm_num) (Nat.ne_of_gt hnPos)] at hlogFive
        norm_num at hlogFive
        exact hlogFive
      exact ⟨(proposition_2_8_holds n word hn hword hthreshold).2.1.2.1,
        (proposition_2_8_holds n word hn hword hthreshold).2.2.2.1⟩
    · have hlogEq : Nat.log 2 n = 4 := by omega
      have hqEq := dyadicQ_eq_one_of_log_eq_four hlogEq
      have hoddTheta := isTheta_oddBase hword
      have hevenTheta := isTheta_evenBase hword
      have hoddLength : 4 <= (oddBase word).length := by
        rw [isTheta_length hoddTheta]
        omega
      have hevenLength : 4 <= (evenBase word).length := by
        rw [isTheta_length hevenTheta]
        omega
      have hodd := prefixCongruent_oddLift_of_base
        (fun x hx => positive_of_mem_of_isTheta hoddTheta hx)
        (prefixCongruent_one_of_le_length hoddLength)
      have heven := prefixCongruent_evenLift_of_base
        (prefixCongruent_one_of_le_length hevenLength)
      rw [oddLift_oddBase] at hodd
      rw [evenLift_evenBase] at heven
      constructor
      · simpa only [hqEq] using hodd
      · simpa only [hqEq] using heven
  have traceOne := dyadicQ_trace_prefixes_of_threshold
    hthreshold hword (k := 8) (s := 8) hhalf (by norm_num)
  exact ⟨⟨hwordFour, hwordTwo, hwordOne⟩,
    ⟨⟨hoddFour, traceTwo.1, traceOne.1⟩,
      ⟨hevenFour, traceTwo.2, traceOne.2⟩⟩⟩

/-- The boundary entries in the standing situation are separated far enough
that neither affine reflection remains in `[n]`. -/
lemma standing_boundary_separated {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    exists b1 c1 : Nat,
      EndsWith (oddTrace gamma) b1 /\
      StartsWith (evenTrace gamma) c1 /\
      b1 ∈ lowerHalf n /\ c1 ∈ upperHalf n /\
      2 * b1 <= c1 /\ n < 2 * c1 - b1 := by
  rcases hstanding with
    ⟨hgamma12, b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hn : 3 <= n := three_le_of_standingInterleavingHypotheses
    ⟨hgamma12, b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hbSegment : b1 ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
    omega
  have hcSegment : c1 ∈ segment n := by
    simp only [upperHalf, segment, Finset.mem_Icc] at hcUpper ⊢
    omega
  have hbOdd : Odd b1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hcEven : Even c1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_startsWith hcStart)).2
  have hnotDoNotCommute : ¬ DoNotCommute n b1 c1 := by
    intro hdo
    rcases hcommute with ⟨witness, hwitness12, hreverse⟩
    exact (occursLeftOf_asymm (isTheta_nodup hwitness12.1)
      (hdo witness hwitness12)) hreverse
  have hnoBoundaryReflections :
      ¬ ((c1 <= 2 * b1 /\ 2 * b1 - c1 ∈ segment n) \/
        (b1 <= 2 * c1 /\ 2 * c1 - b1 ∈ segment n)) := by
    intro hreflections
    exact hnotDoNotCommute
      ((theorem_2_2_holds n b1 c1 hn hbSegment hcSegment hbOdd hcEven).2 hreflections)
  have hseparated : 2 * b1 <= c1 := by
    by_contra hnot
    apply hnoBoundaryReflections
    left
    constructor
    · omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, Finset.mem_Icc] at hbLower
      rcases hbOdd with ⟨b, hb⟩
      rcases hcEven with ⟨c, hc⟩
      omega
  have hreflectionAbove : n < 2 * c1 - b1 := by
    by_contra hnot
    apply hnoBoundaryReflections
    right
    constructor
    · simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hbLower hcUpper
      omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hbLower hcUpper
      omega
  exact ⟨b1, c1, hbEnd, hcStart, hbLower, hcUpper,
    hseparated, hreflectionAbove⟩

lemma oddActiveBlock_nodup {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) :
    (oddActiveBlock n (oddTrace gamma)).Nodup := by
  unfold oddActiveBlock epilogue
  apply List.nodup_reverse.mpr
  exact (prologue_prefix n (reversal (oddTrace gamma))).sublist.nodup (by
    change (oddTrace gamma).reverse.Nodup
    exact List.nodup_reverse.mpr ((isTheta_nodup hgamma).filter _))

lemma evenActiveBlock_nodup {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) :
    (evenActiveBlock n (evenTrace gamma)).Nodup := by
  unfold evenActiveBlock
  exact (prologue_prefix n (evenTrace gamma)).sublist.nodup
    ((isTheta_nodup hgamma).filter _)

/-- Every active odd/even pair obeys the two strict separation inequalities
implicit in the paper's commutation cases. -/
lemma activeBlocks_separated {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ oddActiveBlock n (oddTrace gamma),
      ∀ y ∈ evenActiveBlock n (evenTrace gamma),
        2 * x <= y /\ n < 2 * y - x := by
  obtain ⟨b1, c1, hbEnd, hcStart, hbLower, hcUpper,
      hboundary, hreflection⟩ := standing_boundary_separated hstanding
  intro x hx y hy
  have hxTrace := oddActiveBlock_mem_oddTrace hx
  have hyTrace := evenActiveBlock_mem_evenTrace hy
  have hxGamma : x ∈ gamma := (List.mem_filter.mp hxTrace).1
  have hyGamma : y ∈ gamma := (List.mem_filter.mp hyTrace).1
  have hxSegment := mem_segment_of_mem_of_isTheta hstanding.1.1 hxGamma
  have hySegment := mem_segment_of_mem_of_isTheta hstanding.1.1 hyGamma
  have hxLe : x <= b1 := oddEpilogue_entry_le_last hstanding.1.1 hbEnd hbLower (by
    simpa [oddActiveBlock] using hx)
  have hyLe : c1 <= y := evenPrologue_first_le_entry hstanding.1.1 hcStart hcUpper (by
    simpa [evenActiveBlock] using hy)
  simp only [segment, Finset.mem_Icc] at hxSegment hySegment
  constructor <;> omega

/-- Four active odds and three active evens already force the ambient segment
past the first dyadic scale. -/
lemma sixteen_le_of_active_lengths {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hu : 4 <= (epilogue n (oddTrace gamma)).length)
    (hv : 3 <= (prologue n (evenTrace gamma)).length) : 16 <= n := by
  let xs := oddActiveBlock n (oddTrace gamma)
  let ys := evenActiveBlock n (evenTrace gamma)
  have hxsLength : 4 <= xs.length := by
    simpa only [xs, oddActiveBlock_length] using hu
  have hysLength : 3 <= ys.length := by
    simpa only [ys, evenActiveBlock_length] using hv
  let x0 := xs[0]'(by omega)
  let x1 := xs[1]'(by omega)
  let x2 := xs[2]'(by omega)
  let x3 := xs[3]'(by omega)
  let y0 := ys[0]'(by omega)
  let y1 := ys[1]'(by omega)
  let y2 := ys[2]'(by omega)
  have hx0 : x0 ∈ xs := List.getElem_mem _
  have hx1 : x1 ∈ xs := List.getElem_mem _
  have hx2 : x2 ∈ xs := List.getElem_mem _
  have hx3 : x3 ∈ xs := List.getElem_mem _
  have hy0 : y0 ∈ ys := List.getElem_mem _
  have hy1 : y1 ∈ ys := List.getElem_mem _
  have hy2 : y2 ∈ ys := List.getElem_mem _
  have hxsNodup : xs.Nodup := by
    simpa only [xs] using oddActiveBlock_nodup hstanding.1.1
  have hysNodup : ys.Nodup := by
    simpa only [ys] using evenActiveBlock_nodup hstanding.1.1
  have hx01 : x0 ≠ x1 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx02 : x0 ≠ x2 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx03 : x0 ≠ x3 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx12 : x1 ≠ x2 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx13 : x1 ≠ x3 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx23 : x2 ≠ x3 := by
    exact mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hy01 : y0 ≠ y1 := by
    exact mt hysNodup.getElem_inj_iff.mp (by norm_num)
  have hy02 : y0 ≠ y2 := by
    exact mt hysNodup.getElem_inj_iff.mp (by norm_num)
  have hy12 : y1 ≠ y2 := by
    exact mt hysNodup.getElem_inj_iff.mp (by norm_num)
  have hxOdd : ∀ x ∈ xs, Odd x := by
    intro x hx
    exact of_decide_eq_true
      (List.mem_filter.mp (oddActiveBlock_mem_oddTrace (by simpa only [xs] using hx))).2
  have hyEven : ∀ y ∈ ys, Even y := by
    intro y hy
    exact of_decide_eq_true
      (List.mem_filter.mp (evenActiveBlock_mem_evenTrace (by simpa only [ys] using hy))).2
  have hsep := activeBlocks_separated hstanding
  have h00 := hsep x0 (by simpa only [xs] using hx0) y0 (by simpa only [ys] using hy0)
  have h01 := hsep x1 (by simpa only [xs] using hx1) y0 (by simpa only [ys] using hy0)
  have h02 := hsep x2 (by simpa only [xs] using hx2) y0 (by simpa only [ys] using hy0)
  have h03 := hsep x3 (by simpa only [xs] using hx3) y0 (by simpa only [ys] using hy0)
  have h10 := hsep x0 (by simpa only [xs] using hx0) y1 (by simpa only [ys] using hy1)
  have h11 := hsep x1 (by simpa only [xs] using hx1) y1 (by simpa only [ys] using hy1)
  have h12 := hsep x2 (by simpa only [xs] using hx2) y1 (by simpa only [ys] using hy1)
  have h13 := hsep x3 (by simpa only [xs] using hx3) y1 (by simpa only [ys] using hy1)
  have h20 := hsep x0 (by simpa only [xs] using hx0) y2 (by simpa only [ys] using hy2)
  have h21 := hsep x1 (by simpa only [xs] using hx1) y2 (by simpa only [ys] using hy2)
  have h22 := hsep x2 (by simpa only [xs] using hx2) y2 (by simpa only [ys] using hy2)
  have h23 := hsep x3 (by simpa only [xs] using hx3) y2 (by simpa only [ys] using hy2)
  have hy0Segment := mem_segment_of_mem_of_isTheta hstanding.1.1
    (List.mem_filter.mp (evenActiveBlock_mem_evenTrace
      (by simpa only [ys] using hy0))).1
  have hy1Segment := mem_segment_of_mem_of_isTheta hstanding.1.1
    (List.mem_filter.mp (evenActiveBlock_mem_evenTrace
      (by simpa only [ys] using hy1))).1
  have hy2Segment := mem_segment_of_mem_of_isTheta hstanding.1.1
    (List.mem_filter.mp (evenActiveBlock_mem_evenTrace
      (by simpa only [ys] using hy2))).1
  rcases hxOdd x0 hx0 with ⟨a0, ha0⟩
  rcases hxOdd x1 hx1 with ⟨a1, ha1⟩
  rcases hxOdd x2 hx2 with ⟨a2, ha2⟩
  rcases hxOdd x3 hx3 with ⟨a3, ha3⟩
  rcases hyEven y0 hy0 with ⟨b0, hb0⟩
  rcases hyEven y1 hy1 with ⟨b1, hb1⟩
  rcases hyEven y2 hy2 with ⟨b2, hb2⟩
  simp only [segment, Finset.mem_Icc] at hy0Segment hy1Segment hy2Segment
  omega

lemma sixteen_mul_dyadicQ_le {n : Nat} (hn : 16 <= n) :
    16 * dyadicQ n <= n := by
  have hnPos : n ≠ 0 := by omega
  have hlog : 4 <= Nat.log 2 n := by
    rw [Nat.le_log_iff_pow_le (by norm_num) hnPos]
    norm_num
    exact hn
  have hpow : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hnPos
  rw [show 16 * dyadicQ n = 2 ^ Nat.log 2 n by
    simp only [dyadicQ]
    rw [show Nat.log 2 n = (Nat.log 2 n - 4) + 4 by omega, pow_add]
    norm_num
    ring]
  exact hpow


lemma oddTrace_reversal_eq (word : List Nat) :
    oddTrace (reversal word) = reversal (oddTrace word) := by
  simp [oddTrace, trace, reversal]

lemma startsWith_oddBase_of_oddTrace {word : List Nat} {a : Nat}
    (h : StartsWith (oddTrace word) a) :
    StartsWith (oddBase word) ((a + 1) / 2) := by
  unfold StartsWith at h ⊢
  simp only [oddBase, List.head?_map, h, Option.map_some]

lemma occursLeftOf_oddTrace_of_oddBase {word : List Nat} {x y : Nat}
    (hx : Odd x) (hy : Odd y)
    (h : OccursLeftOf (oddBase word) ((x + 1) / 2) ((y + 1) / 2)) :
    OccursLeftOf (oddTrace word) x y := by
  have hlift := occursLeftOf_map (fun z : Nat => 2 * z - 1) h
  change OccursLeftOf (oddLift (oddBase word))
    (2 * ((x + 1) / 2) - 1) (2 * ((y + 1) / 2) - 1) at hlift
  rw [oddLift_oddBase] at hlift
  rcases hx with ⟨X, hx⟩
  rcases hy with ⟨Y, hy⟩
  convert hlift using 1 <;> omega

lemma oddEpilogue_closed_left {n : Nat} {gamma : List Nat} {x z : Nat}
    (hgamma : IsTheta n gamma)
    (hx : x ∈ epilogue n (oddTrace gamma))
    (hzx : OccursLeftOf (oddTrace (reversal gamma)) z x) :
    z ∈ epilogue n (oddTrace gamma) := by
  have htraceNodup : (oddTrace (reversal gamma)).Nodup :=
    (isTheta_nodup (isTheta_reversal hgamma)).filter _
  have hx' : x ∈ prologue n (oddTrace (reversal gamma)) := by
    simpa only [epilogue, oddTrace_reversal_eq] using hx
  have hz' := mem_prologue_of_occursLeftOf_mem_prologue htraceNodup hx' hzx
  simpa only [epilogue, oddTrace_reversal_eq] using hz'

/-- The odd-trace version of Theorem 2.4's forcing rule, oriented from the
right endpoint of the original odd trace. -/
lemma oddEpilogue_forced_middle {n : Nat} {gamma : List Nat}
    {first x y z : Nat}
    (hgamma : IsTheta n gamma)
    (hfirst : EndsWith (oddTrace gamma) first)
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hzSegment : z ∈ segment n)
    (hfirstOdd : Odd first) (hxOdd : Odd x) (hyOdd : Odd y) (hzOdd : Odd z)
    (hmean : x + y = 2 * z)
    (hfirstZ : first ≠ z) (hfirstX : first ≠ x)
    (hdegree :
      binaryCongruenceDegree ((first + 1) / 2) ((x + 1) / 2) <
        binaryCongruenceDegree ((first + 1) / 2) ((z + 1) / 2))
    (hxEpilogue : x ∈ epilogue n (oddTrace gamma)) :
    z ∈ epilogue n (oddTrace gamma) := by
  let word := reversal gamma
  have hword : IsTheta n word := isTheta_reversal hgamma
  have hbase : IsTheta ((n + 1) / 2) (oddBase word) := isTheta_oddBase hword
  have htraceStart : StartsWith (oddTrace word) first := by
    simpa only [word, oddTrace_reversal_eq] using startsWith_reversal_of_endsWith hfirst
  have hbaseStart : StartsWith (oddBase word) ((first + 1) / 2) :=
    startsWith_oddBase_of_oddTrace htraceStart
  have hxBase := oddHalf_mem_segment hxSegment hxOdd
  have hyBase := oddHalf_mem_segment hySegment hyOdd
  have hzBase := oddHalf_mem_segment hzSegment hzOdd
  have hmeanBase : (x + 1) / 2 + (y + 1) / 2 = 2 * ((z + 1) / 2) := by
    rcases hxOdd with ⟨X, hx⟩
    rcases hyOdd with ⟨Y, hy⟩
    rcases hzOdd with ⟨Z, hz⟩
    omega
  have hfirstZBase : (first + 1) / 2 != (z + 1) / 2 := by
    have hne : (first + 1) / 2 ≠ (z + 1) / 2 := by
      intro heq
      rcases hfirstOdd with ⟨F, hf⟩
      rcases hzOdd with ⟨Z, hz⟩
      exact hfirstZ (by omega)
    simpa using hne
  have hfirstXBase : (first + 1) / 2 != (x + 1) / 2 := by
    have hne : (first + 1) / 2 ≠ (x + 1) / 2 := by
      intro heq
      rcases hfirstOdd with ⟨F, hf⟩
      rcases hxOdd with ⟨X, hx⟩
      exact hfirstX (by omega)
    simpa using hne
  have hforced := theorem_2_4_holds ((n + 1) / 2) (oddBase word)
    ((first + 1) / 2) ((x + 1) / 2) ((y + 1) / 2) ((z + 1) / 2)
    hbase hbaseStart hxBase hyBase hzBase hmeanBase hfirstZBase hfirstXBase hdegree
  have htraceOccurs : OccursLeftOf (oddTrace word) z x :=
    occursLeftOf_oddTrace_of_oddBase hzOdd hxOdd hforced.1
  exact oddEpilogue_closed_left hgamma hxEpilogue (by simpa only [word] using htraceOccurs)

lemma factorization_five_mul_pow_two (k : Nat) :
    (5 * 2 ^ k).factorization 2 = k := by
  rw [Nat.factorization_mul (by norm_num : 5 ≠ 0)
    (pow_ne_zero k (by norm_num : 2 ≠ 0))]
  norm_num [Nat.factorization_pow]

lemma dyadicQ_four_pow (n : Nat) : 4 * dyadicQ n = 2 ^ (Nat.log 2 n - 4 + 2) := by
  simp only [dyadicQ, pow_add]
  norm_num
  ring

lemma dyadicQ_eight_pow (n : Nat) : 8 * dyadicQ n = 2 ^ (Nat.log 2 n - 4 + 3) := by
  simp only [dyadicQ, pow_add]
  norm_num
  ring

/-- Once the last odd entry lies between the fourth and sixth dyadic levels,
its immediately preceding congruence-class value cannot remain in the odd
epilogue. -/
lemma dyadic_predecessor_not_mem_oddEpilogue {n : Nat} {gamma : List Nat}
    {b1 : Nat}
    (hgamma : IsTheta n gamma)
    (hbEnd : EndsWith (oddTrace gamma) b1)
    (hbLower : b1 ∈ lowerHalf n)
    (hbOdd : Odd b1)
    (hbEight : 8 * dyadicQ n < b1)
    (hbSixteen : b1 < 16 * dyadicQ n) :
    b1 - 2 * dyadicQ n ∉ epilogue n (oddTrace gamma) := by
  let word := reversal gamma
  let baseWord := oddBase word
  let a1 := (b1 + 1) / 2
  let e := Nat.log 2 n - 4
  let q := dyadicQ n
  have hqPos : 0 < q := dyadicQ_pos n
  have hword : IsTheta n word := isTheta_reversal hgamma
  have hbase : IsTheta ((n + 1) / 2) baseWord := by
    simpa only [baseWord] using isTheta_oddBase hword
  have htraceStart : StartsWith (oddTrace word) b1 := by
    simpa only [word, oddTrace_reversal_eq] using startsWith_reversal_of_endsWith hbEnd
  have hbaseStart : StartsWith baseWord a1 := by
    simpa only [baseWord, a1] using startsWith_oddBase_of_oddTrace htraceStart
  have haFour : 4 < a1 := by
    simp only [a1, q] at *
    omega
  have hpowLower : 2 ^ (e + 2) < a1 := by
    rw [show 2 ^ (e + 2) = 4 * q by
      simp only [e, q, dyadicQ, pow_add]
      norm_num
      ring]
    simp only [a1]
    omega
  have hpowUpper : a1 <= 2 ^ ((e + 2) + 1) := by
    rw [show 2 ^ ((e + 2) + 1) = 8 * q by
      simp only [e, q, dyadicQ]
      rw [show (Nat.log 2 n - 4 + 2) + 1 = Nat.log 2 n - 4 + 3 by omega,
        pow_add]
      norm_num
      ring]
    simp only [a1]
    omega
  have hlemma := lemma_2_3_holds ((n + 1) / 2) baseWord a1 (e + 2)
    hbase hbaseStart haFour hpowLower hpowUpper
  dsimp only at hlemma
  have huEq : 2 ^ (e + 2 - 2) = q := by
    simp only [e, q, dyadicQ]
    congr 1
  rw [huEq] at hlemma
  have hambient : a1 + 2 * q <= (n + 1) / 2 := by
    simp only [lowerHalf, Finset.mem_Icc] at hbLower
    simp only [a1]
    omega
  have hbefore := hlemma.2.2.2.1 hambient
  intro hpred
  have hpredOdd : Odd (b1 - 2 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    refine ⟨B - q, ?_⟩
    omega
  have hhighOdd : Odd (b1 + 4 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 2 * q, by omega⟩
  have hhighBase : (b1 + 4 * q + 1) / 2 = a1 + 2 * q := by
    rcases hbOdd with ⟨B, hb⟩
    simp only [a1]
    omega
  have hpredBase : (b1 - 2 * q + 1) / 2 = a1 - q := by
    rcases hbOdd with ⟨B, hb⟩
    simp only [a1]
    omega
  have htraceBefore : OccursLeftOf (oddTrace word) (b1 + 4 * q) (b1 - 2 * q) := by
    apply occursLeftOf_oddTrace_of_oddBase hhighOdd hpredOdd
    rw [hhighBase, hpredBase]
    simpa only [baseWord] using hbefore
  have hhighEpi := oddEpilogue_closed_left hgamma hpred (by
    simpa only [word] using htraceBefore)
  have hhighLe := oddEpilogue_entry_le_last hgamma hbEnd hbLower hhighEpi
  omega


lemma occursLeftOf_evenTrace_of_evenBase {word : List Nat} {x y : Nat}
    (hx : Even x) (hy : Even y)
    (h : OccursLeftOf (evenBase word) (x / 2) (y / 2)) :
    OccursLeftOf (evenTrace word) x y := by
  have hlift := occursLeftOf_map (fun z : Nat => 2 * z) h
  change OccursLeftOf (evenLift (evenBase word)) (2 * (x / 2)) (2 * (y / 2)) at hlift
  rw [evenLift_evenBase] at hlift
  simpa [Nat.two_mul_div_two_of_even hx, Nat.two_mul_div_two_of_even hy] using hlift

lemma startsWith_evenBase_of_evenTrace {word : List Nat} {a : Nat}
    (h : StartsWith (evenTrace word) a) : StartsWith (evenBase word) (a / 2) := by
  unfold StartsWith at h ⊢
  simp only [evenBase, List.head?_map, h, Option.map_some]

lemma add_modulus_le_of_modEq_of_lt {m a b : Nat} (_hm : 0 < m)
    (hmod : Nat.ModEq m a b) (hab : a < b) : a + m <= b := by
  have hdvd : m ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
  have hdiff : 0 < b - a := by omega
  have hmLe : m <= b - a := Nat.le_of_dvd hdiff hdvd
  omega

lemma modulus_gap_or_gap {m a b : Nat} (hm : 0 < m)
    (hmod : Nat.ModEq m a b) (hne : a ≠ b) :
    a + m <= b \/ b + m <= a := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact Or.inl (add_modulus_le_of_modEq_of_lt hm hmod hab)
  · exact Or.inr (add_modulus_le_of_modEq_of_lt hm hmod.symm hba)

lemma thirty_two_dyadicQ_gt {n : Nat} (hn : 16 <= n) :
    n < 32 * dyadicQ n := by
  have hnPos : n ≠ 0 := by omega
  have hlog : 4 <= Nat.log 2 n := by
    rw [Nat.le_log_iff_pow_le (by norm_num) hnPos]
    norm_num
    exact hn
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rw [show 2 ^ (Nat.log 2 n + 1) = 32 * dyadicQ n by
    simp only [dyadicQ]
    rw [show Nat.log 2 n + 1 = (Nat.log 2 n - 4) + 5 by omega, pow_add]
    norm_num
    ring] at h
  exact h

lemma startsWith_prologue_of_startsWith {n : Nat} {word : List Nat} {a : Nat}
    (h : StartsWith word a) : StartsWith (prologue n word) a := by
  cases word with
  | nil => simp [StartsWith] at h
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using h
      subst first
      simp [prologue, StartsWith]

lemma PrefixCongruent.of_prefix {small large : List Nat} {k m : Nat}
    (hsmall : small <+: large) (hlarge : PrefixCongruent large k m)
    (hk : k <= small.length) : PrefixCongruent small k m := by
  obtain ⟨tail, rfl⟩ := hsmall
  refine ⟨hk, ?_⟩
  intro i hi j hj x y hx hy
  apply hlarge.2 i hi j hj x y
  · rw [List.getElem?_append_left (hi.trans_le hk)]
    exact hx
  · rw [List.getElem?_append_left (hj.trans_le hk)]
    exact hy

lemma left_endpoint_left_of_middle_of_right_endpoint_of_free
    {word : List Nat} (hnodup : word.Nodup) (hfree : ThreeFree word)
    {a d : Nat} (hd : 0 < d)
    (ha : a ∈ word) (hm : a + d ∈ word) (_hc : a + 2 * d ∈ word)
    (hcm : OccursLeftOf word (a + 2 * d) (a + d)) :
    OccursLeftOf word a (a + d) := by
  rcases occursLeftOf_total_of_mem hnodup ha hm (by omega) with ham | hma
  · exact ham
  · rcases hcm with ⟨i, j, hij, hi, hj⟩
    rcases hma with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' := getElem?_index_unique_of_nodup hnodup hj hj'
    subst j'
    exfalso
    exact hfree (containsThreeAP_of_decreasing_positions hij hjk hd hi hj hk)

lemma right_endpoint_left_of_middle_of_left_endpoint_of_free
    {word : List Nat} (hnodup : word.Nodup) (hfree : ThreeFree word)
    {a d : Nat} (hd : 0 < d)
    (_ha : a ∈ word) (hm : a + d ∈ word) (hc : a + 2 * d ∈ word)
    (ham : OccursLeftOf word a (a + d)) :
    OccursLeftOf word (a + 2 * d) (a + d) := by
  rcases occursLeftOf_total_of_mem hnodup hc hm (by omega) with hcm | hmc
  · exact hcm
  · rcases ham with ⟨i, j, hij, hi, hj⟩
    rcases hmc with ⟨j', k, hjk, hj', hk⟩
    have hjEq : j = j' := getElem?_index_unique_of_nodup hnodup hj hj'
    subst j'
    exfalso
    exact hfree (containsThreeAP_of_increasing_positions hij hjk hd hi hj hk)

lemma third_entry_occursLeftOf_of_mem {word : List Nat} {a b c x : Nat}
    (ha : word[0]? = some a) (hb : word[1]? = some b) (hc : word[2]? = some c)
    (hx : x ∈ word) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    OccursLeftOf word c x := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨hjLength, _⟩ := List.getElem?_eq_some_iff.mp hj
  have hjZero : j ≠ 0 := by
    intro h
    subst j
    exact hxa (Option.some.inj (hj.symm.trans ha))
  have hjOne : j ≠ 1 := by
    intro h
    subst j
    exact hxb (Option.some.inj (hj.symm.trans hb))
  have hjTwo : j ≠ 2 := by
    intro h
    subst j
    exact hxc (Option.some.inj (hj.symm.trans hc))
  exact ⟨2, j, by omega, hc, hj⟩

/-- The local even-trace obstruction used in the middle case of Theorem 2.6. -/
lemma evenTrace_middle_case_impossible {n : Nat} {gamma : List Nat}
    {c1 c2 c3 q : Nat}
    (hgamma : IsTheta n gamma)
    (hq : q = dyadicQ n)
    (hcStart : StartsWith (evenTrace gamma) c1)
    (hc1 : (evenTrace gamma)[0]? = some c1)
    (hc2 : (evenTrace gamma)[1]? = some c2)
    (hc3 : (evenTrace gamma)[2]? = some c3)
    (hc1Even : Even c1)
    (hc2Eq : c2 = c1 + 4 * q) (hc3Eq : c3 = c1 + 2 * q)
    (hcLower : 16 * q < c1) : False := by
  have hqPos : 0 < q := by simpa only [hq] using dyadicQ_pos n
  let traceWord := evenTrace gamma
  have hnodup : traceWord.Nodup := (isTheta_nodup hgamma).filter _
  have hfree : ThreeFree traceWord := evenTrace_threeFree hgamma
  have hthetaBase := isTheta_evenBase hgamma
  have hstartBase : StartsWith (evenBase gamma) (c1 / 2) :=
    startsWith_evenBase_of_evenTrace hcStart
  let l1 := c1 - 2 * q
  let l2 := c1 - 4 * q
  let l3 := c1 - 6 * q
  let target := c1 - 10 * q
  have hvalues : ∀ z ∈ [l1, l2, l3, target], z ∈ evenTrace gamma := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    all_goals
      apply List.mem_filter.mpr
      constructor
      · apply mem_of_mem_segment_of_isTheta hgamma
        simp only [segment, Finset.mem_Icc, l1, l2, l3, target]
        have hc1Mem : c1 ∈ gamma := (List.mem_filter.mp (mem_of_startsWith hcStart)).1
        have hc1Segment := mem_segment_of_mem_of_isTheta hgamma hc1Mem
        simp only [segment, Finset.mem_Icc] at hc1Segment
        omega
      · apply decide_eq_true
        rcases hc1Even with ⟨C, hc⟩
        simp only [l1, l2, l3, target]
        first
        | exact ⟨C - q, by omega⟩
        | exact ⟨C - 2 * q, by omega⟩
        | exact ⟨C - 3 * q, by omega⟩
        | exact ⟨C - 5 * q, by omega⟩
  have hl1 := hvalues l1 (by simp)
  have hl2 := hvalues l2 (by simp)
  have hl3 := hvalues l3 (by simp)
  have ht := hvalues target (by simp)
  have hc3BeforeL2 : OccursLeftOf traceWord c3 l2 := by
    apply third_entry_occursLeftOf_of_mem hc1 hc2 hc3 hl2
    all_goals simp only [l2, hc2Eq, hc3Eq] <;> omega
  have hc3BeforeL1 : OccursLeftOf traceWord c3 l1 := by
    apply third_entry_occursLeftOf_of_mem hc1 hc2 hc3 hl1
    all_goals simp only [l1, hc2Eq, hc3Eq] <;> omega
  have hl2BeforeL3 : OccursLeftOf traceWord l2 l3 := by
    have hl1Even : Even l1 := by
      rcases hc1Even with ⟨C, hc⟩
      exact ⟨C - q, by simp only [l1]; omega⟩
    have hl2Even : Even l2 := by
      rcases hc1Even with ⟨C, hc⟩
      exact ⟨C - 2 * q, by simp only [l2]; omega⟩
    have hl3Even : Even l3 := by
      rcases hc1Even with ⟨C, hc⟩
      exact ⟨C - 3 * q, by simp only [l3]; omega⟩
    have hl1Segment := evenHalf_mem_segment
      (mem_segment_of_mem_of_isTheta hgamma (List.mem_filter.mp hl1).1) hl1Even
    have hl2Segment := evenHalf_mem_segment
      (mem_segment_of_mem_of_isTheta hgamma (List.mem_filter.mp hl2).1) hl2Even
    have hl3Segment := evenHalf_mem_segment
      (mem_segment_of_mem_of_isTheta hgamma (List.mem_filter.mp hl3).1) hl3Even
    have hmean : l3 / 2 + l1 / 2 = 2 * (l2 / 2) := by
      rcases hc1Even with ⟨C, hc⟩
      simp only [l1, l2, l3]
      omega
    have hdistX : Nat.dist (c1 / 2) (l3 / 2) = 3 * q := by
      rcases hc1Even with ⟨C, hc⟩
      simp only [l3]
      unfold Nat.dist
      omega
    have hdistZ : Nat.dist (c1 / 2) (l2 / 2) = 2 * q := by
      rcases hc1Even with ⟨C, hc⟩
      simp only [l2]
      unfold Nat.dist
      omega
    have hdegree : binaryCongruenceDegree (c1 / 2) (l3 / 2) <
        binaryCongruenceDegree (c1 / 2) (l2 / 2) := by
      simp only [binaryCongruenceDegree, hdistX, hdistZ, hq, dyadicQ]
      rw [factorization_three_mul_pow_two, factorization_two_mul_pow_two]
      omega
    have hforced := theorem_2_4_holds (n / 2) (evenBase gamma) (c1 / 2)
      (l3 / 2) (l1 / 2) (l2 / 2) hthetaBase hstartBase
      hl3Segment hl1Segment hl2Segment hmean (by
        have hne : c1 / 2 ≠ l2 / 2 := by
          rcases hc1Even with ⟨C, hc⟩
          simp only [l2]
          omega
        simpa using hne) (by
          have hne : c1 / 2 ≠ l3 / 2 := by
            rcases hc1Even with ⟨C, hc⟩
            simp only [l3]
            omega
          simpa using hne) hdegree
    exact occursLeftOf_evenTrace_of_evenBase hl2Even hl3Even hforced.1
  have htBeforeL2 : OccursLeftOf traceWord target l2 := by
    have h := left_endpoint_left_of_middle_of_right_endpoint_of_free
      hnodup hfree (a := target) (d := 6 * q) (by omega) ht
      (by convert hl2 using 1 <;> simp only [target, l2] <;> omega)
      (by convert (show c3 ∈ traceWord from List.mem_iff_getElem?.mpr ⟨2, hc3⟩)
          using 1 <;> simp only [target, hc3Eq] <;> omega)
      (by convert hc3BeforeL2 using 1 <;> simp only [target, l2, hc3Eq] <;> omega)
    convert h using 1 <;> simp only [target, l2] <;> omega
  have hl3BeforeL1 : OccursLeftOf traceWord l3 l1 := by
    have h := left_endpoint_left_of_middle_of_right_endpoint_of_free
      hnodup hfree (a := l3) (d := 4 * q) (by omega) hl3
      (by convert hl1 using 1 <;> simp only [l3, l1] <;> omega)
      (by convert (show c3 ∈ traceWord from List.mem_iff_getElem?.mpr ⟨2, hc3⟩)
          using 1 <;> simp only [l3, hc3Eq] <;> omega)
      (by convert hc3BeforeL1 using 1 <;> simp only [l3, l1, hc3Eq] <;> omega)
    convert h using 1 <;> simp only [l3, l1] <;> omega
  have hl3BeforeTarget : OccursLeftOf traceWord l3 target := by
    rcases occursLeftOf_total_of_mem hnodup hl3 ht (by
      simp only [l3, target]
      omega) with h | h
    · exact h
    · have hright := right_endpoint_left_of_middle_of_left_endpoint_of_free
        hnodup hfree (a := target) (d := 4 * q) (by omega) ht
        (by convert hl3 using 1 <;> simp only [target, l3] <;> omega)
        (by convert hl1 using 1 <;> simp only [target, l1] <;> omega) (by
          convert h using 1 <;> simp only [target, l3] <;> omega)
      exact False.elim ((occursLeftOf_asymm hnodup hl3BeforeL1) (by
        convert hright using 1 <;> simp only [target, l3, l1] <;> omega))
  have hcycle := occursLeftOf_trans hnodup
    (occursLeftOf_trans hnodup hl2BeforeL3 hl3BeforeTarget) htBeforeL2
  exact (occursLeftOf_asymm hnodup hcycle) hcycle

/-- The largest even integer at most `n`. -/
def reflectedActiveAmbient (n : Nat) : Nat :=
  2 * (n / 2)

/-- Reflection in the odd center immediately above `reflectedActiveAmbient n`.
This swaps parity whether `n` is even or odd. -/
def activeReflection (n x : Nat) : Nat :=
  reflectedActiveAmbient n + 1 - x

/-- The active odd list, oriented from its boundary endpoint. -/
def oddBoundaryActiveList (n : Nat) (gamma : List Nat) : List Nat :=
  epilogue n (oddTrace gamma)

/-- The active even list, oriented from its boundary endpoint. -/
def evenBoundaryActiveList (n : Nat) (gamma : List Nat) : List Nat :=
  prologue n (evenTrace gamma)

/-- The even active list reflected into the odd, lower-half role. -/
def reflectedOddActiveList (n : Nat) (gamma : List Nat) : List Nat :=
  (evenBoundaryActiveList n gamma).map (activeReflection n)

/-- The odd active list reflected into the even, upper-half role. -/
def reflectedEvenActiveList (n : Nat) (gamma : List Nat) : List Nat :=
  (oddBoundaryActiveList n gamma).map (activeReflection n)

lemma reflectedActiveAmbient_le (n : Nat) : reflectedActiveAmbient n ≤ n := by
  simp only [reflectedActiveAmbient]
  omega

lemma reflectedActiveAmbient_eq_self_or_pred (n : Nat) :
    reflectedActiveAmbient n = n ∨ reflectedActiveAmbient n + 1 = n := by
  simp only [reflectedActiveAmbient]
  omega

lemma activeReflection_involutive_of_mem_segment {n x : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n)) :
    activeReflection n (activeReflection n x) = x := by
  simp only [segment, Finset.mem_Icc] at hx
  simp only [activeReflection]
  omega

lemma activeReflection_injective_on_segment (n : Nat) :
    Set.InjOn (activeReflection n) (segment (reflectedActiveAmbient n)) := by
  intro x hx y hy hxy
  change x ∈ segment (reflectedActiveAmbient n) at hx
  change y ∈ segment (reflectedActiveAmbient n) at hy
  simp only [segment, Finset.mem_Icc] at hx hy
  simp only [activeReflection] at hxy
  omega

lemma activeReflection_of_even_upper {n y : Nat}
    (hyUpper : y ∈ upperHalf n) (hyEven : Even y) :
    activeReflection n y ∈ lowerHalf (reflectedActiveAmbient n) ∧
      Odd (activeReflection n y) := by
  rcases hyEven with ⟨k, hk⟩
  simp only [upperHalf, lowerHalf, Finset.mem_Icc] at hyUpper ⊢
  simp only [activeReflection, reflectedActiveAmbient]
  constructor
  · constructor <;> omega
  · refine ⟨n / 2 - k, ?_⟩
    omega

lemma activeReflection_of_odd_lower {n x : Nat}
    (hxLower : x ∈ lowerHalf n) (hxOdd : Odd x) :
    activeReflection n x ∈ upperHalf (reflectedActiveAmbient n) ∧
      Even (activeReflection n x) := by
  rcases hxOdd with ⟨k, hk⟩
  simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxLower ⊢
  simp only [activeReflection, reflectedActiveAmbient]
  constructor
  · constructor <;> omega
  · refine ⟨n / 2 - k, ?_⟩
    omega

lemma activeReflection_separated {n x y : Nat}
    (hxLower : x ∈ lowerHalf n) (hxOdd : Odd x)
    (hyUpper : y ∈ upperHalf n) (hyEven : Even y)
    (hxy : 2 * x ≤ y) (hreflection : n < 2 * y - x) :
    2 * activeReflection n y ≤ activeReflection n x ∧
      reflectedActiveAmbient n <
        2 * activeReflection n x - activeReflection n y := by
  have hxData := activeReflection_of_odd_lower hxLower hxOdd
  have hyData := activeReflection_of_even_upper hyUpper hyEven
  simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxLower hyUpper
  simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxData hyData
  simp only [activeReflection, reflectedActiveAmbient] at *
  constructor <;> omega

/-- At the original ambient `n`, reflected strict separation can fail only in
the odd-ambient equality case `y = 2x`. -/
lemma activeReflection_originalAmbient_separation {n x y : Nat}
    (hxLower : x ∈ lowerHalf n) (hxOdd : Odd x)
    (hyUpper : y ∈ upperHalf n) (hyEven : Even y)
    (hxy : 2 * x ≤ y) :
    n ≤ 2 * activeReflection n x - activeReflection n y ∧
      (n < 2 * activeReflection n x - activeReflection n y ↔
        Even n ∨ 2 * x < y) := by
  have hxData := activeReflection_of_odd_lower hxLower hxOdd
  have hyData := activeReflection_of_even_upper hyUpper hyEven
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨k, hk⟩
    simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxLower hyUpper
    simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxData hyData
    simp only [activeReflection, reflectedActiveAmbient]
    constructor
    · omega
    · constructor
      · exact fun _ => Or.inl ⟨k, hk⟩
      · intro _
        omega
  · rcases hnOdd with ⟨k, hk⟩
    have hnNotEven : ¬ Even n := Nat.not_even_iff_odd.mpr ⟨k, hk⟩
    simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxLower hyUpper
    simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxData hyData
    simp only [activeReflection, reflectedActiveAmbient]
    constructor
    · omega
    · constructor
      · intro hstrict
        exact Or.inr (by omega)
      · rintro (heven | hstrict)
        · exact False.elim (hnNotEven heven)
        · omega

lemma activeReflection_originalAmbient_dichotomy {n x y : Nat}
    (hxLower : x ∈ lowerHalf n) (hxOdd : Odd x)
    (hyUpper : y ∈ upperHalf n) (hyEven : Even y)
    (hxy : 2 * x ≤ y) :
    n < 2 * activeReflection n x - activeReflection n y ∨
      (Odd n ∧ y = 2 * x) := by
  have hcharacterization := activeReflection_originalAmbient_separation
    hxLower hxOdd hyUpper hyEven hxy
  by_cases hstrict : n < 2 * activeReflection n x - activeReflection n y
  · exact Or.inl hstrict
  · right
    have hnotEven : ¬ Even n := by
      intro hnEven
      exact hstrict (hcharacterization.2.2 (Or.inl hnEven))
    have hnotSourceStrict : ¬ 2 * x < y := by
      intro hsource
      exact hstrict (hcharacterization.2.2 (Or.inr hsource))
    exact ⟨Nat.not_even_iff_odd.mp hnotEven, by omega⟩

lemma oddBoundaryActiveList_length (n : Nat) (gamma : List Nat) :
    (oddBoundaryActiveList n gamma).length =
      (epilogue n (oddTrace gamma)).length := rfl

lemma evenBoundaryActiveList_length (n : Nat) (gamma : List Nat) :
    (evenBoundaryActiveList n gamma).length =
      (prologue n (evenTrace gamma)).length := rfl

lemma reflectedOddActiveList_length (n : Nat) (gamma : List Nat) :
    (reflectedOddActiveList n gamma).length =
      (prologue n (evenTrace gamma)).length := by
  simp [reflectedOddActiveList, evenBoundaryActiveList]

lemma reflectedEvenActiveList_length (n : Nat) (gamma : List Nat) :
    (reflectedEvenActiveList n gamma).length =
      (epilogue n (oddTrace gamma)).length := by
  simp [reflectedEvenActiveList, oddBoundaryActiveList]

/-- The list-level data used by the numeric part of the active-block
argument.  It deliberately does not assert that the lists arise as traces of
a reflected full `Theta_12` word. -/
structure BoundaryActiveListProfile (N : Nat) (oddList evenList : List Nat) : Prop where
  oddNodup : oddList.Nodup
  evenNodup : evenList.Nodup
  oddLower : ∀ x ∈ oddList, x ∈ lowerHalf N
  evenUpper : ∀ y ∈ evenList, y ∈ upperHalf N
  oddParity : ∀ x ∈ oddList, Odd x
  evenParity : ∀ y ∈ evenList, Even y
  separated : ∀ x ∈ oddList, ∀ y ∈ evenList,
    2 * x ≤ y ∧ N < 2 * y - x

lemma oddBoundaryActiveList_nodup {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) :
    (oddBoundaryActiveList n gamma).Nodup := by
  have hactive := oddActiveBlock_nodup hgamma
  simpa [oddBoundaryActiveList, oddActiveBlock] using hactive

lemma evenBoundaryActiveList_nodup {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) :
    (evenBoundaryActiveList n gamma).Nodup := by
  simpa [evenBoundaryActiveList, evenActiveBlock] using
    evenActiveBlock_nodup hgamma

lemma oddBoundaryActiveList_mem_lowerHalf {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ oddBoundaryActiveList n gamma, x ∈ lowerHalf n := by
  rcases hstanding.2 with ⟨b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  intro x hx
  have hstart : StartsWith (reversal (oddTrace gamma)) b1 :=
    startsWith_reversal_of_endsWith hbEnd
  apply mem_lowerHalf_of_mem_prologue hstart hbLower
  simpa [oddBoundaryActiveList, epilogue] using hx

lemma evenBoundaryActiveList_mem_upperHalf {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ y ∈ evenBoundaryActiveList n gamma, y ∈ upperHalf n := by
  rcases hstanding.2 with ⟨b1, c1, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  intro y hy
  apply mem_upperHalf_of_mem_prologue hcStart hcUpper
  simpa [evenBoundaryActiveList] using hy

lemma oddBoundaryActiveList_odd {n : Nat} {gamma : List Nat} {x : Nat}
    (hx : x ∈ oddBoundaryActiveList n gamma) : Odd x := by
  have hxActive : x ∈ oddActiveBlock n (oddTrace gamma) := by
    simpa [oddBoundaryActiveList, oddActiveBlock] using hx
  exact of_decide_eq_true
    (List.mem_filter.mp (oddActiveBlock_mem_oddTrace hxActive)).2

lemma evenBoundaryActiveList_even {n : Nat} {gamma : List Nat} {y : Nat}
    (hy : y ∈ evenBoundaryActiveList n gamma) : Even y := by
  have hyActive : y ∈ evenActiveBlock n (evenTrace gamma) := by
    simpa [evenBoundaryActiveList, evenActiveBlock] using hy
  exact of_decide_eq_true
    (List.mem_filter.mp (evenActiveBlock_mem_evenTrace hyActive)).2

lemma oddBoundaryActiveList_mem_oddActiveBlock {n : Nat} {gamma : List Nat}
    {x : Nat} (hx : x ∈ oddBoundaryActiveList n gamma) :
    x ∈ oddActiveBlock n (oddTrace gamma) := by
  simpa [oddBoundaryActiveList, oddActiveBlock] using hx

lemma evenBoundaryActiveList_mem_evenActiveBlock {n : Nat} {gamma : List Nat}
    {y : Nat} (hy : y ∈ evenBoundaryActiveList n gamma) :
    y ∈ evenActiveBlock n (evenTrace gamma) := by
  simpa [evenBoundaryActiveList, evenActiveBlock] using hy

lemma activeReflection_source_even_mem_segment {n y : Nat}
    (hyUpper : y ∈ upperHalf n) (hyEven : Even y) :
    y ∈ segment (reflectedActiveAmbient n) := by
  rcases hyEven with ⟨k, hk⟩
  simp only [upperHalf, segment, Finset.mem_Icc] at hyUpper ⊢
  simp only [reflectedActiveAmbient]
  omega

lemma activeReflection_source_odd_mem_segment {n x : Nat}
    (hxLower : x ∈ lowerHalf n) :
    x ∈ segment (reflectedActiveAmbient n) := by
  simp only [lowerHalf, segment, Finset.mem_Icc] at hxLower ⊢
  simp only [reflectedActiveAmbient]
  omega

lemma activeReflection_modEq {n m x y : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n))
    (hy : y ∈ segment (reflectedActiveAmbient n))
    (hxy : Nat.ModEq m x y) :
    Nat.ModEq m (activeReflection n x) (activeReflection n y) := by
  have hxBound : x ≤ reflectedActiveAmbient n + 1 := by
    simp only [segment, Finset.mem_Icc] at hx
    omega
  have hyBound : y ≤ reflectedActiveAmbient n + 1 := by
    simp only [segment, Finset.mem_Icc] at hy
    omega
  exact Nat.ModEq.sub hxBound hyBound Nat.ModEq.rfl hxy

lemma activeReflection_dist {n x y : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n))
    (hy : y ∈ segment (reflectedActiveAmbient n)) :
    Nat.dist (activeReflection n x) (activeReflection n y) = Nat.dist x y := by
  simp only [segment, Finset.mem_Icc] at hx hy
  simp only [activeReflection]
  unfold Nat.dist
  omega

lemma binaryCongruenceDegree_activeReflection {n x y : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n))
    (hy : y ∈ segment (reflectedActiveAmbient n)) :
    binaryCongruenceDegree (activeReflection n x) (activeReflection n y) =
      binaryCongruenceDegree x y := by
  unfold binaryCongruenceDegree
  rw [activeReflection_dist hx hy]

lemma PrefixCongruent.map_activeReflection {n k m : Nat} {word : List Nat}
    (hword : ∀ x ∈ word, x ∈ segment (reflectedActiveAmbient n))
    (hprefix : PrefixCongruent word k m) :
    PrefixCongruent (word.map (activeReflection n)) k m := by
  refine ⟨by simpa using hprefix.1, ?_⟩
  intro i hi j hj x y hx hy
  obtain ⟨x0, hx0, hxEq⟩ := exists_of_getElem?_map_eq_some hx
  obtain ⟨y0, hy0, hyEq⟩ := exists_of_getElem?_map_eq_some hy
  subst x
  subst y
  apply activeReflection_modEq (hword x0 (List.mem_iff_getElem?.mpr ⟨i, hx0⟩))
    (hword y0 (List.mem_iff_getElem?.mpr ⟨j, hy0⟩))
  exact hprefix.2 i hi j hj x0 y0 hx0 hy0

lemma reflectedOddActiveList_nodup {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    (reflectedOddActiveList n gamma).Nodup := by
  unfold reflectedOddActiveList
  apply List.Nodup.map_on _ (evenBoundaryActiveList_nodup hstanding.1.1)
  intro x hx y hy hxy
  apply activeReflection_injective_on_segment n
  · exact activeReflection_source_even_mem_segment
      (evenBoundaryActiveList_mem_upperHalf hstanding x hx)
      (evenBoundaryActiveList_even hx)
  · exact activeReflection_source_even_mem_segment
      (evenBoundaryActiveList_mem_upperHalf hstanding y hy)
      (evenBoundaryActiveList_even hy)
  · exact hxy

lemma reflectedEvenActiveList_nodup {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    (reflectedEvenActiveList n gamma).Nodup := by
  unfold reflectedEvenActiveList
  apply List.Nodup.map_on _ (oddBoundaryActiveList_nodup hstanding.1.1)
  intro x hx y hy hxy
  apply activeReflection_injective_on_segment n
  · exact activeReflection_source_odd_mem_segment
      (oddBoundaryActiveList_mem_lowerHalf hstanding x hx)
  · exact activeReflection_source_odd_mem_segment
      (oddBoundaryActiveList_mem_lowerHalf hstanding y hy)
  · exact hxy

lemma reflectedOddActiveList_mem_lowerHalf {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ reflectedOddActiveList n gamma,
      x ∈ lowerHalf (reflectedActiveAmbient n) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact (activeReflection_of_even_upper
    (evenBoundaryActiveList_mem_upperHalf hstanding y hy)
    (evenBoundaryActiveList_even hy)).1

lemma reflectedEvenActiveList_mem_upperHalf {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ y ∈ reflectedEvenActiveList n gamma,
      y ∈ upperHalf (reflectedActiveAmbient n) := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact (activeReflection_of_odd_lower
    (oddBoundaryActiveList_mem_lowerHalf hstanding x hx)
    (oddBoundaryActiveList_odd hx)).1

lemma reflectedOddActiveList_odd {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ reflectedOddActiveList n gamma, Odd x := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact (activeReflection_of_even_upper
    (evenBoundaryActiveList_mem_upperHalf hstanding y hy)
    (evenBoundaryActiveList_even hy)).2

lemma reflectedEvenActiveList_even {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ y ∈ reflectedEvenActiveList n gamma, Even y := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact (activeReflection_of_odd_lower
    (oddBoundaryActiveList_mem_lowerHalf hstanding x hx)
    (oddBoundaryActiveList_odd hx)).2

lemma reflectedActiveLists_separated {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∀ x ∈ reflectedOddActiveList n gamma,
      ∀ y ∈ reflectedEvenActiveList n gamma,
        2 * x ≤ y ∧
          reflectedActiveAmbient n < 2 * y - x := by
  intro reflectedOdd hreflectedOdd reflectedEven hreflectedEven
  rcases List.mem_map.mp hreflectedOdd with ⟨evenSource, hevenSource, rfl⟩
  rcases List.mem_map.mp hreflectedEven with ⟨oddSource, hoddSource, rfl⟩
  have hsource := activeBlocks_separated hstanding oddSource
    (oddBoundaryActiveList_mem_oddActiveBlock hoddSource) evenSource
    (evenBoundaryActiveList_mem_evenActiveBlock hevenSource)
  exact activeReflection_separated
    (oddBoundaryActiveList_mem_lowerHalf hstanding oddSource hoddSource)
    (oddBoundaryActiveList_odd hoddSource)
    (evenBoundaryActiveList_mem_upperHalf hstanding evenSource hevenSource)
    (evenBoundaryActiveList_even hevenSource) hsource.1 hsource.2

lemma reflectedActivePair_originalAmbient_separation
    {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    {oddSource evenSource : Nat}
    (hodd : oddSource ∈ oddBoundaryActiveList n gamma)
    (heven : evenSource ∈ evenBoundaryActiveList n gamma) :
    n ≤ 2 * activeReflection n oddSource - activeReflection n evenSource ∧
      (n < 2 * activeReflection n oddSource - activeReflection n evenSource ↔
        Even n ∨ 2 * oddSource < evenSource) := by
  have hsource := activeBlocks_separated hstanding oddSource
    (oddBoundaryActiveList_mem_oddActiveBlock hodd) evenSource
    (evenBoundaryActiveList_mem_evenActiveBlock heven)
  exact activeReflection_originalAmbient_separation
    (oddBoundaryActiveList_mem_lowerHalf hstanding oddSource hodd)
    (oddBoundaryActiveList_odd hodd)
    (evenBoundaryActiveList_mem_upperHalf hstanding evenSource heven)
    (evenBoundaryActiveList_even heven) hsource.1

lemma reflectedActivePair_originalAmbient_dichotomy
    {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    {oddSource evenSource : Nat}
    (hodd : oddSource ∈ oddBoundaryActiveList n gamma)
    (heven : evenSource ∈ evenBoundaryActiveList n gamma) :
    n < 2 * activeReflection n oddSource - activeReflection n evenSource ∨
      (Odd n ∧ evenSource = 2 * oddSource) := by
  have hsource := activeBlocks_separated hstanding oddSource
    (oddBoundaryActiveList_mem_oddActiveBlock hodd) evenSource
    (evenBoundaryActiveList_mem_evenActiveBlock heven)
  exact activeReflection_originalAmbient_dichotomy
    (oddBoundaryActiveList_mem_lowerHalf hstanding oddSource hodd)
    (oddBoundaryActiveList_odd hodd)
    (evenBoundaryActiveList_mem_upperHalf hstanding evenSource heven)
    (evenBoundaryActiveList_even heven) hsource.1

/-- The reflected active lists satisfy exactly the parity, half, uniqueness,
and separation data used by the numeric active-block argument. -/
theorem reflectedActiveLists_profile {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    BoundaryActiveListProfile (reflectedActiveAmbient n)
      (reflectedOddActiveList n gamma) (reflectedEvenActiveList n gamma) := by
  exact ⟨reflectedOddActiveList_nodup hstanding,
    reflectedEvenActiveList_nodup hstanding,
    reflectedOddActiveList_mem_lowerHalf hstanding,
    reflectedEvenActiveList_mem_upperHalf hstanding,
    reflectedOddActiveList_odd hstanding,
    reflectedEvenActiveList_even hstanding,
    reflectedActiveLists_separated hstanding⟩

lemma reflectedOddActiveList_prefixCongruent {n k m : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hprefix : PrefixCongruent (evenBoundaryActiveList n gamma) k m) :
    PrefixCongruent (reflectedOddActiveList n gamma) k m := by
  unfold reflectedOddActiveList
  apply hprefix.map_activeReflection
  intro y hy
  exact activeReflection_source_even_mem_segment
    (evenBoundaryActiveList_mem_upperHalf hstanding y hy)
    (evenBoundaryActiveList_even hy)

lemma reflectedEvenActiveList_prefixCongruent {n k m : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hprefix : PrefixCongruent (oddBoundaryActiveList n gamma) k m) :
    PrefixCongruent (reflectedEvenActiveList n gamma) k m := by
  unfold reflectedEvenActiveList
  apply hprefix.map_activeReflection
  intro x hx
  exact activeReflection_source_odd_mem_segment
    (oddBoundaryActiveList_mem_lowerHalf hstanding x hx)

lemma evenBoundaryActiveList_prefixCongruent_of_evenTrace
    {n k m : Nat} {gamma : List Nat}
    (hk : k ≤ (prologue n (evenTrace gamma)).length)
    (htrace : PrefixCongruent (evenTrace gamma) k m) :
    PrefixCongruent (evenBoundaryActiveList n gamma) k m := by
  apply PrefixCongruent.of_prefix (prologue_prefix n (evenTrace gamma)) htrace
  simpa [evenBoundaryActiveList] using hk

lemma oddBoundaryActiveList_prefixCongruent_of_reversal
    {n k m : Nat} {gamma : List Nat}
    (hk : k ≤ (epilogue n (oddTrace gamma)).length)
    (htrace : PrefixCongruent (reversal (oddTrace gamma)) k m) :
    PrefixCongruent (oddBoundaryActiveList n gamma) k m := by
  change PrefixCongruent (prologue n (reversal (oddTrace gamma))) k m
  apply PrefixCongruent.of_prefix
    (prologue_prefix n (reversal (oddTrace gamma))) htrace
  simpa [epilogue] using hk

lemma reflectedOddActiveList_prefixCongruent_of_evenTrace
    {n k m : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hk : k ≤ (prologue n (evenTrace gamma)).length)
    (htrace : PrefixCongruent (evenTrace gamma) k m) :
    PrefixCongruent (reflectedOddActiveList n gamma) k m :=
  reflectedOddActiveList_prefixCongruent hstanding
    (evenBoundaryActiveList_prefixCongruent_of_evenTrace hk htrace)

lemma reflectedEvenActiveList_prefixCongruent_of_reversal
    {n k m : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hk : k ≤ (epilogue n (oddTrace gamma)).length)
    (htrace : PrefixCongruent (reversal (oddTrace gamma)) k m) :
    PrefixCongruent (reflectedEvenActiveList n gamma) k m :=
  reflectedEvenActiveList_prefixCongruent hstanding
    (oddBoundaryActiveList_prefixCongruent_of_reversal hk htrace)

lemma startsWith_map_activeReflection {n : Nat} {word : List Nat} {x : Nat}
    (h : StartsWith word x) :
    StartsWith (word.map (activeReflection n)) (activeReflection n x) := by
  unfold StartsWith at h ⊢
  simp only [List.head?_map, h, Option.map_some]

/-- Reflection swaps the two boundary endpoints while preserving their
boundary-oriented list positions. -/
lemma reflectedActiveLists_endpoints {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    ∃ b c : Nat,
      EndsWith (oddTrace gamma) b ∧ StartsWith (evenTrace gamma) c ∧
      StartsWith (reflectedOddActiveList n gamma) (activeReflection n c) ∧
      StartsWith (reflectedEvenActiveList n gamma) (activeReflection n b) := by
  rcases hstanding.2 with ⟨b, c, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  refine ⟨b, c, hbEnd, hcStart, ?_, ?_⟩
  · apply startsWith_map_activeReflection
    exact startsWith_prologue_of_startsWith hcStart
  · apply startsWith_map_activeReflection
    apply startsWith_prologue_of_startsWith
    exact startsWith_reversal_of_endsWith hbEnd


lemma coefficient_pos_of_modEq_le_of_ne {q b x d : Nat}
    (hxb : x ≠ b)
    (heq : b = x + (2 * q) * d) : 0 < d := by
  by_contra hd
  have : d = 0 := by omega
  subst d
  simp only [Nat.mul_zero, Nat.add_zero] at heq
  exact hxb heq.symm

lemma coefficient_ne_of_values_ne {q b x y dx dy : Nat}
    (hx : b = x + (2 * q) * dx) (hy : b = y + (2 * q) * dy)
    (hxy : x ≠ y) : dx ≠ dy := by
  intro h
  subst dy
  exact hxy (by omega)

lemma values_ne_of_getElem?_ne_index {word : List Nat} {i j x y : Nat}
    (hword : word.Nodup) (hi : word[i]? = some x) (hj : word[j]? = some y)
    (hij : i ≠ j) : x ≠ y := by
  intro hxy
  subst y
  exact hij (getElem?_index_unique_of_nodup hword hi hj)

lemma six_mul_lt_of_three_distinct_predecessors {q b x₁ x₂ x₃ : Nat}
    (hx₁Pos : 0 < x₁) (hx₂Pos : 0 < x₂) (hx₃Pos : 0 < x₃)
    (hx₁Le : x₁ <= b) (hx₂Le : x₂ <= b) (hx₃Le : x₃ <= b)
    (hx₁b : x₁ ≠ b) (hx₂b : x₂ ≠ b) (hx₃b : x₃ ≠ b)
    (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃) (hx₂₃ : x₂ ≠ x₃)
    (hmod₁ : Nat.ModEq (2 * q) x₁ b)
    (hmod₂ : Nat.ModEq (2 * q) x₂ b)
    (hmod₃ : Nat.ModEq (2 * q) x₃ b) : 6 * q < b := by
  obtain ⟨d₁, hd₁⟩ := (Nat.modEq_iff_exists_eq_add hx₁Le).mp hmod₁
  obtain ⟨d₂, hd₂⟩ := (Nat.modEq_iff_exists_eq_add hx₂Le).mp hmod₂
  obtain ⟨d₃, hd₃⟩ := (Nat.modEq_iff_exists_eq_add hx₃Le).mp hmod₃
  have hd₁Eq : b = x₁ + (2 * q) * d₁ := by simpa [Nat.mul_comm] using hd₁
  have hd₂Eq : b = x₂ + (2 * q) * d₂ := by simpa [Nat.mul_comm] using hd₂
  have hd₃Eq : b = x₃ + (2 * q) * d₃ := by simpa [Nat.mul_comm] using hd₃
  have hd₁Pos := coefficient_pos_of_modEq_le_of_ne hx₁b hd₁Eq
  have hd₂Pos := coefficient_pos_of_modEq_le_of_ne hx₂b hd₂Eq
  have hd₃Pos := coefficient_pos_of_modEq_le_of_ne hx₃b hd₃Eq
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hlarge : 3 <= d₁ ∨ 3 <= d₂ ∨ 3 <= d₃ := by omega
  rcases hlarge with hlarge | hlarge | hlarge <;> nlinarith

lemma first_predecessor_among_three {q b x₁ x₂ x₃ : Nat}
    (hbUpper : b < 8 * q)
    (hx₁Pos : 0 < x₁) (hx₂Pos : 0 < x₂) (hx₃Pos : 0 < x₃)
    (hx₁Le : x₁ <= b) (hx₂Le : x₂ <= b) (hx₃Le : x₃ <= b)
    (hx₁b : x₁ ≠ b) (hx₂b : x₂ ≠ b) (hx₃b : x₃ ≠ b)
    (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃) (hx₂₃ : x₂ ≠ x₃)
    (hmod₁ : Nat.ModEq (2 * q) x₁ b)
    (hmod₂ : Nat.ModEq (2 * q) x₂ b)
    (hmod₃ : Nat.ModEq (2 * q) x₃ b) :
    x₁ = b - 2 * q ∨ x₂ = b - 2 * q ∨ x₃ = b - 2 * q := by
  obtain ⟨d₁, hd₁⟩ := (Nat.modEq_iff_exists_eq_add hx₁Le).mp hmod₁
  obtain ⟨d₂, hd₂⟩ := (Nat.modEq_iff_exists_eq_add hx₂Le).mp hmod₂
  obtain ⟨d₃, hd₃⟩ := (Nat.modEq_iff_exists_eq_add hx₃Le).mp hmod₃
  have hd₁Eq : b = x₁ + (2 * q) * d₁ := by simpa [Nat.mul_comm] using hd₁
  have hd₂Eq : b = x₂ + (2 * q) * d₂ := by simpa [Nat.mul_comm] using hd₂
  have hd₃Eq : b = x₃ + (2 * q) * d₃ := by simpa [Nat.mul_comm] using hd₃
  have hd₁Pos := coefficient_pos_of_modEq_le_of_ne hx₁b hd₁Eq
  have hd₂Pos := coefficient_pos_of_modEq_le_of_ne hx₂b hd₂Eq
  have hd₃Pos := coefficient_pos_of_modEq_le_of_ne hx₃b hd₃Eq
  have hd₁Le : d₁ <= 3 := by nlinarith
  have hd₂Le : d₂ <= 3 := by nlinarith
  have hd₃Le : d₃ <= 3 := by nlinarith
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hcover : d₁ = 1 ∨ d₂ = 1 ∨ d₃ = 1 := by omega
  rcases hcover with h | h | h
  · left
    subst d₁
    omega
  · right; left
    subst d₂
    omega
  · right; right
    subst d₃
    omega

lemma third_predecessor_among_three_without_first {q b x₁ x₂ x₃ : Nat}
    (hbUpper : b < 10 * q)
    (hx₁Pos : 0 < x₁) (hx₂Pos : 0 < x₂) (hx₃Pos : 0 < x₃)
    (hx₁Le : x₁ <= b) (hx₂Le : x₂ <= b) (hx₃Le : x₃ <= b)
    (hx₁b : x₁ ≠ b) (hx₂b : x₂ ≠ b) (hx₃b : x₃ ≠ b)
    (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃) (hx₂₃ : x₂ ≠ x₃)
    (hmod₁ : Nat.ModEq (2 * q) x₁ b)
    (hmod₂ : Nat.ModEq (2 * q) x₂ b)
    (hmod₃ : Nat.ModEq (2 * q) x₃ b)
    (hnotFirst₁ : x₁ ≠ b - 2 * q)
    (hnotFirst₂ : x₂ ≠ b - 2 * q)
    (hnotFirst₃ : x₃ ≠ b - 2 * q) :
    x₁ = b - 6 * q ∨ x₂ = b - 6 * q ∨ x₃ = b - 6 * q := by
  obtain ⟨d₁, hd₁⟩ := (Nat.modEq_iff_exists_eq_add hx₁Le).mp hmod₁
  obtain ⟨d₂, hd₂⟩ := (Nat.modEq_iff_exists_eq_add hx₂Le).mp hmod₂
  obtain ⟨d₃, hd₃⟩ := (Nat.modEq_iff_exists_eq_add hx₃Le).mp hmod₃
  have hd₁Eq : b = x₁ + (2 * q) * d₁ := by simpa [Nat.mul_comm] using hd₁
  have hd₂Eq : b = x₂ + (2 * q) * d₂ := by simpa [Nat.mul_comm] using hd₂
  have hd₃Eq : b = x₃ + (2 * q) * d₃ := by simpa [Nat.mul_comm] using hd₃
  have hd₁Pos := coefficient_pos_of_modEq_le_of_ne hx₁b hd₁Eq
  have hd₂Pos := coefficient_pos_of_modEq_le_of_ne hx₂b hd₂Eq
  have hd₃Pos := coefficient_pos_of_modEq_le_of_ne hx₃b hd₃Eq
  have hd₁Le : d₁ <= 4 := by nlinarith
  have hd₂Le : d₂ <= 4 := by nlinarith
  have hd₃Le : d₃ <= 4 := by nlinarith
  have hd₁NeOne : d₁ ≠ 1 := by intro h; subst d₁; apply hnotFirst₁; omega
  have hd₂NeOne : d₂ ≠ 1 := by intro h; subst d₂; apply hnotFirst₂; omega
  have hd₃NeOne : d₃ ≠ 1 := by intro h; subst d₃; apply hnotFirst₃; omega
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hcover : d₁ = 3 ∨ d₂ = 3 ∨ d₃ = 3 := by omega
  rcases hcover with h | h | h
  · left; subst d₁; omega
  · right; left; subst d₂; omega
  · right; right; subst d₃; omega

lemma third_or_fifth_predecessor_among_three_without_first {q b x₁ x₂ x₃ : Nat}
    (hbUpper : b < 12 * q)
    (hx₁Pos : 0 < x₁) (hx₂Pos : 0 < x₂) (hx₃Pos : 0 < x₃)
    (hx₁Le : x₁ <= b) (hx₂Le : x₂ <= b) (hx₃Le : x₃ <= b)
    (hx₁b : x₁ ≠ b) (hx₂b : x₂ ≠ b) (hx₃b : x₃ ≠ b)
    (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃) (hx₂₃ : x₂ ≠ x₃)
    (hmod₁ : Nat.ModEq (2 * q) x₁ b)
    (hmod₂ : Nat.ModEq (2 * q) x₂ b)
    (hmod₃ : Nat.ModEq (2 * q) x₃ b)
    (hnotFirst₁ : x₁ ≠ b - 2 * q)
    (hnotFirst₂ : x₂ ≠ b - 2 * q)
    (hnotFirst₃ : x₃ ≠ b - 2 * q) :
    (x₁ = b - 6 * q ∨ x₂ = b - 6 * q ∨ x₃ = b - 6 * q) ∨
      (x₁ = b - 10 * q ∨ x₂ = b - 10 * q ∨ x₃ = b - 10 * q) := by
  obtain ⟨d₁, hd₁⟩ := (Nat.modEq_iff_exists_eq_add hx₁Le).mp hmod₁
  obtain ⟨d₂, hd₂⟩ := (Nat.modEq_iff_exists_eq_add hx₂Le).mp hmod₂
  obtain ⟨d₃, hd₃⟩ := (Nat.modEq_iff_exists_eq_add hx₃Le).mp hmod₃
  have hd₁Eq : b = x₁ + (2 * q) * d₁ := by simpa [Nat.mul_comm] using hd₁
  have hd₂Eq : b = x₂ + (2 * q) * d₂ := by simpa [Nat.mul_comm] using hd₂
  have hd₃Eq : b = x₃ + (2 * q) * d₃ := by simpa [Nat.mul_comm] using hd₃
  have hd₁Pos := coefficient_pos_of_modEq_le_of_ne hx₁b hd₁Eq
  have hd₂Pos := coefficient_pos_of_modEq_le_of_ne hx₂b hd₂Eq
  have hd₃Pos := coefficient_pos_of_modEq_le_of_ne hx₃b hd₃Eq
  have hd₁Le : d₁ <= 5 := by nlinarith
  have hd₂Le : d₂ <= 5 := by nlinarith
  have hd₃Le : d₃ <= 5 := by nlinarith
  have hd₁NeOne : d₁ ≠ 1 := by intro h; subst d₁; apply hnotFirst₁; omega
  have hd₂NeOne : d₂ ≠ 1 := by intro h; subst d₂; apply hnotFirst₂; omega
  have hd₃NeOne : d₃ ≠ 1 := by intro h; subst d₃; apply hnotFirst₃; omega
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hcover : d₁ = 3 ∨ d₂ = 3 ∨ d₃ = 3 ∨ d₁ = 5 ∨ d₂ = 5 ∨ d₃ = 5 := by
    omega
  rcases hcover with h | h | h | h | h | h
  · left; left; subst d₁; omega
  · left; right; left; subst d₂; omega
  · left; right; right; subst d₃; omega
  · right; left; subst d₁; omega
  · right; right; left; subst d₂; omega
  · right; right; right; subst d₃; omega

/-- The order-theoretic core of the odd-end forcing step common to the three
numeric cases in Theorem 2.6. -/
lemma ambient_lt_of_oddEpilogue_forcing {n : Nat} {gamma : List Nat}
    {b x y z : Nat}
    (hgamma : IsTheta n gamma)
    (hbEnd : EndsWith (oddTrace gamma) b)
    (hbLower : b ∈ lowerHalf n)
    (hbOdd : Odd b) (hxOdd : Odd x) (hyOdd : Odd y) (hzOdd : Odd z)
    (hx : x ∈ epilogue n (oddTrace gamma))
    (hmean : x + y = 2 * z)
    (hbZ : b ≠ z) (hbX : b ≠ x)
    (hdegree : binaryCongruenceDegree ((b + 1) / 2) ((x + 1) / 2) <
      binaryCongruenceDegree ((b + 1) / 2) ((z + 1) / 2))
    (hyPos : 0 < y) (hzPos : 0 < z) (hzLeY : z <= y) (hbLtZ : b < z) :
    n < y := by
  have hxTrace : x ∈ oddTrace gamma := by
    apply oddActiveBlock_mem_oddTrace (n := n)
    simpa only [oddActiveBlock, List.mem_reverse] using hx
  have hxGamma : x ∈ gamma := (List.mem_filter.mp hxTrace).1
  have hxSegment := mem_segment_of_mem_of_isTheta hgamma hxGamma
  by_contra hnot
  have hySegment : y ∈ segment n := by
    simp only [segment, Finset.mem_Icc]
    omega
  have hzSegment : z ∈ segment n := by
    simp only [segment, Finset.mem_Icc] at hySegment ⊢
    omega
  have hzEpilogue := oddEpilogue_forced_middle hgamma hbEnd hxSegment hySegment
    hzSegment hbOdd hxOdd hyOdd hzOdd hmean hbZ hbX hdegree hx
  have hzLe := oddEpilogue_entry_le_last hgamma hbEnd hbLower hzEpilogue
  omega

lemma ambient_lt_b_add_ten_of_sub_two_mem {n : Nat} {gamma : List Nat} {b : Nat}
    (hgamma : IsTheta n gamma) (hbEnd : EndsWith (oddTrace gamma) b)
    (hbLower : b ∈ lowerHalf n) (hbOdd : Odd b)
    (hbTwo : 2 * dyadicQ n < b)
    (hx : b - 2 * dyadicQ n ∈ epilogue n (oddTrace gamma)) :
    n < b + 10 * dyadicQ n := by
  let q := dyadicQ n
  have hqPos : 0 < q := dyadicQ_pos n
  have hxOdd : Odd (b - 2 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B - q, by omega⟩
  have hyOdd : Odd (b + 10 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 5 * q, by omega⟩
  have hzOdd : Odd (b + 4 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 2 * q, by omega⟩
  have hxHalf : (b - 2 * q + 1) / 2 = (b + 1) / 2 - q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hzHalf : (b + 4 * q + 1) / 2 = (b + 1) / 2 + 2 * q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hdistX : Nat.dist ((b + 1) / 2) ((b - 2 * q + 1) / 2) = q := by
    rw [hxHalf]
    unfold Nat.dist
    omega
  have hdistZ : Nat.dist ((b + 1) / 2) ((b + 4 * q + 1) / 2) = 2 * q := by
    rw [hzHalf]
    unfold Nat.dist
    omega
  have hfactorQ : q.factorization 2 = Nat.log 2 n - 4 := by
    exact Nat.factorization_pow_self Nat.prime_two
  have hfactorTwo : (2 * q).factorization 2 = Nat.log 2 n - 4 + 1 := by
    simpa only [q, dyadicQ] using factorization_two_mul_pow_two (Nat.log 2 n - 4)
  apply ambient_lt_of_oddEpilogue_forcing hgamma hbEnd hbLower hbOdd hxOdd hyOdd hzOdd
    (by simpa only [q] using hx) (by omega) (by omega) (by omega)
  · simp only [binaryCongruenceDegree, hdistX, hdistZ, hfactorQ, hfactorTwo]
    omega
  all_goals omega

lemma ambient_lt_b_add_fourteen_of_sub_six_mem {n : Nat} {gamma : List Nat} {b : Nat}
    (hgamma : IsTheta n gamma) (hbEnd : EndsWith (oddTrace gamma) b)
    (hbLower : b ∈ lowerHalf n) (hbOdd : Odd b)
    (hbSix : 6 * dyadicQ n < b)
    (hx : b - 6 * dyadicQ n ∈ epilogue n (oddTrace gamma)) :
    n < b + 14 * dyadicQ n := by
  let q := dyadicQ n
  have hqPos : 0 < q := dyadicQ_pos n
  have hxOdd : Odd (b - 6 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B - 3 * q, by omega⟩
  have hyOdd : Odd (b + 14 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 7 * q, by omega⟩
  have hzOdd : Odd (b + 4 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 2 * q, by omega⟩
  have hxHalf : (b - 6 * q + 1) / 2 = (b + 1) / 2 - 3 * q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hzHalf : (b + 4 * q + 1) / 2 = (b + 1) / 2 + 2 * q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hdistX : Nat.dist ((b + 1) / 2) ((b - 6 * q + 1) / 2) = 3 * q := by
    rw [hxHalf]
    unfold Nat.dist
    omega
  have hdistZ : Nat.dist ((b + 1) / 2) ((b + 4 * q + 1) / 2) = 2 * q := by
    rw [hzHalf]
    unfold Nat.dist
    omega
  have hfactorThree : (3 * q).factorization 2 = Nat.log 2 n - 4 := by
    simpa only [q, dyadicQ] using factorization_three_mul_pow_two (Nat.log 2 n - 4)
  have hfactorTwo : (2 * q).factorization 2 = Nat.log 2 n - 4 + 1 := by
    simpa only [q, dyadicQ] using factorization_two_mul_pow_two (Nat.log 2 n - 4)
  apply ambient_lt_of_oddEpilogue_forcing hgamma hbEnd hbLower hbOdd hxOdd hyOdd hzOdd
    (by simpa only [q] using hx) (by omega) (by omega) (by omega)
  · simp only [binaryCongruenceDegree, hdistX, hdistZ, hfactorThree, hfactorTwo]
    omega
  all_goals omega

lemma ambient_lt_b_add_eighteen_of_sub_ten_mem {n : Nat} {gamma : List Nat} {b : Nat}
    (hgamma : IsTheta n gamma) (hbEnd : EndsWith (oddTrace gamma) b)
    (hbLower : b ∈ lowerHalf n) (hbOdd : Odd b)
    (hbTen : 10 * dyadicQ n < b)
    (hx : b - 10 * dyadicQ n ∈ epilogue n (oddTrace gamma)) :
    n < b + 18 * dyadicQ n := by
  let q := dyadicQ n
  have hqPos : 0 < q := dyadicQ_pos n
  have hxOdd : Odd (b - 10 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B - 5 * q, by omega⟩
  have hyOdd : Odd (b + 18 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 9 * q, by omega⟩
  have hzOdd : Odd (b + 4 * q) := by
    rcases hbOdd with ⟨B, hb⟩
    exact ⟨B + 2 * q, by omega⟩
  have hxHalf : (b - 10 * q + 1) / 2 = (b + 1) / 2 - 5 * q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hzHalf : (b + 4 * q + 1) / 2 = (b + 1) / 2 + 2 * q := by
    rcases hbOdd with ⟨B, hb⟩
    omega
  have hdistX : Nat.dist ((b + 1) / 2) ((b - 10 * q + 1) / 2) = 5 * q := by
    rw [hxHalf]
    unfold Nat.dist
    omega
  have hdistZ : Nat.dist ((b + 1) / 2) ((b + 4 * q + 1) / 2) = 2 * q := by
    rw [hzHalf]
    unfold Nat.dist
    omega
  have hfactorFive : (5 * q).factorization 2 = Nat.log 2 n - 4 := by
    simpa only [q, dyadicQ] using factorization_five_mul_pow_two (Nat.log 2 n - 4)
  have hfactorTwo : (2 * q).factorization 2 = Nat.log 2 n - 4 + 1 := by
    simpa only [q, dyadicQ] using factorization_two_mul_pow_two (Nat.log 2 n - 4)
  apply ambient_lt_of_oddEpilogue_forcing hgamma hbEnd hbLower hbOdd hxOdd hyOdd hzOdd
    (by simpa only [q] using hx) (by omega) (by omega) (by omega)
  · simp only [binaryCongruenceDegree, hdistX, hdistZ, hfactorFive, hfactorTwo]
    omega
  all_goals omega

lemma evenTrace_prefix_three_mod_four_of_twenty_two {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) (hSixteen : 16 * dyadicQ n <= n)
    (hTwentyTwo : 22 * dyadicQ n <= n) :
    PrefixCongruent (evenTrace gamma) 3 (4 * dyadicQ n) := by
  have hlog := log_two_four_le_of_dyadic_threshold hSixteen
  have hhalf : 11 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 4)
    (k := 3) (r := 11) (by nlinarith [dyadicQ_pos n]) hgamma hhalf (by norm_num)
  rw [dyadic_modulus_two_of_log_four hlog] at h
  convert h using 1 <;> omega

lemma evenTrace_prefix_two_mod_eight_of_twenty_eight {n : Nat} {gamma : List Nat}
    (hgamma : IsTheta n gamma) (hSixteen : 16 * dyadicQ n <= n)
    (hTwentyEight : 28 * dyadicQ n <= n) :
    PrefixCongruent (evenTrace gamma) 2 (8 * dyadicQ n) := by
  have hlog := log_two_four_le_of_dyadic_threshold hSixteen
  have hhalf : 14 * dyadicQ n <= n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have h := forcedEvenTracePrefixCongruent (N := n) (j := Nat.log 2 n - 3)
    (k := 2) (r := 7) (by nlinarith [dyadicQ_pos n]) hgamma (by
      rw [dyadic_denominator_two_of_log_four hlog]
      nlinarith) (by norm_num)
  rw [dyadic_modulus_four_of_log_four hlog] at h
  convert h using 1 <;> omega

/-- The boundary-oriented entries and congruence data used by the one-sided
numeric argument in Sharma's Theorem 2.6. -/
structure OneSidedActiveEntries (n : Nat) (gamma : List Nat)
    (b1 b2 b3 b4 c1 c2 c3 : Nat) : Prop where
  hbEnd : EndsWith (oddTrace gamma) b1
  hcStart : StartsWith (evenTrace gamma) c1
  hcommute : Commute n b1 c1
  hb1Lower : b1 ∈ lowerHalf n
  hc1Upper : c1 ∈ upperHalf n
  hb1Get : (oddBoundaryActiveList n gamma)[0]? = some b1
  hb2Get : (oddBoundaryActiveList n gamma)[1]? = some b2
  hb3Get : (oddBoundaryActiveList n gamma)[2]? = some b3
  hb4Get : (oddBoundaryActiveList n gamma)[3]? = some b4
  hc1Get : (evenBoundaryActiveList n gamma)[0]? = some c1
  hc2Get : (evenBoundaryActiveList n gamma)[1]? = some c2
  hc3Get : (evenBoundaryActiveList n gamma)[2]? = some c3
  hc1TraceGet : (evenTrace gamma)[0]? = some c1
  hc2TraceGet : (evenTrace gamma)[1]? = some c2
  hc3TraceGet : (evenTrace gamma)[2]? = some c3
  hb1Mem : b1 ∈ oddBoundaryActiveList n gamma
  hb2Mem : b2 ∈ oddBoundaryActiveList n gamma
  hb3Mem : b3 ∈ oddBoundaryActiveList n gamma
  hb4Mem : b4 ∈ oddBoundaryActiveList n gamma
  hc1Mem : c1 ∈ evenBoundaryActiveList n gamma
  hc2Mem : c2 ∈ evenBoundaryActiveList n gamma
  hc3Mem : c3 ∈ evenBoundaryActiveList n gamma
  hb1Odd : Odd b1
  hb2Odd : Odd b2
  hb3Odd : Odd b3
  hb4Odd : Odd b4
  hc1Even : Even c1
  hc2Even : Even c2
  hc3Even : Even c3
  hb1Segment : b1 ∈ segment n
  hb2Segment : b2 ∈ segment n
  hb3Segment : b3 ∈ segment n
  hb4Segment : b4 ∈ segment n
  hc1Segment : c1 ∈ segment n
  hc2Segment : c2 ∈ segment n
  hc3Segment : c3 ∈ segment n
  hb12 : b1 ≠ b2
  hb13 : b1 ≠ b3
  hb14 : b1 ≠ b4
  hb23 : b2 ≠ b3
  hb24 : b2 ≠ b4
  hb34 : b3 ≠ b4
  hc12 : c1 ≠ c2
  hc13 : c1 ≠ c3
  hc23 : c2 ≠ c3
  hb2Le : b2 ≤ b1
  hb3Le : b3 ≤ b1
  hb4Le : b4 ≤ b1
  hc2Ge : c1 ≤ c2
  hc3Ge : c1 ≤ c3
  hseparated : 2 * b1 ≤ c1
  hreflectionAbove : n < 2 * c1 - b1
  hqPos : 0 < dyadicQ n
  hthreshold : 16 * dyadicQ n ≤ n
  hb2ModFour : Nat.ModEq (4 * dyadicQ n) b2 b1
  hb2ModTwo : Nat.ModEq (2 * dyadicQ n) b2 b1
  hb3ModTwo : Nat.ModEq (2 * dyadicQ n) b3 b1
  hb4ModTwo : Nat.ModEq (2 * dyadicQ n) b4 b1
  hc2ModFour : Nat.ModEq (4 * dyadicQ n) c1 c2
  hc2ModTwo : Nat.ModEq (2 * dyadicQ n) c1 c2
  hc3ModTwo : Nat.ModEq (2 * dyadicQ n) c1 c3

/-- Extract the first four boundary-oriented odd entries and first three even
entries from the long-active-list branch. -/
theorem oneSidedActiveEntries_of_lengths {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hu : 4 ≤ (epilogue n (oddTrace gamma)).length)
    (hv : 3 ≤ (prologue n (evenTrace gamma)).length) :
    ∃ b1 b2 b3 b4 c1 c2 c3,
      OneSidedActiveEntries n gamma b1 b2 b3 b4 c1 c2 c3 := by
  let oddList := oddBoundaryActiveList n gamma
  let evenList := evenBoundaryActiveList n gamma
  have hoddLength : 4 ≤ oddList.length := by
    simpa only [oddList, oddBoundaryActiveList_length] using hu
  have hevenLength : 3 ≤ evenList.length := by
    simpa only [evenList, evenBoundaryActiveList_length] using hv
  rcases hstanding.2 with
    ⟨b1, c1, hbEnd, hcStart, hcommute, hb1Lower, hc1Upper⟩
  have hbStart : StartsWith oddList b1 := by
    simp only [oddList, oddBoundaryActiveList, epilogue]
    exact startsWith_prologue_of_startsWith
      (startsWith_reversal_of_endsWith hbEnd)
  have hcBoundaryStart : StartsWith evenList c1 := by
    simp only [evenList, evenBoundaryActiveList]
    exact startsWith_prologue_of_startsWith hcStart
  have hb1Get : oddList[0]? = some b1 := by
    rw [← List.head?_eq_getElem?]
    exact hbStart
  have hc1Get : evenList[0]? = some c1 := by
    rw [← List.head?_eq_getElem?]
    exact hcBoundaryStart
  let b2 := oddList[1]'(by omega)
  let b3 := oddList[2]'(by omega)
  let b4 := oddList[3]'(by omega)
  let c2 := evenList[1]'(by omega)
  let c3 := evenList[2]'(by omega)
  have hb2Get : oddList[1]? = some b2 := by
    simpa only [b2] using List.getElem?_eq_getElem (l := oddList) (i := 1) (by omega)
  have hb3Get : oddList[2]? = some b3 := by
    simpa only [b3] using List.getElem?_eq_getElem (l := oddList) (i := 2) (by omega)
  have hb4Get : oddList[3]? = some b4 := by
    simpa only [b4] using List.getElem?_eq_getElem (l := oddList) (i := 3) (by omega)
  have hc2Get : evenList[1]? = some c2 := by
    simpa only [c2] using List.getElem?_eq_getElem (l := evenList) (i := 1) (by omega)
  have hc3Get : evenList[2]? = some c3 := by
    simpa only [c3] using List.getElem?_eq_getElem (l := evenList) (i := 2) (by omega)
  have hb1Mem : b1 ∈ oddList := List.mem_iff_getElem?.mpr ⟨0, hb1Get⟩
  have hb2Mem : b2 ∈ oddList := List.mem_iff_getElem?.mpr ⟨1, hb2Get⟩
  have hb3Mem : b3 ∈ oddList := List.mem_iff_getElem?.mpr ⟨2, hb3Get⟩
  have hb4Mem : b4 ∈ oddList := List.mem_iff_getElem?.mpr ⟨3, hb4Get⟩
  have hc1Mem : c1 ∈ evenList := List.mem_iff_getElem?.mpr ⟨0, hc1Get⟩
  have hc2Mem : c2 ∈ evenList := List.mem_iff_getElem?.mpr ⟨1, hc2Get⟩
  have hc3Mem : c3 ∈ evenList := List.mem_iff_getElem?.mpr ⟨2, hc3Get⟩
  have hoddNodup : oddList.Nodup := by
    simpa only [oddList] using oddBoundaryActiveList_nodup hstanding.1.1
  have hevenNodup : evenList.Nodup := by
    simpa only [evenList] using evenBoundaryActiveList_nodup hstanding.1.1
  have hb12 : b1 ≠ b2 :=
    values_ne_of_getElem?_ne_index hoddNodup hb1Get hb2Get (by norm_num)
  have hb13 : b1 ≠ b3 :=
    values_ne_of_getElem?_ne_index hoddNodup hb1Get hb3Get (by norm_num)
  have hb14 : b1 ≠ b4 :=
    values_ne_of_getElem?_ne_index hoddNodup hb1Get hb4Get (by norm_num)
  have hb23 : b2 ≠ b3 :=
    values_ne_of_getElem?_ne_index hoddNodup hb2Get hb3Get (by norm_num)
  have hb24 : b2 ≠ b4 :=
    values_ne_of_getElem?_ne_index hoddNodup hb2Get hb4Get (by norm_num)
  have hb34 : b3 ≠ b4 :=
    values_ne_of_getElem?_ne_index hoddNodup hb3Get hb4Get (by norm_num)
  have hc12 : c1 ≠ c2 :=
    values_ne_of_getElem?_ne_index hevenNodup hc1Get hc2Get (by norm_num)
  have hc13 : c1 ≠ c3 :=
    values_ne_of_getElem?_ne_index hevenNodup hc1Get hc3Get (by norm_num)
  have hc23 : c2 ≠ c3 :=
    values_ne_of_getElem?_ne_index hevenNodup hc2Get hc3Get (by norm_num)
  have hb1Odd : Odd b1 := oddBoundaryActiveList_odd (by simpa only [oddList] using hb1Mem)
  have hb2Odd : Odd b2 := oddBoundaryActiveList_odd (by simpa only [oddList] using hb2Mem)
  have hb3Odd : Odd b3 := oddBoundaryActiveList_odd (by simpa only [oddList] using hb3Mem)
  have hb4Odd : Odd b4 := oddBoundaryActiveList_odd (by simpa only [oddList] using hb4Mem)
  have hc1Even : Even c1 := evenBoundaryActiveList_even (by simpa only [evenList] using hc1Mem)
  have hc2Even : Even c2 := evenBoundaryActiveList_even (by simpa only [evenList] using hc2Mem)
  have hc3Even : Even c3 := evenBoundaryActiveList_even (by simpa only [evenList] using hc3Mem)
  have hoddGamma : ∀ x ∈ oddList, x ∈ gamma := by
    intro x hx
    have hxActive := oddBoundaryActiveList_mem_oddActiveBlock
      (by simpa only [oddList] using hx)
    exact (List.mem_filter.mp (oddActiveBlock_mem_oddTrace hxActive)).1
  have hevenGamma : ∀ x ∈ evenList, x ∈ gamma := by
    intro x hx
    have hxActive := evenBoundaryActiveList_mem_evenActiveBlock
      (by simpa only [evenList] using hx)
    exact (List.mem_filter.mp (evenActiveBlock_mem_evenTrace hxActive)).1
  have hb1Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hoddGamma b1 hb1Mem)
  have hb2Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hoddGamma b2 hb2Mem)
  have hb3Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hoddGamma b3 hb3Mem)
  have hb4Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hoddGamma b4 hb4Mem)
  have hc1Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hevenGamma c1 hc1Mem)
  have hc2Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hevenGamma c2 hc2Mem)
  have hc3Segment := mem_segment_of_mem_of_isTheta hstanding.1.1 (hevenGamma c3 hc3Mem)
  have hb2Le := oddEpilogue_entry_le_last hstanding.1.1 hbEnd hb1Lower (by
    simpa only [oddList, oddBoundaryActiveList] using hb2Mem)
  have hb3Le := oddEpilogue_entry_le_last hstanding.1.1 hbEnd hb1Lower (by
    simpa only [oddList, oddBoundaryActiveList] using hb3Mem)
  have hb4Le := oddEpilogue_entry_le_last hstanding.1.1 hbEnd hb1Lower (by
    simpa only [oddList, oddBoundaryActiveList] using hb4Mem)
  have hc2Ge := evenPrologue_first_le_entry hstanding.1.1 hcStart hc1Upper (by
    simpa only [evenList, evenBoundaryActiveList] using hc2Mem)
  have hc3Ge := evenPrologue_first_le_entry hstanding.1.1 hcStart hc1Upper (by
    simpa only [evenList, evenBoundaryActiveList] using hc3Mem)
  have hseparation := activeBlocks_separated hstanding b1
    (oddBoundaryActiveList_mem_oddActiveBlock (by simpa only [oddList] using hb1Mem)) c1
    (evenBoundaryActiveList_mem_evenActiveBlock (by simpa only [evenList] using hc1Mem))
  have hthreshold := sixteen_mul_dyadicQ_le
    (sixteen_le_of_active_lengths hstanding hu hv)
  have hpatterns := dyadic_pattern_sixteen hstanding.1.1 hthreshold
  have hreversePatterns :=
    dyadic_pattern_sixteen (isTheta_reversal hstanding.1.1) hthreshold
  have hoddFourTrace :
      PrefixCongruent (reversal (oddTrace gamma)) 2 (4 * dyadicQ n) := by
    simpa only [oddTrace_reversal_eq] using hreversePatterns.2.1.1
  have hoddTwoTrace :
      PrefixCongruent (reversal (oddTrace gamma)) 4 (2 * dyadicQ n) := by
    simpa only [oddTrace_reversal_eq] using hreversePatterns.2.1.2.1
  have hoddFour : PrefixCongruent oddList 2 (4 * dyadicQ n) := by
    simpa only [oddList] using
      oddBoundaryActiveList_prefixCongruent_of_reversal (by omega) hoddFourTrace
  have hoddTwo : PrefixCongruent oddList 4 (2 * dyadicQ n) := by
    simpa only [oddList] using
      oddBoundaryActiveList_prefixCongruent_of_reversal hu hoddTwoTrace
  have hevenFour : PrefixCongruent evenList 2 (4 * dyadicQ n) := by
    simpa only [evenList] using
      evenBoundaryActiveList_prefixCongruent_of_evenTrace (by omega) hpatterns.2.2.1
  have hevenTwo : PrefixCongruent evenList 3 (2 * dyadicQ n) := by
    have htrace : PrefixCongruent (evenTrace gamma) 3 (2 * dyadicQ n) :=
      PrefixCongruent.mono hpatterns.2.2.2.1 (by norm_num)
    simpa only [evenList] using
      evenBoundaryActiveList_prefixCongruent_of_evenTrace hv htrace
  have hEvenPrefix : evenList <+: evenTrace gamma := by
    simpa only [evenList, evenBoundaryActiveList] using prologue_prefix n (evenTrace gamma)
  have hgetEvenTrace : ∀ (i x : Nat), i < evenList.length →
      evenList[i]? = some x → (evenTrace gamma)[i]? = some x := by
    intro i x hi hx
    have hiTrace : i < (evenTrace gamma).length :=
      hi.trans_le hEvenPrefix.length_le
    calc
      (evenTrace gamma)[i]? = some (evenTrace gamma)[i] :=
        List.getElem?_eq_getElem hiTrace
      _ = some evenList[i] := congrArg some (hEvenPrefix.getElem hi).symm
      _ = some x := by simpa only [List.getElem?_eq_getElem hi] using hx
  have hc1TraceGet : (evenTrace gamma)[0]? = some c1 :=
    hgetEvenTrace 0 c1 (by omega) hc1Get
  have hc2TraceGet : (evenTrace gamma)[1]? = some c2 :=
    hgetEvenTrace 1 c2 (by omega) hc2Get
  have hc3TraceGet : (evenTrace gamma)[2]? = some c3 :=
    hgetEvenTrace 2 c3 (by omega) hc3Get
  refine ⟨b1, b2, b3, b4, c1, c2, c3, ?_⟩
  refine
    { hbEnd := hbEnd
      hcStart := hcStart
      hcommute := hcommute
      hb1Lower := hb1Lower
      hc1Upper := hc1Upper
      hb1Get := by simpa only [oddList] using hb1Get
      hb2Get := by simpa only [oddList] using hb2Get
      hb3Get := by simpa only [oddList] using hb3Get
      hb4Get := by simpa only [oddList] using hb4Get
      hc1Get := by simpa only [evenList] using hc1Get
      hc2Get := by simpa only [evenList] using hc2Get
      hc3Get := by simpa only [evenList] using hc3Get
      hc1TraceGet := hc1TraceGet
      hc2TraceGet := hc2TraceGet
      hc3TraceGet := hc3TraceGet
      hb1Mem := by simpa only [oddList] using hb1Mem
      hb2Mem := by simpa only [oddList] using hb2Mem
      hb3Mem := by simpa only [oddList] using hb3Mem
      hb4Mem := by simpa only [oddList] using hb4Mem
      hc1Mem := by simpa only [evenList] using hc1Mem
      hc2Mem := by simpa only [evenList] using hc2Mem
      hc3Mem := by simpa only [evenList] using hc3Mem
      hb1Odd := hb1Odd
      hb2Odd := hb2Odd
      hb3Odd := hb3Odd
      hb4Odd := hb4Odd
      hc1Even := hc1Even
      hc2Even := hc2Even
      hc3Even := hc3Even
      hb1Segment := hb1Segment
      hb2Segment := hb2Segment
      hb3Segment := hb3Segment
      hb4Segment := hb4Segment
      hc1Segment := hc1Segment
      hc2Segment := hc2Segment
      hc3Segment := hc3Segment
      hb12 := hb12
      hb13 := hb13
      hb14 := hb14
      hb23 := hb23
      hb24 := hb24
      hb34 := hb34
      hc12 := hc12
      hc13 := hc13
      hc23 := hc23
      hb2Le := hb2Le
      hb3Le := hb3Le
      hb4Le := hb4Le
      hc2Ge := hc2Ge
      hc3Ge := hc3Ge
      hseparated := hseparation.1
      hreflectionAbove := hseparation.2
      hqPos := dyadicQ_pos n
      hthreshold := hthreshold
      hb2ModFour := (hoddFour.2 0 (by norm_num) 1 (by norm_num)
        b1 b2 hb1Get hb2Get).symm
      hb2ModTwo := (hoddTwo.2 0 (by norm_num) 1 (by norm_num)
        b1 b2 hb1Get hb2Get).symm
      hb3ModTwo := (hoddTwo.2 0 (by norm_num) 2 (by norm_num)
        b1 b3 hb1Get hb3Get).symm
      hb4ModTwo := (hoddTwo.2 0 (by norm_num) 3 (by norm_num)
        b1 b4 hb1Get hb4Get).symm
      hc2ModFour := hevenFour.2 0 (by norm_num) 1 (by norm_num)
        c1 c2 hc1Get hc2Get
      hc2ModTwo := hevenTwo.2 0 (by norm_num) 1 (by norm_num)
        c1 c2 hc1Get hc2Get
      hc3ModTwo := hevenTwo.2 0 (by norm_num) 2 (by norm_num)
        c1 c3 hc1Get hc3Get }


lemma two_distinct_modEq_successors_force_double_gap {m a x y N : Nat}
    (hax : a <= x) (hay : a <= y)
    (haxNe : a ≠ x) (hayNe : a ≠ y) (hxy : x ≠ y)
    (hmodX : Nat.ModEq m a x) (hmodY : Nat.ModEq m a y)
    (hxN : x <= N) (hyN : y <= N) :
    a + 2 * m <= N := by
  obtain ⟨dx, hdx⟩ := (Nat.modEq_iff_exists_eq_add hax).mp hmodX
  obtain ⟨dy, hdy⟩ := (Nat.modEq_iff_exists_eq_add hay).mp hmodY
  have hdxPos : 0 < dx := by
    by_contra h
    have : dx = 0 := by omega
    subst dx
    simp only [Nat.mul_zero, Nat.add_zero] at hdx
    exact haxNe hdx.symm
  have hdyPos : 0 < dy := by
    by_contra h
    have : dy = 0 := by omega
    subst dy
    simp only [Nat.mul_zero, Nat.add_zero] at hdy
    exact hayNe hdy.symm
  have hdxdy : dx ≠ dy := by
    intro h
    subst dy
    exact hxy (by nlinarith)
  have hlarge : 2 <= dx ∨ 2 <= dy := by omega
  rcases hlarge with hlarge | hlarge <;> nlinarith

lemma middle_case_successor_values {q b c1 c2 c3 n : Nat}
    (hq : 0 < q) (hbEight : 8 * q < b)
    (hcLower : 2 * b <= c1) (hnUpper : n < b + 14 * q)
    (hc1Two : c1 <= c2) (hc1Three : c1 <= c3)
    (hc12 : c1 ≠ c2) (hc13 : c1 ≠ c3) (hc23 : c2 ≠ c3)
    (hc2N : c2 <= n) (hc3N : c3 <= n)
    (hmod2 : Nat.ModEq (4 * q) c1 c2)
    (hmod3 : Nat.ModEq (2 * q) c1 c3) :
    c2 = c1 + 4 * q ∧ c3 = c1 + 2 * q := by
  obtain ⟨d2, hd2⟩ := (Nat.modEq_iff_exists_eq_add hc1Two).mp hmod2
  obtain ⟨d3, hd3⟩ := (Nat.modEq_iff_exists_eq_add hc1Three).mp hmod3
  have hd2Pos : 0 < d2 := by
    by_contra h
    have : d2 = 0 := by omega
    subst d2
    simp only [Nat.mul_zero, Nat.add_zero] at hd2
    exact hc12 hd2.symm
  have hd3Pos : 0 < d3 := by
    by_contra h
    have : d3 = 0 := by omega
    subst d3
    simp only [Nat.mul_zero, Nat.add_zero] at hd3
    exact hc13 hd3.symm
  have hd2One : d2 = 1 := by nlinarith
  have hd3Le : d3 <= 2 := by nlinarith
  have hc2Eq : c2 = c1 + 4 * q := by
    subst d2
    nlinarith
  have hd3NeTwo : d3 ≠ 2 := by
    intro h
    subst d3
    apply hc23
    nlinarith
  have hd3One : d3 = 1 := by omega
  constructor
  · exact hc2Eq
  · subst d3
    nlinarith

/-- The numeric three-case core of the first implication in Theorem 2.6,
given the seven boundary entries. -/
lemma oddEpilogue_four_evenPrologue_three_impossible_of_entries
    {n : Nat} {gamma : List Nat} {b1 b2 b3 b4 c1 c2 c3 : Nat}
    (hgamma : IsTheta n gamma)
    (hdata : OneSidedActiveEntries n gamma b1 b2 b3 b4 c1 c2 c3) : False := by
  let q := dyadicQ n
  have hbEnd := hdata.hbEnd
  have hcStart := hdata.hcStart
  have hbLower := hdata.hb1Lower
  have hb1At := hdata.hb1Get
  have hb2At := hdata.hb2Get
  have hb3At := hdata.hb3Get
  have hb4At := hdata.hb4Get
  have hc1At := hdata.hc1Get
  have hc2At := hdata.hc2Get
  have hc3At := hdata.hc3Get
  have hv : 3 <= (prologue n (evenTrace gamma)).length := by
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hc3At
    have hbound' : 2 < (prologue n (evenTrace gamma)).length := by
      simpa only [evenBoundaryActiveList] using hbound
    omega
  have hb1Mem := hdata.hb1Mem
  have hb2Mem := hdata.hb2Mem
  have hb3Mem := hdata.hb3Mem
  have hb4Mem := hdata.hb4Mem
  have hqPos : 0 < q := by simpa only [q] using hdata.hqPos
  have hb12 := hdata.hb12
  have hb13 := hdata.hb13
  have hb14 := hdata.hb14
  have hb23 := hdata.hb23
  have hb24 := hdata.hb24
  have hb34 := hdata.hb34
  have hc12 := hdata.hc12
  have hc13 := hdata.hc13
  have hc23 := hdata.hc23
  have hb1Odd := hdata.hb1Odd
  have hc1Even := hdata.hc1Even
  have hb1Half := hdata.hb1Lower
  have hb2Pos : 0 < b2 := by
    have h := hdata.hb2Segment
    simp only [segment, Finset.mem_Icc] at h
    omega
  have hb3Pos : 0 < b3 := by
    have h := hdata.hb3Segment
    simp only [segment, Finset.mem_Icc] at h
    omega
  have hb4Pos : 0 < b4 := by
    have h := hdata.hb4Segment
    simp only [segment, Finset.mem_Icc] at h
    omega
  have hc2N : c2 <= n := by
    have h := hdata.hc2Segment
    simp only [segment, Finset.mem_Icc] at h
    omega
  have hc3N : c3 <= n := by
    have h := hdata.hc3Segment
    simp only [segment, Finset.mem_Icc] at h
    omega
  have hb2Le := hdata.hb2Le
  have hb3Le := hdata.hb3Le
  have hb4Le := hdata.hb4Le
  have hc1Le2 := hdata.hc2Ge
  have hc1Le3 := hdata.hc3Ge
  have hbc := hdata.hseparated
  have hSixteen : 16 * q <= n := by simpa only [q] using hdata.hthreshold
  have hnSixteen : 16 <= n := by nlinarith
  have hnThirtyTwo : n < 32 * q := by
    simpa only [q] using thirty_two_dyadicQ_gt hnSixteen
  have hb2Mod : Nat.ModEq (2 * q) b2 b1 := by simpa only [q] using hdata.hb2ModTwo
  have hb3Mod : Nat.ModEq (2 * q) b3 b1 := by simpa only [q] using hdata.hb3ModTwo
  have hb4Mod : Nat.ModEq (2 * q) b4 b1 := by simpa only [q] using hdata.hb4ModTwo
  have hc2ModFour : Nat.ModEq (4 * q) c1 c2 := by
    simpa only [q] using hdata.hc2ModFour
  have hc3ModTwo : Nat.ModEq (2 * q) c1 c3 := by
    simpa only [q] using hdata.hc3ModTwo
  have hbSix : 6 * q < b1 := six_mul_lt_of_three_distinct_predecessors
    hb2Pos hb3Pos hb4Pos hb2Le hb3Le hb4Le hb12.symm hb13.symm hb14.symm
    hb23 hb24 hb34 hb2Mod hb3Mod hb4Mod
  by_cases hbEight : b1 < 8 * q
  · have hwhich := first_predecessor_among_three hbEight hb2Pos hb3Pos hb4Pos
      hb2Le hb3Le hb4Le hb12.symm hb13.symm hb14.symm hb23 hb24 hb34
      hb2Mod hb3Mod hb4Mod
    have hsubTwoMem : b1 - 2 * q ∈ epilogue n (oddTrace gamma) := by
      rcases hwhich with h | h | h
      · simpa only [oddBoundaryActiveList, h] using hb2Mem
      · simpa only [oddBoundaryActiveList, h] using hb3Mem
      · simpa only [oddBoundaryActiveList, h] using hb4Mem
    have hnUpper := ambient_lt_b_add_ten_of_sub_two_mem hgamma hbEnd hbLower hb1Odd
      (by omega) (by simpa only [q] using hsubTwoMem)
    have hc1Lt2 : c1 < c2 := lt_of_le_of_ne hc1Le2 hc12
    have hc2Gap := add_modulus_le_of_modEq_of_lt (by omega : 0 < 4 * q)
      hc2ModFour hc1Lt2
    omega
  · have hbEightStrict : 8 * q < b1 := by
      rcases hb1Odd with ⟨B, hb⟩
      omega
    by_cases hbTen : b1 < 10 * q
    · have hbSixteen : b1 < 16 * q := by
        simp only [lowerHalf, Finset.mem_Icc] at hb1Half
        omega
      have hnotPred := dyadic_predecessor_not_mem_oddEpilogue hgamma hbEnd hbLower
        hb1Odd hbEightStrict (by simpa only [q] using hbSixteen)
      have hb2Not : b2 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb2Mem
      have hb3Not : b3 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb3Mem
      have hb4Not : b4 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb4Mem
      have hwhich := third_predecessor_among_three_without_first hbTen
        hb2Pos hb3Pos hb4Pos hb2Le hb3Le hb4Le hb12.symm hb13.symm hb14.symm
        hb23 hb24 hb34 hb2Mod hb3Mod hb4Mod hb2Not hb3Not hb4Not
      have hsubSixMem : b1 - 6 * q ∈ epilogue n (oddTrace gamma) := by
        rcases hwhich with h | h | h
        · simpa only [oddBoundaryActiveList, h] using hb2Mem
        · simpa only [oddBoundaryActiveList, h] using hb3Mem
        · simpa only [oddBoundaryActiveList, h] using hb4Mem
      have hnUpper := ambient_lt_b_add_fourteen_of_sub_six_mem hgamma hbEnd hbLower
        hb1Odd (by simpa only [q] using hbSix) (by simpa only [q] using hsubSixMem)
      have hvalues := middle_case_successor_values hqPos hbEightStrict hbc
        (by simpa only [q] using hnUpper) hc1Le2 hc1Le3 hc12 hc13 hc23 hc2N hc3N
        hc2ModFour hc3ModTwo
      have hc1Trace := hdata.hc1TraceGet
      have hc2Trace := hdata.hc2TraceGet
      have hc3Trace := hdata.hc3TraceGet
      exact evenTrace_middle_case_impossible hgamma rfl hcStart hc1Trace hc2Trace hc3Trace
        hc1Even hvalues.1 hvalues.2 (by omega)
    · have hbTenStrict : 10 * q < b1 := by
        rcases hb1Odd with ⟨B, hb⟩
        omega
      have hc1Lt2 : c1 < c2 := lt_of_le_of_ne hc1Le2 hc12
      have hc2GapFour := add_modulus_le_of_modEq_of_lt (by omega : 0 < 4 * q)
        hc2ModFour hc1Lt2
      have hTwentyTwo : 22 * q <= n := by omega
      have hTraceThreeFour := evenTrace_prefix_three_mod_four_of_twenty_two hgamma
        (by simpa only [q] using hSixteen) (by simpa only [q] using hTwentyTwo)
      have hCThreeFour := evenBoundaryActiveList_prefixCongruent_of_evenTrace
        (n := n) (gamma := gamma) (k := 3) (m := 4 * q)
        (by omega) (by simpa only [q] using hTraceThreeFour)
      have hc3ModFour : Nat.ModEq (4 * q) c1 c3 :=
        hCThreeFour.2 0 (by omega) 2 (by omega) c1 c3 hc1At hc3At
      have hcDoubleGap := two_distinct_modEq_successors_force_double_gap
        hc1Le2 hc1Le3 hc12 hc13 hc23 hc2ModFour hc3ModFour hc2N hc3N
      have hTwentyEight : 28 * q <= n := by omega
      have hTraceTwoEight := evenTrace_prefix_two_mod_eight_of_twenty_eight hgamma
        (by simpa only [q] using hSixteen) (by simpa only [q] using hTwentyEight)
      have hCTwoEight := evenBoundaryActiveList_prefixCongruent_of_evenTrace
        (n := n) (gamma := gamma) (k := 2) (m := 8 * q)
        (by omega) (by simpa only [q] using hTraceTwoEight)
      have hc2ModEight : Nat.ModEq (8 * q) c1 c2 :=
        hCTwoEight.2 0 (by omega) 1 (by omega) c1 c2 hc1At hc2At
      have hc2GapEight := add_modulus_le_of_modEq_of_lt (by omega : 0 < 8 * q)
        hc2ModEight hc1Lt2
      have hbTwelve : b1 < 12 * q := by omega
      have hbSixteen : b1 < 16 * q := by omega
      have hnotPred := dyadic_predecessor_not_mem_oddEpilogue hgamma hbEnd hbLower
        hb1Odd hbEightStrict (by simpa only [q] using hbSixteen)
      have hb2Not : b2 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb2Mem
      have hb3Not : b3 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb3Mem
      have hb4Not : b4 ≠ b1 - 2 * q := by
        intro h
        apply hnotPred
        simpa only [oddBoundaryActiveList, q, h] using hb4Mem
      have hwhich := third_or_fifth_predecessor_among_three_without_first hbTwelve
        hb2Pos hb3Pos hb4Pos hb2Le hb3Le hb4Le hb12.symm hb13.symm hb14.symm
        hb23 hb24 hb34 hb2Mod hb3Mod hb4Mod hb2Not hb3Not hb4Not
      rcases hwhich with hsubSix | hsubTen
      · have hsubSixMem : b1 - 6 * q ∈ epilogue n (oddTrace gamma) := by
          rcases hsubSix with h | h | h
          · simpa only [oddBoundaryActiveList, h] using hb2Mem
          · simpa only [oddBoundaryActiveList, h] using hb3Mem
          · simpa only [oddBoundaryActiveList, h] using hb4Mem
        have hnUpper := ambient_lt_b_add_fourteen_of_sub_six_mem hgamma hbEnd hbLower
          hb1Odd (by simpa only [q] using hbSix) (by simpa only [q] using hsubSixMem)
        omega
      · have hsubTenMem : b1 - 10 * q ∈ epilogue n (oddTrace gamma) := by
          rcases hsubTen with h | h | h
          · simpa only [oddBoundaryActiveList, h] using hb2Mem
          · simpa only [oddBoundaryActiveList, h] using hb3Mem
          · simpa only [oddBoundaryActiveList, h] using hb4Mem
        have hnUpper := ambient_lt_b_add_eighteen_of_sub_ten_mem hgamma hbEnd hbLower
          hb1Odd (by simpa only [q] using hbTenStrict)
          (by simpa only [q] using hsubTenMem)
        omega

/-- The first implication of Theorem 2.6: four active odd entries force the
active even prefix to have length at most two. -/
theorem theorem_2_6_left {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hu : 4 <= (epilogue n (oddTrace gamma)).length) :
    (prologue n (evenTrace gamma)).length <= 2 := by
  by_contra hv
  have hvThree : 3 <= (prologue n (evenTrace gamma)).length := by omega
  rcases oneSidedActiveEntries_of_lengths hstanding hu hvThree with
    ⟨b1, b2, b3, b4, c1, c2, c3, hdata⟩
  exact oddEpilogue_four_evenPrologue_three_impossible_of_entries hstanding.1.1 hdata

lemma sub_two_mul_mem_of_four_prefix {word : List Nat} {first q : Nat}
    (_hq : 0 < q) (hlength : 4 <= word.length) (hnodup : word.Nodup)
    (hstart : StartsWith word first)
    (hpositive : forall x, x ∈ word -> 0 < x)
    (hmax : forall x, x ∈ word -> x <= first)
    (hcongruent : PrefixCongruent word 4 (2 * q))
    (hupper : first < 8 * q) :
    6 * q < first /\ first - 2 * q ∈ word := by
  let x1 := word[1]'(by omega)
  let x2 := word[2]'(by omega)
  let x3 := word[3]'(by omega)
  have hzero : word[0]? = some first := by
    rw [← List.head?_eq_getElem?]
    exact hstart
  have hone : word[1]? = some x1 := by
    simpa only [x1] using (List.getElem?_eq_getElem (l := word) (i := 1) (by omega))
  have htwo : word[2]? = some x2 := by
    simpa only [x2] using (List.getElem?_eq_getElem (l := word) (i := 2) (by omega))
  have hthree : word[3]? = some x3 := by
    simpa only [x3] using (List.getElem?_eq_getElem (l := word) (i := 3) (by omega))
  have hx1Mem : x1 ∈ word := List.getElem_mem _
  have hx2Mem : x2 ∈ word := List.getElem_mem _
  have hx3Mem : x3 ∈ word := List.getElem_mem _
  have hx1Le := hmax x1 hx1Mem
  have hx2Le := hmax x2 hx2Mem
  have hx3Le := hmax x3 hx3Mem
  have hx1Pos := hpositive x1 hx1Mem
  have hx2Pos := hpositive x2 hx2Mem
  have hx3Pos := hpositive x3 hx3Mem
  have hmod1 : Nat.ModEq (2 * q) x1 first :=
    hcongruent.2 1 (by omega) 0 (by omega) x1 first hone hzero
  have hmod2 : Nat.ModEq (2 * q) x2 first :=
    hcongruent.2 2 (by omega) 0 (by omega) x2 first htwo hzero
  have hmod3 : Nat.ModEq (2 * q) x3 first :=
    hcongruent.2 3 (by omega) 0 (by omega) x3 first hthree hzero
  obtain ⟨d1, hd1⟩ := (Nat.modEq_iff_exists_eq_add hx1Le).mp hmod1
  obtain ⟨d2, hd2⟩ := (Nat.modEq_iff_exists_eq_add hx2Le).mp hmod2
  obtain ⟨d3, hd3⟩ := (Nat.modEq_iff_exists_eq_add hx3Le).mp hmod3
  have hd1Le : d1 <= 3 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 4 <= d1 by omega)
    omega
  have hd2Le : d2 <= 3 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 4 <= d2 by omega)
    omega
  have hd3Le : d3 <= 3 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 4 <= d3 by omega)
    omega
  have h01 : first ≠ x1 := by
    intro h
    have hone' : word[1]? = some first := by simpa only [← h] using hone
    have := getElem?_index_unique_of_nodup hnodup hzero hone'
    omega
  have h02 : first ≠ x2 := by
    intro h
    have htwo' : word[2]? = some first := by simpa only [← h] using htwo
    have := getElem?_index_unique_of_nodup hnodup hzero htwo'
    omega
  have h03 : first ≠ x3 := by
    intro h
    have hthree' : word[3]? = some first := by simpa only [← h] using hthree
    have := getElem?_index_unique_of_nodup hnodup hzero hthree'
    omega
  have h12 : x1 ≠ x2 := by
    exact mt hnodup.getElem_inj_iff.mp (by norm_num)
  have h13 : x1 ≠ x3 := by
    exact mt hnodup.getElem_inj_iff.mp (by norm_num)
  have h23 : x2 ≠ x3 := by
    exact mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hd1Pos : 0 < d1 := by
    by_contra h
    have hd : d1 = 0 := by omega
    subst d1
    simp only [mul_zero, add_zero] at hd1
    omega
  have hd2Pos : 0 < d2 := by
    by_contra h
    have hd : d2 = 0 := by omega
    subst d2
    simp only [mul_zero, add_zero] at hd2
    omega
  have hd3Pos : 0 < d3 := by
    by_contra h
    have hd : d3 = 0 := by omega
    subst d3
    simp only [mul_zero, add_zero] at hd3
    omega
  have hd12 : d1 ≠ d2 := by
    intro h
    subst d2
    omega
  have hd13 : d1 ≠ d3 := by
    intro h
    subst d3
    omega
  have hd23 : d2 ≠ d3 := by
    intro h
    subst d3
    omega
  have honeCoeff : d1 = 1 \/ d2 = 1 \/ d3 = 1 := by omega
  have hthreeCoeff : d1 = 3 \/ d2 = 3 \/ d3 = 3 := by omega
  have hlower : 6 * q < first := by
    rcases hthreeCoeff with h | h | h
    · subst d1
      simp only [mul_comm (2 * q) 3] at hd1
      omega
    · subst d2
      simp only [mul_comm (2 * q) 3] at hd2
      omega
    · subst d3
      simp only [mul_comm (2 * q) 3] at hd3
      omega
  have htarget : x1 = first - 2 * q \/ x2 = first - 2 * q \/
      x3 = first - 2 * q := by
    rcases honeCoeff with h | h | h
    · left
      subst d1
      simp only [mul_one] at hd1
      omega
    · right; left
      subst d2
      simp only [mul_one] at hd2
      omega
    · right; right
      subst d3
      simp only [mul_one] at hd3
      omega
  rcases htarget with h | h | h
  · exact ⟨hlower, h ▸ hx1Mem⟩
  · exact ⟨hlower, h ▸ hx2Mem⟩
  · exact ⟨hlower, h ▸ hx3Mem⟩

/-- The `5+2` active-block hypothesis of Theorem 2.7 is already large
enough to enter the first dyadic range. -/
lemma sixteen_le_of_five_two_active_lengths {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hu : 5 <= (epilogue n (oddTrace gamma)).length)
    (hv : 2 <= (prologue n (evenTrace gamma)).length) : 16 <= n := by
  let xs := oddActiveBlock n (oddTrace gamma)
  let ys := evenActiveBlock n (evenTrace gamma)
  have hxsLength : 5 <= xs.length := by
    simpa only [xs, oddActiveBlock_length] using hu
  have hysLength : 2 <= ys.length := by
    simpa only [ys, evenActiveBlock_length] using hv
  let x0 := xs[0]'(by omega)
  let x1 := xs[1]'(by omega)
  let x2 := xs[2]'(by omega)
  let x3 := xs[3]'(by omega)
  let x4 := xs[4]'(by omega)
  let y0 := ys[0]'(by omega)
  have hx0 : x0 ∈ xs := List.getElem_mem _
  have hx1 : x1 ∈ xs := List.getElem_mem _
  have hx2 : x2 ∈ xs := List.getElem_mem _
  have hx3 : x3 ∈ xs := List.getElem_mem _
  have hx4 : x4 ∈ xs := List.getElem_mem _
  have hy0 : y0 ∈ ys := List.getElem_mem _
  have hxsNodup : xs.Nodup := by
    simpa only [xs] using oddActiveBlock_nodup hstanding.1.1
  have hx01 : x0 ≠ x1 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx02 : x0 ≠ x2 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx03 : x0 ≠ x3 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx04 : x0 ≠ x4 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx12 : x1 ≠ x2 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx13 : x1 ≠ x3 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx14 : x1 ≠ x4 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx23 : x2 ≠ x3 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx24 : x2 ≠ x4 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hx34 : x3 ≠ x4 := mt hxsNodup.getElem_inj_iff.mp (by norm_num)
  have hxOdd : ∀ x ∈ xs, Odd x := by
    intro x hx
    exact of_decide_eq_true
      (List.mem_filter.mp (oddActiveBlock_mem_oddTrace (by simpa only [xs] using hx))).2
  have hsep := activeBlocks_separated hstanding
  have h0 := (hsep x0 (by simpa only [xs] using hx0) y0
    (by simpa only [ys] using hy0)).1
  have h1 := (hsep x1 (by simpa only [xs] using hx1) y0
    (by simpa only [ys] using hy0)).1
  have h2 := (hsep x2 (by simpa only [xs] using hx2) y0
    (by simpa only [ys] using hy0)).1
  have h3 := (hsep x3 (by simpa only [xs] using hx3) y0
    (by simpa only [ys] using hy0)).1
  have h4 := (hsep x4 (by simpa only [xs] using hx4) y0
    (by simpa only [ys] using hy0)).1
  have hySegment := mem_segment_of_mem_of_isTheta hstanding.1.1
    (List.mem_filter.mp (evenActiveBlock_mem_evenTrace
      (by simpa only [ys] using hy0))).1
  rcases hxOdd x0 hx0 with ⟨a0, ha0⟩
  rcases hxOdd x1 hx1 with ⟨a1, ha1⟩
  rcases hxOdd x2 hx2 with ⟨a2, ha2⟩
  rcases hxOdd x3 hx3 with ⟨a3, ha3⟩
  rcases hxOdd x4 hx4 with ⟨a4, ha4⟩
  simp only [segment, Finset.mem_Icc] at hySegment
  omega

/-- The omitted `6q < b₁ < 8q` subcase in the printed proof of Theorem 2.7.
The same forced-middle argument as the first case of Theorem 2.6 already
contradicts the existence of two active even entries. -/
lemma five_two_impossible_of_boundary_lt_eight {n : Nat} {gamma : List Nat}
    {b1 c1 : Nat}
    (hstanding : StandingInterleavingHypotheses n gamma)
    (hbEnd : EndsWith (oddTrace gamma) b1)
    (hcStart : StartsWith (evenTrace gamma) c1)
    (hbLower : b1 ∈ lowerHalf n)
    (hu : 5 <= (epilogue n (oddTrace gamma)).length)
    (hv : 2 <= (prologue n (evenTrace gamma)).length)
    (hbSix : 6 * dyadicQ n < b1) (hbEight : b1 < 8 * dyadicQ n) : False := by
  let q := dyadicQ n
  let B := epilogue n (oddTrace gamma)
  let C := prologue n (evenTrace gamma)
  have hqPos : 0 < q := by simpa only [q] using dyadicQ_pos n
  have hnSixteen := sixteen_le_of_five_two_active_lengths hstanding hu hv
  have hthreshold := sixteen_mul_dyadicQ_le hnSixteen
  have hgamma := hstanding.1.1
  obtain ⟨bs, cs, hbsEnd, hcsStart, hbsLower, hcsUpper, hsep, _hreflect⟩ :=
    standing_boundary_separated hstanding
  have hbsEq : bs = b1 := Option.some.inj (hbsEnd.symm.trans hbEnd)
  have hcsEq : cs = c1 := Option.some.inj (hcsStart.symm.trans hcStart)
  subst bs
  subst cs
  have hrev := isTheta_reversal hgamma
  have hpatternsRev := dyadic_pattern_sixteen hrev hthreshold
  have hpatterns := dyadic_pattern_sixteen hgamma hthreshold
  have hBLength : 4 <= B.length := by simpa only [B] using hu.trans' (by norm_num)
  have hCLength : 2 <= C.length := by simpa only [C] using hv
  have htraceStart : StartsWith (oddTrace (reversal gamma)) b1 := by
    simpa only [oddTrace_reversal_eq] using startsWith_reversal_of_endsWith hbEnd
  have hBStart : StartsWith B b1 := by
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      startsWith_prologue_of_startsWith (n := n) htraceStart
  have hBNodup : B.Nodup := by
    have htraceNodup : (oddTrace (reversal gamma)).Nodup :=
      (isTheta_nodup hrev).filter _
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      (prologue_prefix n (oddTrace (reversal gamma))).sublist.nodup htraceNodup
  have hBPositive : forall x, x ∈ B -> 0 < x := by
    intro x hx
    have hxTrace : x ∈ oddTrace gamma := by
      have hxRev : x ∈ reversal (oddTrace gamma) :=
        (prologue_prefix n (reversal (oddTrace gamma))).mem (by
          simpa only [B, epilogue] using hx)
      simpa only [reversal, List.mem_reverse] using hxRev
    exact positive_of_mem_of_isTheta hgamma (List.mem_filter.mp hxTrace).1
  have hBMax : forall x, x ∈ B -> x <= b1 := by
    intro x hx
    exact oddEpilogue_entry_le_last hgamma hbEnd hbLower (by simpa only [B] using hx)
  have hBPrefix : B <+: oddTrace (reversal gamma) := by
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      prologue_prefix n (oddTrace (reversal gamma))
  have hBCongruent : PrefixCongruent B 4 (2 * q) := by
    apply PrefixCongruent.of_prefix hBPrefix
      (by simpa only [q] using hpatternsRev.2.1.2.1) hBLength
  have hxB : b1 - 2 * q ∈ B := by
    exact (sub_two_mul_mem_of_four_prefix hqPos hBLength hBNodup hBStart
      hBPositive hBMax hBCongruent (by simpa only [q] using hbEight)).2
  let z := b1 - 6 * q
  have hzPos : 0 < z := by simp only [z]; omega
  have hbEq : b1 = 6 * q + z := by simp only [z]; omega
  have hbOdd : Odd b1 := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hzOdd : Odd z := by
    rcases hbOdd with ⟨b, hb⟩
    exact ⟨b - 3 * q, by simp only [z]; omega⟩
  have hnUpper : n < 16 * q + z := by
    by_contra hnot
    have hyLe : 16 * q + z <= n := by omega
    let x := 4 * q + z
    let y := 16 * q + z
    let m := 10 * q + z
    have hxEq : x = b1 - 2 * q := by simp only [x, hbEq]; omega
    have hxSegment : x ∈ segment n := by
      simp only [segment, Finset.mem_Icc, x]
      have hbSegment : b1 ∈ segment n := by
        simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
        omega
      simp only [segment, Finset.mem_Icc] at hbSegment
      omega
    have hySegment : y ∈ segment n := by
      simp only [segment, Finset.mem_Icc, y]
      omega
    have hmSegment : m ∈ segment n := by
      simp only [segment, Finset.mem_Icc, m]
      omega
    have hxOdd : Odd x := by
      rw [hxEq]
      rcases hbOdd with ⟨b, hb⟩
      exact ⟨b - q, by omega⟩
    have hyOdd : Odd y := by
      rcases hzOdd with ⟨a, ha⟩
      exact ⟨8 * q + a, by simp only [y]; omega⟩
    have hmOdd : Odd m := by
      rcases hzOdd with ⟨a, ha⟩
      exact ⟨5 * q + a, by simp only [m]; omega⟩
    have hdistX : Nat.dist ((b1 + 1) / 2) ((x + 1) / 2) = q := by
      rcases hbOdd with ⟨b, hb⟩
      rcases hxOdd with ⟨a, ha⟩
      simp only [x, hbEq] at *
      unfold Nat.dist
      omega
    have hdistM : Nat.dist ((b1 + 1) / 2) ((m + 1) / 2) = 2 * q := by
      rcases hbOdd with ⟨b, hb⟩
      rcases hmOdd with ⟨a, ha⟩
      simp only [m, hbEq] at *
      unfold Nat.dist
      omega
    have hdegree :
        binaryCongruenceDegree ((b1 + 1) / 2) ((x + 1) / 2) <
          binaryCongruenceDegree ((b1 + 1) / 2) ((m + 1) / 2) := by
      simp only [binaryCongruenceDegree, hdistX, hdistM, q, dyadicQ]
      rw [Nat.factorization_pow_self Nat.prime_two,
        factorization_two_mul_pow_two]
      omega
    have hmB := oddEpilogue_forced_middle hgamma hbEnd hxSegment hySegment
      hmSegment hbOdd hxOdd hyOdd hmOdd (by simp only [x, y, m]; omega)
      (by simp only [m, hbEq]; omega) (by simp only [x, hbEq]; omega)
      hdegree (by simpa only [B, hxEq] using hxB)
    have hmLe := hBMax m (by simpa only [B] using hmB)
    simp only [m, hbEq] at hmLe
    omega
  let c2 := C[1]'(by omega)
  have hc2Mem : c2 ∈ C := List.getElem_mem _
  have hc1Le : c1 <= c2 := evenPrologue_first_le_entry hgamma hcStart
    hcsUpper (by simpa only [C] using hc2Mem)
  have hCNodup : C.Nodup :=
    (prologue_prefix n (evenTrace gamma)).sublist.nodup ((isTheta_nodup hgamma).filter _)
  have hc1Ne : c1 ≠ c2 := by
    have hc1At : C[0]? = some c1 := by
      rw [← List.head?_eq_getElem?]
      exact startsWith_prologue_of_startsWith hcStart
    have hc2At : C[1]? = some c2 := by
      simpa only [c2] using (List.getElem?_eq_getElem (l := C) (i := 1) (by omega))
    intro h
    have hc2At' : C[1]? = some c1 := by simpa only [← h] using hc2At
    have := getElem?_index_unique_of_nodup hCNodup hc1At hc2At'
    omega
  have hc1Lt : c1 < c2 := by omega
  have hCPrefix : C <+: evenTrace gamma := prologue_prefix n (evenTrace gamma)
  have hCCongruent : PrefixCongruent C 2 (4 * q) := by
    apply PrefixCongruent.of_prefix hCPrefix
      (by simpa only [q] using hpatterns.2.2.1) hCLength
  have hc1At : C[0]? = some c1 := by
    rw [← List.head?_eq_getElem?]
    exact startsWith_prologue_of_startsWith hcStart
  have hc2At : C[1]? = some c2 := by
    simpa only [c2] using (List.getElem?_eq_getElem (l := C) (i := 1) (by omega))
  have hcMod : Nat.ModEq (4 * q) c1 c2 :=
    hCCongruent.2 0 (by omega) 1 (by omega) c1 c2 hc1At hc2At
  have hcGap := add_modulus_le_of_modEq_of_lt (by omega : 0 < 4 * q) hcMod hc1Lt
  have hc2Trace : c2 ∈ evenTrace gamma := hCPrefix.mem hc2Mem
  have hc2Segment := mem_segment_of_mem_of_isTheta hgamma (List.mem_filter.mp hc2Trace).1
  simp only [segment, Finset.mem_Icc] at hc2Segment
  omega

/-- Direct odd-epilogue form of the candidate-set step used in Theorem 2.7.
Unlike `prologue_dyadic_parameter`, this does not impose a half hypothesis on
the normalized odd-base first entry: a hypothetical failure of congruence is
sent back to the forbidden immediate predecessor by Theorem 2.4. -/
lemma oddEpilogue_dyadic_parameter {n : Nat} {gamma : List Nat} {b : Nat}
    (hgamma : IsTheta n gamma)
    (hbEnd : EndsWith (oddTrace gamma) b)
    (hbLower : b ∈ lowerHalf n)
    (hbOdd : Odd b)
    (hbEight : 8 * dyadicQ n < b)
    (hbSixteen : b < 16 * dyadicQ n) :
    ∀ x, x ∈ epilogue n (oddTrace gamma) →
      ∃ d : Nat, d ≤ 7 ∧ d ≠ 1 ∧
        x = b - (2 * dyadicQ n) * d ∧
        b = x + (2 * dyadicQ n) * d := by
  let q := dyadicQ n
  let e := Nat.log 2 n - 4
  have hqPos : 0 < q := by simpa only [q] using dyadicQ_pos n
  have hqPow : q = 2 ^ e := by rfl
  have hpredNot : b - 2 * q ∉ epilogue n (oddTrace gamma) := by
    simpa only [q] using dyadic_predecessor_not_mem_oddEpilogue hgamma hbEnd
      hbLower hbOdd hbEight hbSixteen
  intro x hxEpi
  have hxLe : x ≤ b := oddEpilogue_entry_le_last hgamma hbEnd hbLower hxEpi
  have hxTrace : x ∈ oddTrace gamma := by
    apply oddActiveBlock_mem_oddTrace (n := n)
    simpa only [oddActiveBlock, List.mem_reverse] using hxEpi
  have hxSegment : x ∈ segment n :=
    mem_segment_of_mem_of_isTheta hgamma (List.mem_filter.mp hxTrace).1
  have hxOdd : Odd x := of_decide_eq_true (List.mem_filter.mp hxTrace).2
  have hmod : Nat.ModEq (2 * q) x b := by
    by_contra hnotMod
    have hxb : x ≠ b := by
      intro h
      subst x
      exact hnotMod Nat.ModEq.rfl
    have hxLt : x < b := by omega
    let y := 2 * b - 4 * q - x
    let z := b - 2 * q
    have hyExact : y + 4 * q + x = 2 * b := by
      simp only [y]
      omega
    have hbSegment : b ∈ segment n := by
      simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
      omega
    have hySegment : y ∈ segment n := by
      simp only [y, lowerHalf, segment, Finset.mem_Icc] at hxSegment hbSegment hbLower ⊢
      omega
    have hzSegment : z ∈ segment n := by
      simp only [z, segment, Finset.mem_Icc] at hbSegment ⊢
      omega
    have hyOdd : Odd y := by
      rcases hbOdd with ⟨B, hb⟩
      rcases hxOdd with ⟨X, hx⟩
      refine ⟨2 * B - 2 * q - X, ?_⟩
      simp only [y]
      omega
    have hzOdd : Odd z := by
      rcases hbOdd with ⟨B, hb⟩
      refine ⟨B - q, ?_⟩
      simp only [z]
      omega
    have hmean : x + y = 2 * z := by
      simp only [y, z]
      omega
    have hdistX :
        Nat.dist ((b + 1) / 2) ((x + 1) / 2) = (b - x) / 2 := by
      rcases hbOdd with ⟨B, hb⟩
      rcases hxOdd with ⟨X, hx⟩
      unfold Nat.dist
      omega
    have htwiceDistX :
        b - x = 2 * Nat.dist ((b + 1) / 2) ((x + 1) / 2) := by
      rw [hdistX]
      rcases hbOdd with ⟨B, hb⟩
      rcases hxOdd with ⟨X, hx⟩
      omega
    have hdistXNe : Nat.dist ((b + 1) / 2) ((x + 1) / 2) ≠ 0 := by
      intro hzero
      have hhalfEq := Nat.eq_of_dist_eq_zero hzero
      rcases hbOdd with ⟨B, hb⟩
      rcases hxOdd with ⟨X, hx⟩
      omega
    have hdegreeX :
        binaryCongruenceDegree ((b + 1) / 2) ((x + 1) / 2) < e := by
      unfold binaryCongruenceDegree
      by_contra hnotLt
      have hpowDvd : 2 ^ e ∣ Nat.dist ((b + 1) / 2) ((x + 1) / 2) :=
        (Nat.prime_two.pow_dvd_iff_le_factorization hdistXNe).2 (by omega)
      rw [← hqPow] at hpowDvd
      rcases hpowDvd with ⟨k, hk⟩
      have htwoQDvd : 2 * q ∣ b - x := by
        refine ⟨k, ?_⟩
        rw [htwiceDistX, hk]
        ring
      exact hnotMod ((Nat.modEq_iff_dvd' hxLe).2 htwoQDvd)
    have hdistZ :
        Nat.dist ((b + 1) / 2) ((z + 1) / 2) = q := by
      rcases hbOdd with ⟨B, hb⟩
      simp only [z]
      unfold Nat.dist
      omega
    have hdegreeZ :
        binaryCongruenceDegree ((b + 1) / 2) ((z + 1) / 2) = e := by
      simp only [binaryCongruenceDegree, hdistZ, hqPow]
      exact Nat.factorization_pow_self Nat.prime_two
    have hzEpi := oddEpilogue_forced_middle hgamma hbEnd hxSegment hySegment
      hzSegment hbOdd hxOdd hyOdd hzOdd hmean (by simp only [z]; omega) hxb.symm
      (by rw [hdegreeZ]; exact hdegreeX) hxEpi
    exact hpredNot (by simpa only [z] using hzEpi)
  obtain ⟨d, hd⟩ := (Nat.modEq_iff_exists_eq_add hxLe).mp hmod
  have hdEq : b = x + (2 * q) * d := by simpa [Nat.mul_comm] using hd
  have hdLe : d ≤ 7 := by
    by_contra hnot
    have hmul := Nat.mul_le_mul_left (2 * q) (show 8 ≤ d by omega)
    have hxPos : 0 < x := by
      simp only [segment, Finset.mem_Icc] at hxSegment
      exact hxSegment.1
    omega
  have hdNe : d ≠ 1 := by
    intro hone
    subst d
    simp only [Nat.mul_one] at hdEq
    have hxEq : x = b - 2 * q := by omega
    exact hpredNot (hxEq ▸ hxEpi)
  refine ⟨d, hdLe, hdNe, ?_, ?_⟩
  change x = b - (2 * q) * d
  omega
  simpa only [q] using hdEq

lemma no_five_distinct_coefficients_le_four {d₀ d₁ d₂ d₃ d₄ : Nat}
    (hd₀ : d₀ ≤ 4) (hd₁ : d₁ ≤ 4) (hd₂ : d₂ ≤ 4)
    (hd₃ : d₃ ≤ 4) (hd₄ : d₄ ≤ 4)
    (hone₀ : d₀ ≠ 1) (hone₁ : d₁ ≠ 1) (hone₂ : d₂ ≠ 1)
    (hone₃ : d₃ ≠ 1) (hone₄ : d₄ ≠ 1)
    (h₀₁ : d₀ ≠ d₁) (h₀₂ : d₀ ≠ d₂) (h₀₃ : d₀ ≠ d₃)
    (h₀₄ : d₀ ≠ d₄) (h₁₂ : d₁ ≠ d₂) (h₁₃ : d₁ ≠ d₃)
    (h₁₄ : d₁ ≠ d₄) (h₂₃ : d₂ ≠ d₃) (h₂₄ : d₂ ≠ d₄)
    (h₃₄ : d₃ ≠ d₄) : False := by
  omega

lemma three_and_five_among_five_coefficients {d₀ d₁ d₂ d₃ d₄ : Nat}
    (hd₀ : d₀ ≤ 5) (hd₁ : d₁ ≤ 5) (hd₂ : d₂ ≤ 5)
    (hd₃ : d₃ ≤ 5) (hd₄ : d₄ ≤ 5)
    (hone₀ : d₀ ≠ 1) (hone₁ : d₁ ≠ 1) (hone₂ : d₂ ≠ 1)
    (hone₃ : d₃ ≠ 1) (hone₄ : d₄ ≠ 1)
    (h₀₁ : d₀ ≠ d₁) (h₀₂ : d₀ ≠ d₂) (h₀₃ : d₀ ≠ d₃)
    (h₀₄ : d₀ ≠ d₄) (h₁₂ : d₁ ≠ d₂) (h₁₃ : d₁ ≠ d₃)
    (h₁₄ : d₁ ≠ d₄) (h₂₃ : d₂ ≠ d₃) (h₂₄ : d₂ ≠ d₄)
    (h₃₄ : d₃ ≠ d₄) :
    (d₀ = 3 ∨ d₁ = 3 ∨ d₂ = 3 ∨ d₃ = 3 ∨ d₄ = 3) ∧
      (d₀ = 5 ∨ d₁ = 5 ∨ d₂ = 5 ∨ d₃ = 5 ∨ d₄ = 5) := by
  omega

/-- Five distinct positive candidates cannot fit strictly below `10q` once
the forbidden first predecessor is removed. -/
lemma five_dyadic_candidates_impossible_below_ten {word : List Nat}
    {b q : Nat} (_hqPos : 0 < q) (hbTen : b < 10 * q)
    (hlength : 5 ≤ word.length) (hnodup : word.Nodup)
    (hpositive : ∀ x, x ∈ word → 0 < x)
    (hparam : ∀ x, x ∈ word →
      ∃ d : Nat, d ≤ 7 ∧ d ≠ 1 ∧
        x = b - (2 * q) * d ∧ b = x + (2 * q) * d) : False := by
  let x₀ := word[0]'(by omega)
  let x₁ := word[1]'(by omega)
  let x₂ := word[2]'(by omega)
  let x₃ := word[3]'(by omega)
  let x₄ := word[4]'(by omega)
  have hx₀ : x₀ ∈ word := List.getElem_mem _
  have hx₁ : x₁ ∈ word := List.getElem_mem _
  have hx₂ : x₂ ∈ word := List.getElem_mem _
  have hx₃ : x₃ ∈ word := List.getElem_mem _
  have hx₄ : x₄ ∈ word := List.getElem_mem _
  obtain ⟨d₀, hd₀Le, hd₀One, _, hd₀Eq⟩ := hparam x₀ hx₀
  obtain ⟨d₁, hd₁Le, hd₁One, _, hd₁Eq⟩ := hparam x₁ hx₁
  obtain ⟨d₂, hd₂Le, hd₂One, _, hd₂Eq⟩ := hparam x₂ hx₂
  obtain ⟨d₃, hd₃Le, hd₃One, _, hd₃Eq⟩ := hparam x₃ hx₃
  obtain ⟨d₄, hd₄Le, hd₄One, _, hd₄Eq⟩ := hparam x₄ hx₄
  have hd₀Four : d₀ ≤ 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 5 ≤ d₀ by omega)
    have := hpositive x₀ hx₀
    omega
  have hd₁Four : d₁ ≤ 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 5 ≤ d₁ by omega)
    have := hpositive x₁ hx₁
    omega
  have hd₂Four : d₂ ≤ 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 5 ≤ d₂ by omega)
    have := hpositive x₂ hx₂
    omega
  have hd₃Four : d₃ ≤ 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 5 ≤ d₃ by omega)
    have := hpositive x₃ hx₃
    omega
  have hd₄Four : d₄ ≤ 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 5 ≤ d₄ by omega)
    have := hpositive x₄ hx₄
    omega
  have hx₀₁ : x₀ ≠ x₁ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₂ : x₀ ≠ x₂ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₃ : x₀ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₄ : x₀ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₂ : x₁ ≠ x₂ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₃ : x₁ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₄ : x₁ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₂₃ : x₂ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₂₄ : x₂ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₃₄ : x₃ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hd₀₁ := coefficient_ne_of_values_ne hd₀Eq hd₁Eq hx₀₁
  have hd₀₂ := coefficient_ne_of_values_ne hd₀Eq hd₂Eq hx₀₂
  have hd₀₃ := coefficient_ne_of_values_ne hd₀Eq hd₃Eq hx₀₃
  have hd₀₄ := coefficient_ne_of_values_ne hd₀Eq hd₄Eq hx₀₄
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₁₄ := coefficient_ne_of_values_ne hd₁Eq hd₄Eq hx₁₄
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hd₂₄ := coefficient_ne_of_values_ne hd₂Eq hd₄Eq hx₂₄
  have hd₃₄ := coefficient_ne_of_values_ne hd₃Eq hd₄Eq hx₃₄
  exact no_five_distinct_coefficients_le_four hd₀Four hd₁Four hd₂Four
    hd₃Four hd₄Four hd₀One hd₁One hd₂One hd₃One hd₄One
    hd₀₁ hd₀₂ hd₀₃ hd₀₄ hd₁₂ hd₁₃ hd₁₄ hd₂₃ hd₂₄ hd₃₄

/-- Below `12q`, five distinct positive candidates exhaust the coefficients
`0,2,3,4,5`; in particular the third and fifth predecessors occur. -/
lemma sub_six_and_sub_ten_mem_of_five_dyadic_candidates {word : List Nat}
    {b q : Nat} (_hqPos : 0 < q) (hbTwelve : b < 12 * q)
    (hlength : 5 ≤ word.length) (hnodup : word.Nodup)
    (hpositive : ∀ x, x ∈ word → 0 < x)
    (hparam : ∀ x, x ∈ word →
      ∃ d : Nat, d ≤ 7 ∧ d ≠ 1 ∧
        x = b - (2 * q) * d ∧ b = x + (2 * q) * d) :
    b - 6 * q ∈ word ∧ b - 10 * q ∈ word := by
  let x₀ := word[0]'(by omega)
  let x₁ := word[1]'(by omega)
  let x₂ := word[2]'(by omega)
  let x₃ := word[3]'(by omega)
  let x₄ := word[4]'(by omega)
  have hx₀ : x₀ ∈ word := List.getElem_mem _
  have hx₁ : x₁ ∈ word := List.getElem_mem _
  have hx₂ : x₂ ∈ word := List.getElem_mem _
  have hx₃ : x₃ ∈ word := List.getElem_mem _
  have hx₄ : x₄ ∈ word := List.getElem_mem _
  obtain ⟨d₀, hd₀Le, hd₀One, _, hd₀Eq⟩ := hparam x₀ hx₀
  obtain ⟨d₁, hd₁Le, hd₁One, _, hd₁Eq⟩ := hparam x₁ hx₁
  obtain ⟨d₂, hd₂Le, hd₂One, _, hd₂Eq⟩ := hparam x₂ hx₂
  obtain ⟨d₃, hd₃Le, hd₃One, _, hd₃Eq⟩ := hparam x₃ hx₃
  obtain ⟨d₄, hd₄Le, hd₄One, _, hd₄Eq⟩ := hparam x₄ hx₄
  have hd₀Five : d₀ ≤ 5 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 6 ≤ d₀ by omega)
    have := hpositive x₀ hx₀
    omega
  have hd₁Five : d₁ ≤ 5 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 6 ≤ d₁ by omega)
    have := hpositive x₁ hx₁
    omega
  have hd₂Five : d₂ ≤ 5 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 6 ≤ d₂ by omega)
    have := hpositive x₂ hx₂
    omega
  have hd₃Five : d₃ ≤ 5 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 6 ≤ d₃ by omega)
    have := hpositive x₃ hx₃
    omega
  have hd₄Five : d₄ ≤ 5 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (2 * q) (show 6 ≤ d₄ by omega)
    have := hpositive x₄ hx₄
    omega
  have hx₀₁ : x₀ ≠ x₁ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₂ : x₀ ≠ x₂ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₃ : x₀ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₀₄ : x₀ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₂ : x₁ ≠ x₂ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₃ : x₁ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₁₄ : x₁ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₂₃ : x₂ ≠ x₃ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₂₄ : x₂ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hx₃₄ : x₃ ≠ x₄ := mt hnodup.getElem_inj_iff.mp (by norm_num)
  have hd₀₁ := coefficient_ne_of_values_ne hd₀Eq hd₁Eq hx₀₁
  have hd₀₂ := coefficient_ne_of_values_ne hd₀Eq hd₂Eq hx₀₂
  have hd₀₃ := coefficient_ne_of_values_ne hd₀Eq hd₃Eq hx₀₃
  have hd₀₄ := coefficient_ne_of_values_ne hd₀Eq hd₄Eq hx₀₄
  have hd₁₂ := coefficient_ne_of_values_ne hd₁Eq hd₂Eq hx₁₂
  have hd₁₃ := coefficient_ne_of_values_ne hd₁Eq hd₃Eq hx₁₃
  have hd₁₄ := coefficient_ne_of_values_ne hd₁Eq hd₄Eq hx₁₄
  have hd₂₃ := coefficient_ne_of_values_ne hd₂Eq hd₃Eq hx₂₃
  have hd₂₄ := coefficient_ne_of_values_ne hd₂Eq hd₄Eq hx₂₄
  have hd₃₄ := coefficient_ne_of_values_ne hd₃Eq hd₄Eq hx₃₄
  obtain ⟨hthree, hfive⟩ := three_and_five_among_five_coefficients
    hd₀Five hd₁Five hd₂Five hd₃Five hd₄Five hd₀One hd₁One hd₂One
    hd₃One hd₄One hd₀₁ hd₀₂ hd₀₃ hd₀₄ hd₁₂ hd₁₃ hd₁₄ hd₂₃ hd₂₄ hd₃₄
  constructor
  · rcases hthree with h | h | h | h | h
    · subst d₀
      have hxEq : x₀ = b - 6 * q := by omega
      simpa only [hxEq] using hx₀
    · subst d₁
      have hxEq : x₁ = b - 6 * q := by omega
      simpa only [hxEq] using hx₁
    · subst d₂
      have hxEq : x₂ = b - 6 * q := by omega
      simpa only [hxEq] using hx₂
    · subst d₃
      have hxEq : x₃ = b - 6 * q := by omega
      simpa only [hxEq] using hx₃
    · subst d₄
      have hxEq : x₄ = b - 6 * q := by omega
      simpa only [hxEq] using hx₄
  · rcases hfive with h | h | h | h | h
    · subst d₀
      have hxEq : x₀ = b - 10 * q := by omega
      simpa only [hxEq] using hx₀
    · subst d₁
      have hxEq : x₁ = b - 10 * q := by omega
      simpa only [hxEq] using hx₁
    · subst d₂
      have hxEq : x₂ = b - 10 * q := by omega
      simpa only [hxEq] using hx₂
    · subst d₃
      have hxEq : x₃ = b - 10 * q := by omega
      simpa only [hxEq] using hx₃
    · subst d₄
      have hxEq : x₄ = b - 10 * q := by omega
      simpa only [hxEq] using hx₄

/-- Two congruent active even entries, together with boundary separation,
leave at least one full modulus beyond twice the odd boundary endpoint. -/
lemma ambient_gap_of_two_even_prologue {n : Nat} {gamma : List Nat}
    {b c m : Nat} (hgamma : IsTheta n gamma)
    (hcStart : StartsWith (evenTrace gamma) c)
    (hcUpper : c ∈ upperHalf n) (hbc : 2 * b ≤ c)
    (hmPos : 0 < m)
    (hv : 2 ≤ (prologue n (evenTrace gamma)).length)
    (hcongruent : PrefixCongruent (evenTrace gamma) 2 m) :
    2 * b + m ≤ n := by
  let C := prologue n (evenTrace gamma)
  let c₂ := C[1]'(by
    simpa only [C] using
      (show 1 < (prologue n (evenTrace gamma)).length by omega))
  have hc₂Mem : c₂ ∈ C := List.getElem_mem _
  have hcLe : c ≤ c₂ := evenPrologue_first_le_entry hgamma hcStart hcUpper
    (by simpa only [C] using hc₂Mem)
  have hCNodup : C.Nodup := by
    exact (prologue_prefix n (evenTrace gamma)).sublist.nodup
      ((isTheta_nodup hgamma).filter _)
  have hcAt : C[0]? = some c := by
    rw [← List.head?_eq_getElem?]
    simpa only [C, StartsWith] using startsWith_prologue_of_startsWith (n := n) hcStart
  have hc₂At : C[1]? = some c₂ := by
    simpa only [c₂] using
      (List.getElem?_eq_getElem (l := C) (i := 1) (by
        simpa only [C] using
          (show 1 < (prologue n (evenTrace gamma)).length by omega)))
  have hcNe : c ≠ c₂ := by
    intro h
    have hc₂At' : C[1]? = some c := by simpa only [← h] using hc₂At
    have := getElem?_index_unique_of_nodup hCNodup hcAt hc₂At'
    omega
  have hcLt : c < c₂ := by omega
  have hCPrefix : C <+: evenTrace gamma := by
    simpa only [C] using prologue_prefix n (evenTrace gamma)
  have hCMod : PrefixCongruent C 2 m :=
    PrefixCongruent.of_prefix hCPrefix hcongruent (by simpa only [C] using hv)
  have hmod : Nat.ModEq m c c₂ :=
    hCMod.2 0 (by omega) 1 (by omega) c c₂ hcAt hc₂At
  have hgap := add_modulus_le_of_modEq_of_lt hmPos hmod hcLt
  have hc₂Trace : c₂ ∈ evenTrace gamma := hCPrefix.mem hc₂Mem
  have hc₂Segment := mem_segment_of_mem_of_isTheta hgamma
    (List.mem_filter.mp hc₂Trace).1
  simp only [segment, Finset.mem_Icc] at hc₂Segment
  omega

/-- The one-sided content of Theorem 2.7, conditional only on Theorem 2.6.
The reverse implication should be obtained from the reflected active-list
profile, rather than by an invalid full-word reversal/complement symmetry. -/
theorem theorem_2_7_left_of_theorem_2_6 (h₂₆ : theorem_2_6) :
    ∀ (n : Nat) (gamma : List Nat), StandingInterleavingHypotheses n gamma →
      5 ≤ (epilogue n (oddTrace gamma)).length →
        (prologue n (evenTrace gamma)).length = 1 := by
  intro n gamma hstanding hu
  let q := dyadicQ n
  let B := epilogue n (oddTrace gamma)
  let C := prologue n (evenTrace gamma)
  have hgamma : IsTheta n gamma := hstanding.1.1
  have hvUpper : C.length ≤ 2 := by
    simpa only [C] using (h₂₆ n gamma hstanding).1 (by omega)
  obtain ⟨b, c, hbEnd, hcStart, hbLower, hcUpper, hbc, _hreflection⟩ :=
    standing_boundary_separated hstanding
  have hCStart : StartsWith C c := by
    simpa only [C] using startsWith_prologue_of_startsWith (n := n) hcStart
  have hcMem : c ∈ C := mem_of_startsWith hCStart
  have hCPos : 0 < C.length :=
    List.length_pos_of_ne_nil (List.ne_nil_of_mem hcMem)
  change C.length = 1
  by_contra hvNe
  have hv : 2 ≤ C.length := by omega
  have hnSixteen : 16 ≤ n := sixteen_le_of_five_two_active_lengths hstanding
    (by simpa only [B] using hu) (by simpa only [C] using hv)
  have hthreshold : 16 * q ≤ n := by
    simpa only [q] using sixteen_mul_dyadicQ_le hnSixteen
  have hnThirtyTwo : n < 32 * q := by
    simpa only [q] using thirty_two_dyadicQ_gt hnSixteen
  have hpatterns := dyadic_pattern_sixteen hgamma (by simpa only [q] using hthreshold)
  have hrev : IsTheta n (reversal gamma) := isTheta_reversal hgamma
  have hpatternsRev := dyadic_pattern_sixteen hrev (by simpa only [q] using hthreshold)
  have hBLength : 4 ≤ B.length := by simpa only [B] using hu.trans' (by norm_num)
  have htraceStart : StartsWith (oddTrace (reversal gamma)) b := by
    simpa only [oddTrace_reversal_eq] using startsWith_reversal_of_endsWith hbEnd
  have hBStart : StartsWith B b := by
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      startsWith_prologue_of_startsWith (n := n) htraceStart
  have hBNodup : B.Nodup := by
    have htraceNodup : (oddTrace (reversal gamma)).Nodup :=
      (isTheta_nodup hrev).filter _
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      (prologue_prefix n (oddTrace (reversal gamma))).sublist.nodup htraceNodup
  have hBPositive : ∀ x, x ∈ B → 0 < x := by
    intro x hx
    have hxTrace : x ∈ oddTrace gamma := by
      apply oddActiveBlock_mem_oddTrace (n := n)
      simpa only [B, oddActiveBlock, List.mem_reverse] using hx
    exact positive_of_mem_of_isTheta hgamma (List.mem_filter.mp hxTrace).1
  have hBMax : ∀ x, x ∈ B → x ≤ b := by
    intro x hx
    exact oddEpilogue_entry_le_last hgamma hbEnd hbLower (by simpa only [B] using hx)
  have hBPrefix : B <+: oddTrace (reversal gamma) := by
    simpa only [B, epilogue, oddTrace_reversal_eq] using
      prologue_prefix n (oddTrace (reversal gamma))
  have hBCongruent : PrefixCongruent B 4 (2 * q) := by
    apply PrefixCongruent.of_prefix hBPrefix
      (by simpa only [q] using hpatternsRev.2.1.2.1) hBLength
  have hqPos : 0 < q := by simpa only [q] using dyadicQ_pos n
  by_cases hbUnderEight : b < 8 * q
  · have hbSix := (sub_two_mul_mem_of_four_prefix hqPos hBLength hBNodup
      hBStart hBPositive hBMax hBCongruent hbUnderEight).1
    exact five_two_impossible_of_boundary_lt_eight hstanding hbEnd hcStart hbLower
      (by simpa only [B] using hu) (by simpa only [C] using hv) hbSix
      (by simpa only [q] using hbUnderEight)
  have hbNeEight : b ≠ 8 * q := by
    intro h
    rcases (show Odd b from
      of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2) with ⟨k, hk⟩
    omega
  have hbEight : 8 * q < b := by omega
  have hbSixteen : b < 16 * q := by
    have hbLower' := hbLower
    simp only [lowerHalf, Finset.mem_Icc] at hbLower'
    omega
  have hbOdd : Odd b :=
    of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hparam : ∀ x, x ∈ B →
      ∃ d : Nat, d ≤ 7 ∧ d ≠ 1 ∧
        x = b - (2 * q) * d ∧ b = x + (2 * q) * d := by
    intro x hx
    simpa only [B, q] using oddEpilogue_dyadic_parameter hgamma hbEnd hbLower
      hbOdd (by simpa only [q] using hbEight)
      (by simpa only [q] using hbSixteen) x (by simpa only [B] using hx)
  have hgapFour : 2 * b + 4 * q ≤ n := by
    apply ambient_gap_of_two_even_prologue hgamma hcStart hcUpper hbc (by omega)
      (by simpa only [C] using hv)
    simpa only [q] using hpatterns.2.2.1
  by_cases hnTwentyFour : n < 24 * q
  · by_cases hnTwenty : n < 20 * q
    · omega
    · have hbTen : b < 10 * q := by omega
      exact five_dyadic_candidates_impossible_below_ten hqPos hbTen
        (by simpa only [B] using hu) hBNodup hBPositive hparam
  have hnTwentyFourLe : 24 * q ≤ n := by omega
  have hbTwelve : b < 12 * q := by
    by_cases hnTwentyEight : n < 28 * q
    · omega
    · have hnTwentyEightLe : 28 * q ≤ n := by omega
      have hprefixEight := evenTrace_prefix_two_mod_eight_of_twenty_eight
        hgamma (by simpa only [q] using hthreshold)
        (by simpa only [q] using hnTwentyEightLe)
      have hgapEight : 2 * b + 8 * q ≤ n := by
        apply ambient_gap_of_two_even_prologue hgamma hcStart hcUpper hbc (by omega)
          (by simpa only [C] using hv)
        simpa only [q] using hprefixEight
      omega
  obtain ⟨hsubSix, hsubTen⟩ :=
    sub_six_and_sub_ten_mem_of_five_dyadic_candidates hqPos hbTwelve
      (by simpa only [B] using hu) hBNodup hBPositive hparam
  have hnUpper : n < b + 14 * q := by
    simpa only [q] using ambient_lt_b_add_fourteen_of_sub_six_mem hgamma hbEnd
      hbLower hbOdd (by omega) (by simpa only [B, q] using hsubSix)
  have hsubTenPos := hBPositive (b - 10 * q) hsubTen
  omega

end LeanProofs.Sharma2012
