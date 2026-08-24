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

end LeanProofs.Sharma2012
