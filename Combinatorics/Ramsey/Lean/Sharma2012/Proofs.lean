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

/-! ## Elementary facts about permutation words -/

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

end LeanProofs.Sharma2012
