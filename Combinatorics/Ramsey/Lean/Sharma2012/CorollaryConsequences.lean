import Sharma2012.Proofs

set_option autoImplicit false

open Finset Filter

namespace LeanProofs.Sharma2012

lemma prologue_length_le_append (n : Nat) (left right : List Nat) :
    (prologue n left).length ≤ (prologue n (left ++ right)).length := by
  cases left with
  | nil => simp [prologue]
  | cons a tail =>
      simp only [List.cons_append, prologue, List.length_cons]
      rw [List.takeWhile_append]
      split <;> simp_all

lemma sameHalf_evenLift_iff (m a b : Nat) :
    SameHalf (2 * m) (2 * a) (2 * b) ↔ SameHalf m a b := by
  simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc]
  omega

lemma sameHalf_oddLift_odd_iff (m a b : Nat) :
    SameHalf (2 * m - 1) (2 * a - 1) (2 * b - 1) ↔ SameHalf m a b := by
  simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc]
  omega

lemma sameHalf_evenLift_odd_iff (m a b : Nat) :
    SameHalf (2 * m + 1) (2 * a) (2 * b) ↔ SameHalf m a b := by
  simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc]
  omega

lemma prologue_evenLift_length (m : Nat) (word : List Nat) :
    (prologue (2 * m) (evenLift word)).length =
      (prologue m word).length := by
  cases word with
  | nil => simp [prologue, evenLift]
  | cons a tail =>
      simp only [prologue, evenLift, List.map_cons, List.takeWhile_map,
        List.length_cons, List.length_map, Function.comp_def]
      congr 2
      congr 1
      funext b
      exact decide_eq_decide.mpr (sameHalf_evenLift_iff m a b)

lemma prologue_oddLift_odd_length (m : Nat) (word : List Nat) :
    (prologue (2 * m - 1) (oddLift word)).length =
      (prologue m word).length := by
  cases word with
  | nil => simp [prologue, oddLift]
  | cons a tail =>
      simp only [prologue, oddLift, List.map_cons, List.takeWhile_map,
        List.length_cons, List.length_map, Function.comp_def]
      congr 2
      congr 1
      funext b
      exact decide_eq_decide.mpr (sameHalf_oddLift_odd_iff m a b)

lemma prologue_evenLift_odd_length (m : Nat) (word : List Nat) :
    (prologue (2 * m + 1) (evenLift word)).length =
      (prologue m word).length := by
  cases word with
  | nil => simp [prologue, evenLift]
  | cons a tail =>
      simp only [prologue, evenLift, List.map_cons, List.takeWhile_map,
        List.length_cons, List.length_map, Function.comp_def]
      congr 2
      congr 1
      funext b
      exact decide_eq_decide.mpr (sameHalf_evenLift_odd_iff m a b)

lemma prologue_evenTrace_length_le_six {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    (prologue n (evenTrace word)).length ≤ 6 := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨m, hm⟩
    have hbase := isTheta_evenBase hword
    have hbound := theorem_2_5_holds (n / 2) (evenBase word) hbase
    have hlift := prologue_evenLift_length (n / 2) (evenBase word)
    rw [evenLift_evenBase] at hlift
    have hnEq : n = 2 * (n / 2) := by omega
    rw [hnEq]
    rw [hlift]
    exact hbound
  · rcases hnOdd with ⟨m, hm⟩
    have hbase := isTheta_evenBase hword
    have hbound := theorem_2_5_holds (n / 2) (evenBase word) hbase
    have hlift := prologue_evenLift_odd_length (n / 2) (evenBase word)
    rw [evenLift_evenBase] at hlift
    have hnEq : n = 2 * (n / 2) + 1 := by omega
    rw [hnEq]
    rw [hlift]
    exact hbound

lemma prologue_oddTrace_length_le_six {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    (prologue n (oddTrace word)).length ≤ 6 := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨m, hm⟩
    have hnEq : n = 2 * (n / 2) := by omega
    let base := oddBase word
    have hbase : IsTheta (n / 2) base := by
      have hceil : (n + 1) / 2 = n / 2 := by omega
      simpa only [base, hceil] using isTheta_oddBase hword
    have hdelta : IsTheta (2 * (n / 2))
        (oddLift base ++ evenLift base) :=
      isTheta_oddEvenLifts_even hbase hbase
    have hprefix := prologue_length_le_append
      (2 * (n / 2)) (oddLift base) (evenLift base)
    have hbound := theorem_2_5_holds _ _ hdelta
    rw [hnEq]
    rw [← oddLift_oddBase (word := word)]
    exact hprefix.trans hbound
  · rcases hnOdd with ⟨m, hm⟩
    let base := oddBase word
    have hbase : IsTheta ((n + 1) / 2) base := by
      exact isTheta_oddBase hword
    have hnEq : n = 2 * ((n + 1) / 2) - 1 := by omega
    have hlift := prologue_oddLift_odd_length ((n + 1) / 2) base
    have hbound := theorem_2_5_holds ((n + 1) / 2) base hbase
    rw [← hnEq] at hlift
    rw [oddLift_oddBase] at hlift
    rw [hlift]
    exact hbound

lemma oddTrace_reversal (word : List Nat) :
    oddTrace (reversal word) = reversal (oddTrace word) := by
  simp [oddTrace, trace, reversal]

lemma evenTrace_reversal (word : List Nat) :
    evenTrace (reversal word) = reversal (evenTrace word) := by
  simp [evenTrace, trace, reversal]

lemma epilogue_oddTrace_length_le_six {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    (epilogue n (oddTrace word)).length ≤ 6 := by
  have h := prologue_oddTrace_length_le_six (isTheta_reversal hword)
  simpa [epilogue, oddTrace_reversal] using h

lemma epilogue_evenTrace_length_le_six {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    (epilogue n (evenTrace word)).length ≤ 6 := by
  have h := prologue_evenTrace_length_le_six (isTheta_reversal hword)
  simpa [epilogue, evenTrace_reversal] using h

lemma fixedPrefix_before_target {n : Nat} {word trace : List Nat} {y : Nat}
    (hwordNodup : word.Nodup) (htraceNodup : trace.Nodup)
    (htraceSub : trace.Sublist word) (hySegment : y ∈ segment n)
    (htraceSegment : ∀ z ∈ trace, z ∈ segment n)
    (hforce : ∀ z ∈ trace, SameHalf n z y → OccursLeftOf word z y) :
    ∀ x ∈ oddFixedBlock n trace, OccursLeftOf word x y := by
  classical
  intro x hx
  let remainder :=
    (reversal trace).drop (epilogue n trace).length
  cases hremainder : remainder with
  | nil =>
      have hfixedNil : oddFixedBlock n trace = [] := by
        simp [oddFixedBlock, remainder, hremainder]
      simp [hfixedNil] at hx
  | cons d ds =>
      cases hreverse : reversal trace with
      | nil =>
          have : remainder = [] := by simp [remainder, hreverse]
          rw [hremainder] at this
          simp at this
      | cons b bs =>
          have hfixedEq : oddFixedBlock n trace = (d :: ds).reverse := by
            simp [oddFixedBlock, remainder, hremainder]
          have hdRemainder : d ∈ remainder := by simp [hremainder]
          have hdReverse : d ∈ reversal trace :=
            (List.drop_sublist _ _).mem (by simpa [remainder] using hdRemainder)
          have hdTrace : d ∈ trace := by simpa [reversal] using hdReverse
          have hbReverse : b ∈ reversal trace := by rw [hreverse]; simp
          have hbTrace : b ∈ trace := by simpa [reversal] using hbReverse
          have hdSegment := htraceSegment d hdTrace
          have hbSegment := htraceSegment b hbTrace
          have hreverseStart : StartsWith (reversal trace) b := by
            rw [hreverse]
            simp [StartsWith]
          have hbEnd : EndsWith trace b := by
            have h := endsWith_reversal_of_startsWith hreverseStart
            simpa [reversal] using h
          have hremainderStart : StartsWith remainder d := by
            simp [hremainder, StartsWith]
          have hnotSame : ¬ SameHalf n b d :=
            first_after_prologue_not_sameHalf hreverseStart (by
              simpa [remainder, epilogue] using hremainderStart)
          have hdbNe : d ≠ b := by
            intro h
            subst d
            apply hnotSame
            simp only [SameHalf, lowerHalf, upperHalf, segment,
              Finset.mem_Icc] at hbSegment ⊢
            omega
          have hdbTrace : OccursLeftOf trace d b :=
            occursLeftOf_of_mem_of_endsWith htraceNodup hbEnd hdTrace hdbNe
          have hdb : OccursLeftOf word d b :=
            occursLeftOf_of_sublist htraceSub hdbTrace
          have hfixedNodup : (oddFixedBlock n trace).Nodup := by
            rw [hfixedEq]
            apply List.nodup_reverse.mpr
            have hreverseNodup : (reversal trace).Nodup := by
              simpa [reversal] using List.nodup_reverse.mpr htraceNodup
            have hremainderNodup : remainder.Nodup := by
              dsimp only [remainder]
              exact (List.drop_sublist _ _).nodup hreverseNodup
            rw [hremainder] at hremainderNodup
            exact hremainderNodup
          have hdEndsFixed : EndsWith (oddFixedBlock n trace) d := by
            simp [hfixedEq, EndsWith]
          have hxBeforeOrEq : x = d ∨ OccursLeftOf word x d := by
            by_cases hxd : x = d
            · exact Or.inl hxd
            · right
              have hxdFixed := occursLeftOf_of_mem_of_endsWith
                hfixedNodup hdEndsFixed hx hxd
              have hfixedPrefix : oddFixedBlock n trace <+: trace :=
                ⟨oddActiveBlock n trace,
                  oddFixed_append_oddActive n trace⟩
              have hxdTrace := occursLeftOf_of_sublist
                hfixedPrefix.sublist hxdFixed
              exact occursLeftOf_of_sublist htraceSub hxdTrace
          have hsame : SameHalf n d y ∨ SameHalf n b y := by
            simp only [SameHalf, lowerHalf, upperHalf, segment,
              Finset.mem_Icc] at hnotSame hdSegment hbSegment hySegment ⊢
            omega
          rcases hsame with hdy | hby
          · have hdyOrder := hforce d hdTrace hdy
            rcases hxBeforeOrEq with rfl | hxd
            · exact hdyOrder
            · exact occursLeftOf_trans hwordNodup hxd hdyOrder
          · have hbyOrder := hforce b hbTrace hby
            have hxb : OccursLeftOf word x b := by
              rcases hxBeforeOrEq with rfl | hxd
              · exact hdb
              · exact occursLeftOf_trans hwordNodup hxd hdb
            exact occursLeftOf_trans hwordNodup hxb hbyOrder

lemma half_sub_six_le_index_of_even_of_isTheta12
    {n : Nat} {word : List Nat} {i y : Nat}
    (hword : IsTheta12 n word) (hy : word[i]? = some y)
    (hyEven : Even y) :
    n / 2 - 6 ≤ i := by
  let fixed := oddFixedBlock n (oddTrace word)
  have hyMem : y ∈ word := List.mem_iff_getElem?.mpr ⟨i, hy⟩
  have hySegment := mem_segment_of_mem_of_isTheta hword.1 hyMem
  have hoddNodup : (oddTrace word).Nodup := (isTheta_nodup hword.1).filter _
  have hfixedNodup : fixed.Nodup := by
    dsimp only [fixed]
    exact (show oddFixedBlock n (oddTrace word) <+: oddTrace word from
      ⟨oddActiveBlock n (oddTrace word),
        oddFixed_append_oddActive n (oddTrace word)⟩).sublist.nodup hoddNodup
  have hbefore : ∀ x ∈ fixed, OccursLeftOf word x y := by
    dsimp only [fixed]
    apply fixedPrefix_before_target
      (isTheta_nodup hword.1) hoddNodup List.filter_sublist hySegment
    · intro z hz
      exact mem_segment_of_mem_of_isTheta hword.1 (List.mem_filter.mp hz).1
    · intro z hz hsame
      have hzSegment := mem_segment_of_mem_of_isTheta hword.1
        (List.mem_filter.mp hz).1
      have hzOdd : Odd z := of_decide_eq_true (List.mem_filter.mp hz).2
      exact (corollary_2_2_1_holds n z y hzSegment hySegment hsame).1
        hzOdd hyEven word hword
  have hfixedIndex : fixed.length ≤ i := by
    apply index_lower_bound_of_occursLeftOf_family
      (isTheta_nodup hword.1) hy
      (fun t : Fin fixed.length => fixed.get t)
    · exact hfixedNodup.injective_get
    · intro t
      exact hbefore (fixed.get t) (List.get_mem fixed t)
  have hsplit := congrArg List.length
    (oddFixed_append_oddActive n (oddTrace word))
  simp only [List.length_append] at hsplit
  have hactive := oddActiveBlock_length n (oddTrace word)
  have hepilogue := epilogue_oddTrace_length_le_six hword.1
  have htraceLength := isTheta_length (isTheta_oddBase hword.1)
  simp only [oddBase, List.length_map] at htraceLength
  dsimp only [fixed] at hfixedIndex
  omega

lemma sameHalf_symm {n x y : Nat} (h : SameHalf n x y) :
    SameHalf n y x := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨hy, hx⟩
  · exact Or.inr ⟨hy, hx⟩

lemma isTheta12_reversal_of_isTheta21 {n : Nat} {word : List Nat}
    (hn : 2 ≤ n) (hword : IsTheta21 n word) :
    IsTheta12 n (reversal word) := by
  rcases hword.2 with ⟨first, hfirst, hfirstEven⟩
  obtain ⟨first', last, hfirst', hlast, hfirstLast⟩ :=
    proposition_2_1_holds n word hn hword.1
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
  exact ⟨isTheta_reversal hword.1,
    ⟨last, startsWith_reversal_of_endsWith hlast, hlastOdd⟩⟩

lemma half_sub_six_le_index_of_odd_of_isTheta21
    {n : Nat} {word : List Nat} {i y : Nat}
    (hn : 2 ≤ n) (hword : IsTheta21 n word)
    (hy : word[i]? = some y) (hyOdd : Odd y) :
    n / 2 - 6 ≤ i := by
  let fixed := oddFixedBlock n (evenTrace word)
  have hyMem : y ∈ word := List.mem_iff_getElem?.mpr ⟨i, hy⟩
  have hySegment := mem_segment_of_mem_of_isTheta hword.1 hyMem
  have hevenNodup : (evenTrace word).Nodup := (isTheta_nodup hword.1).filter _
  have hfixedNodup : fixed.Nodup := by
    dsimp only [fixed]
    exact (show oddFixedBlock n (evenTrace word) <+: evenTrace word from
      ⟨oddActiveBlock n (evenTrace word),
        oddFixed_append_oddActive n (evenTrace word)⟩).sublist.nodup hevenNodup
  have hreverse12 := isTheta12_reversal_of_isTheta21 hn hword
  have hbefore : ∀ x ∈ fixed, OccursLeftOf word x y := by
    dsimp only [fixed]
    apply fixedPrefix_before_target
      (isTheta_nodup hword.1) hevenNodup List.filter_sublist hySegment
    · intro z hz
      exact mem_segment_of_mem_of_isTheta hword.1 (List.mem_filter.mp hz).1
    · intro z hz hsame
      have hzSegment := mem_segment_of_mem_of_isTheta hword.1
        (List.mem_filter.mp hz).1
      have hzEven : Even z := of_decide_eq_true (List.mem_filter.mp hz).2
      have hforced := (corollary_2_2_1_holds n y z hySegment hzSegment
        (sameHalf_symm hsame)).1 hyOdd hzEven
        (reversal word) hreverse12
      exact occursLeftOf_of_occursLeftOf_reversal hforced
  have hfixedIndex : fixed.length ≤ i := by
    apply index_lower_bound_of_occursLeftOf_family
      (isTheta_nodup hword.1) hy
      (fun t : Fin fixed.length => fixed.get t)
    · exact hfixedNodup.injective_get
    · intro t
      exact hbefore (fixed.get t) (List.get_mem fixed t)
  have hsplit := congrArg List.length
    (oddFixed_append_oddActive n (evenTrace word))
  simp only [List.length_append] at hsplit
  have hactive := oddActiveBlock_length n (evenTrace word)
  have hepilogue := epilogue_evenTrace_length_le_six hword.1
  have htraceLength := isTheta_length (isTheta_evenBase hword.1)
  simp only [evenBase, List.length_map] at htraceLength
  dsimp only [fixed] at hfixedIndex
  omega

theorem corollary_2_7_2_holds : corollary_2_7_2 := by
  intro n word hword
  constructor
  · rw [isTheta_length hword]
    omega
  · intro i hi j hj x y hx hy
    by_cases hk : n / 2 - 6 = 0
    · omega
    · have hn : 2 ≤ n := by omega
      have hne : word ≠ [] := by
        intro hnil
        subst word
        simp at hx
      let first := word.head hne
      have hfirst : StartsWith word first := List.head?_eq_some_head hne
      rcases Nat.even_or_odd first with hfirstEven | hfirstOdd
      · have hword21 : IsTheta21 n word :=
          ⟨hword, ⟨first, hfirst, hfirstEven⟩⟩
        have hxEven : Even x := by
          rcases Nat.even_or_odd x with hxEven | hxOdd
          · exact hxEven
          · have hbound := half_sub_six_le_index_of_odd_of_isTheta21
              hn hword21 hx hxOdd
            omega
        have hyEven : Even y := by
          rcases Nat.even_or_odd y with hyEven | hyOdd
          · exact hyEven
          · have hbound := half_sub_six_le_index_of_odd_of_isTheta21
              hn hword21 hy hyOdd
            omega
        rcases hxEven with ⟨a, ha⟩
        rcases hyEven with ⟨b, hb⟩
        unfold Nat.ModEq
        omega
      · have hword12 : IsTheta12 n word :=
          ⟨hword, ⟨first, hfirst, hfirstOdd⟩⟩
        have hxOdd : Odd x := by
          rcases Nat.even_or_odd x with hxEven | hxOdd
          · have hbound := half_sub_six_le_index_of_even_of_isTheta12
              hword12 hx hxEven
            omega
          · exact hxOdd
        have hyOdd : Odd y := by
          rcases Nat.even_or_odd y with hyEven | hyOdd
          · have hbound := half_sub_six_le_index_of_even_of_isTheta12
              hword12 hy hyEven
            omega
          · exact hyOdd
        rcases hxOdd with ⟨a, ha⟩
        rcases hyOdd with ⟨b, hb⟩
        unfold Nat.ModEq
        omega

lemma interleaving_word_eq_odd_append_even_of_doNotCommute
    {n b c : Nat} {gammaOdd gammaEven word : List Nat}
    (hword12 : IsTheta12 n word)
    (hoddTrace : oddTrace word = gammaOdd)
    (hevenTrace : evenTrace word = gammaEven)
    (hbEnd : EndsWith gammaOdd b) (hcStart : StartsWith gammaEven c)
    (hforced : DoNotCommute n b c) :
    word = gammaOdd ++ gammaEven := by
  have hwordNodup := isTheta_nodup hword12.1
  have hoddNodup : gammaOdd.Nodup := by
    rw [← hoddTrace]
    exact hwordNodup.filter _
  have hevenNodup : gammaEven.Nodup := by
    rw [← hevenTrace]
    exact hwordNodup.filter _
  have hbefore : ∀ x ∈ gammaOdd, ∀ y ∈ gammaEven,
      OccursLeftOf word x y := by
    intro x hx y hy
    have hxb : x = b ∨ OccursLeftOf word x b := by
      by_cases hxbEq : x = b
      · exact Or.inl hxbEq
      · right
        have htrace := occursLeftOf_of_mem_of_endsWith hoddNodup hbEnd hx hxbEq
        apply occursLeftOf_of_sublist
          (small := oddTrace word) (large := word) List.filter_sublist
        rw [hoddTrace]
        exact htrace
    have hcy : c = y ∨ OccursLeftOf word c y := by
      by_cases hcyEq : c = y
      · exact Or.inl hcyEq
      · right
        have htrace := occursLeftOf_of_startsWith_of_mem
          hevenNodup hcStart hy hcyEq
        apply occursLeftOf_of_sublist
          (small := evenTrace word) (large := word) List.filter_sublist
        rw [hevenTrace]
        exact htrace
    have hbc := hforced word hword12
    rcases hxb with rfl | hxb <;> rcases hcy with rfl | hcy
    · exact hbc
    · exact occursLeftOf_trans hwordNodup hbc hcy
    · exact occursLeftOf_trans hwordNodup hxb hbc
    · exact occursLeftOf_trans hwordNodup
        (occursLeftOf_trans hwordNodup hxb hbc) hcy
  let p : Nat → Bool := fun z => decide (Odd z)
  obtain ⟨middle, hmiddle, hdecomp⟩ :=
    eq_fixedPrefix_interleaving_fixedSuffix
      (p := p) (oddFixed := gammaOdd) (oddActive := [])
      (evenActive := []) (evenFixed := gammaEven) (word := word)
      hwordNodup
      (by
        intro x hx
        have hx' : x ∈ oddTrace word := by rw [hoddTrace]; exact hx
        exact (List.mem_filter.mp hx').2)
      (by simp)
      (by simp)
      (by
        intro y hy
        have hy' : y ∈ evenTrace word := by rw [hevenTrace]; exact hy
        have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hy').2
        exact decide_eq_false (Nat.not_odd_iff_even.mpr hyEven))
      (by
        change oddTrace word = gammaOdd ++ []
        simpa using hoddTrace)
      (by
        change word.filter (fun z => !(decide (Odd z))) = [] ++ gammaEven
        rw [filter_not_odd_eq_evenTrace]
        simpa using hevenTrace)
      (by simpa using hbefore)
      (by simpa using hbefore)
  have hmiddleNil : middle = [] := by
    simpa [listInterleavings] using hmiddle
  subst middle
  simpa using hdecomp

lemma interleavingClass_card_le_one_of_doNotCommute
    {n b c : Nat} {gammaOdd gammaEven : List Nat}
    (hbEnd : EndsWith gammaOdd b) (hcStart : StartsWith gammaEven c)
    (hforced : DoNotCommute n b c) :
    (interleavingClass n gammaOdd gammaEven).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro sigma hsigma tau htau
  have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
      oddTrace (permutationWord sigma) = gammaOdd ∧
      evenTrace (permutationWord sigma) = gammaEven := by
    simpa [interleavingClass] using hsigma
  have htauData : IsTheta12 n (permutationWord tau) ∧
      oddTrace (permutationWord tau) = gammaOdd ∧
      evenTrace (permutationWord tau) = gammaEven := by
    simpa [interleavingClass] using htau
  apply permutationWord_injective
  rw [interleaving_word_eq_odd_append_even_of_doNotCommute
      hsigmaData.1 hsigmaData.2.1 hsigmaData.2.2 hbEnd hcStart hforced,
    interleaving_word_eq_odd_append_even_of_doNotCommute
      htauData.1 htauData.2.1 htauData.2.2 hbEnd hcStart hforced]

lemma doNotCommute_of_not_commute {n x y : Nat}
    (hxSegment : x ∈ segment n) (hySegment : y ∈ segment n)
    (hxOdd : Odd x) (hyEven : Even y) (hnot : ¬ Commute n x y) :
    DoNotCommute n x y := by
  intro word hword12
  have hxMem := mem_of_mem_segment_of_isTheta hword12.1 hxSegment
  have hyMem := mem_of_mem_segment_of_isTheta hword12.1 hySegment
  have hxy : x ≠ y := by
    rcases hxOdd with ⟨a, ha⟩
    rcases hyEven with ⟨b, hb⟩
    omega
  rcases occursLeftOf_total_of_mem (isTheta_nodup hword12.1)
      hxMem hyMem hxy with hleft | hright
  · exact hleft
  · exact False.elim (hnot ⟨word, hword12, hright⟩)

lemma doNotCommute_not_commute {n x y : Nat}
    (hforced : DoNotCommute n x y) : ¬ Commute n x y := by
  rintro ⟨word, hword12, hright⟩
  exact (occursLeftOf_asymm (isTheta_nodup hword12.1)
    (hforced word hword12)) hright


/-- The two end-block theorems already imply the sharp class-size bound for
every interleaving class satisfying the paper's standing hypotheses.  This
separates the finite binomial calculation from the remaining endpoint cases
needed for Corollary 2.7.1. -/
theorem standing_interleavingClass_card_le_twenty
    (h26 : theorem_2_6) (h27 : theorem_2_7)
    {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card ≤ 20 := by
  let u := (epilogue n (oddTrace gamma)).length
  let v := (prologue n (evenTrace gamma)).length
  have hcard :
      (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card =
        Nat.choose (u + v) v := by
    simpa only [u, v] using lemma_2_5_holds n gamma hstanding
  have hu : u ≤ 6 := epilogue_oddTrace_length_le_six hstanding.1.1
  have hv : v ≤ 6 := prologue_evenTrace_length_le_six hstanding.1.1
  have h26' : (4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2) := by
    simpa only [u, v] using h26 n gamma hstanding
  have h27' : (5 ≤ u → v = 1) ∧ (5 ≤ v → u = 1) := by
    simpa only [u, v] using h27 n gamma hstanding
  rw [hcard]
  interval_cases u <;> interval_cases v <;>
    first | omega | norm_num [Nat.choose]

end LeanProofs.Sharma2012
