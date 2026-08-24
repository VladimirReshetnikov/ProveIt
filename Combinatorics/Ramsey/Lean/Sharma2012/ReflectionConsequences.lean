import Sharma2012.Proofs

/-!
# Reflection consequences for Sharma's active end blocks

This module removes the possible odd ambient maximum, reverses the remaining
word, and reflects it through the next odd center.  The construction transports
standing interleaving hypotheses to the even active ambient.  Its transformed
odd active list is exact, while its transformed even active list may only grow;
that one-sided comparison supplies the missing implication of Theorem 2.6.
-/

set_option autoImplicit false

open Finset

namespace LeanProofs.Sharma2012

/-- Restrict a word to the largest even initial ambient segment.  If `n` is
odd this removes only its maximum; if `n` is even it leaves the word alone. -/
def reflectedActiveCore (n : Nat) (word : List Nat) : List Nat :=
  word.filter fun x => decide (x ≤ reflectedActiveAmbient n)

/-- Reverse the even-ambient core and reflect its values through the odd
center immediately above that ambient. -/
def reflectedActiveWord (n : Nat) (word : List Nat) : List Nat :=
  complement (reflectedActiveAmbient n) (reversal (reflectedActiveCore n word))

lemma reflectedActiveCore_sublist (n : Nat) (word : List Nat) :
    (reflectedActiveCore n word).Sublist word := by
  unfold reflectedActiveCore
  exact List.filter_sublist

lemma reflectedActiveCore_toFinset {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    (reflectedActiveCore n word).toFinset = segment (reflectedActiveAmbient n) := by
  rw [reflectedActiveCore, List.toFinset_filter, hword.1.2]
  ext x
  simp only [Finset.mem_filter, segment, Finset.mem_Icc,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hxPos, hxn⟩, hxN⟩
    exact ⟨hxPos, hxN⟩
  · rintro ⟨hxPos, hxN⟩
    exact ⟨⟨hxPos, hxN.trans (reflectedActiveAmbient_le n)⟩, hxN⟩

lemma isTheta_reflectedActiveCore {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    IsTheta (reflectedActiveAmbient n) (reflectedActiveCore n word) := by
  refine ⟨⟨(isTheta_nodup hword).filter _, reflectedActiveCore_toFinset hword⟩, ?_⟩
  exact threeFree_of_sublist (isTheta_threeFree hword) List.filter_sublist

lemma isTheta_reflectedActiveWord {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    IsTheta (reflectedActiveAmbient n) (reflectedActiveWord n word) := by
  exact isTheta_complement (isTheta_reversal (isTheta_reflectedActiveCore hword))

lemma reflectedActiveAmbient_even (n : Nat) : Even (reflectedActiveAmbient n) := by
  refine ⟨n / 2, ?_⟩
  simp only [reflectedActiveAmbient]
  omega

lemma dyadicQ_reflectedActiveAmbient (n : Nat) :
    dyadicQ (reflectedActiveAmbient n) = dyadicQ n := by
  rcases reflectedActiveAmbient_eq_self_or_pred n with hN | hN
  · rw [hN]
  · unfold dyadicQ
    by_cases hzero : reflectedActiveAmbient n = 0
    · have hn : n = 1 := by omega
      calc
        2 ^ (Nat.log 2 (reflectedActiveAmbient n) - 4) =
            2 ^ (Nat.log 2 0 - 4) := by rw [hzero]
        _ = 2 ^ (Nat.log 2 1 - 4) := by norm_num
        _ = 2 ^ (Nat.log 2 n - 4) := by rw [hn]
    · have hlog : Nat.log 2 (reflectedActiveAmbient n) =
          Nat.log 2 (reflectedActiveAmbient n + 1) := by
        rw [Nat.log_eq_log_succ_iff (by norm_num) hzero]
        intro hpow
        have hNpos : 0 < reflectedActiveAmbient n := Nat.pos_of_ne_zero hzero
        have hlogPos : 0 < Nat.log 2 (reflectedActiveAmbient n + 1) := by
          rw [Nat.log_pos_iff]
          omega
        have hpowEven : Even (2 ^ Nat.log 2 (reflectedActiveAmbient n + 1)) := by
          let e := Nat.log 2 (reflectedActiveAmbient n + 1)
          refine ⟨2 ^ (e - 1), ?_⟩
          have he : e = (e - 1) + 1 := by simp only [e]; omega
          calc
            2 ^ Nat.log 2 (reflectedActiveAmbient n + 1) = 2 ^ e := rfl
            _ = 2 ^ ((e - 1) + 1) := congrArg (fun t : Nat => 2 ^ t) he
            _ = 2 ^ (e - 1) * 2 := by rw [pow_succ]
            _ = 2 ^ (e - 1) + 2 ^ (e - 1) := by ring
        have hsuccOdd : Odd (reflectedActiveAmbient n + 1) := by
          rcases reflectedActiveAmbient_even n with ⟨k, hk⟩
          exact ⟨k, by omega⟩
        rw [hpow] at hpowEven
        exact (Nat.not_even_iff_odd.mpr hsuccOdd) hpowEven
      calc
        2 ^ (Nat.log 2 (reflectedActiveAmbient n) - 4) =
            2 ^ (Nat.log 2 (reflectedActiveAmbient n + 1) - 4) := by rw [hlog]
        _ = 2 ^ (Nat.log 2 n - 4) := by rw [hN]

lemma mem_segment_of_mem_reflectedActiveCore {n : Nat} {word : List Nat} {x : Nat}
    (hword : IsTheta n word) (hx : x ∈ reflectedActiveCore n word) :
    x ∈ segment (reflectedActiveAmbient n) := by
  rw [← reflectedActiveCore_toFinset hword]
  exact List.mem_toFinset.mpr hx

lemma activeReflection_odd_iff_even_of_mem_segment {n x : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n)) :
    Odd (activeReflection n x) ↔ Even x := by
  simp only [segment, Finset.mem_Icc, reflectedActiveAmbient] at hx
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨n / 2 - k, ?_⟩
    simp only [activeReflection, reflectedActiveAmbient] at hk ⊢
    omega
  · rintro ⟨k, hk⟩
    refine ⟨n / 2 - k, ?_⟩
    simp only [activeReflection, reflectedActiveAmbient] at hk ⊢
    omega

lemma activeReflection_even_iff_odd_of_mem_segment {n x : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n)) :
    Even (activeReflection n x) ↔ Odd x := by
  simp only [segment, Finset.mem_Icc, reflectedActiveAmbient] at hx
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨n / 2 - k, ?_⟩
    simp only [activeReflection, reflectedActiveAmbient] at hk ⊢
    omega
  · rintro ⟨k, hk⟩
    refine ⟨n / 2 - k, ?_⟩
    simp only [activeReflection, reflectedActiveAmbient] at hk ⊢
    omega

lemma oddTrace_map_activeReflection {n : Nat} {word : List Nat}
    (hword : ∀ x ∈ word, x ∈ segment (reflectedActiveAmbient n)) :
    oddTrace (word.map (activeReflection n)) =
      (evenTrace word).map (activeReflection n) := by
  induction word with
  | nil => simp [oddTrace, evenTrace, trace]
  | cons x xs ih =>
      have hxSegment := hword x (by simp)
      have htail : ∀ y ∈ xs, y ∈ segment (reflectedActiveAmbient n) := by
        intro y hy
        exact hword y (by simp [hy])
      have hparity : decide (Odd (activeReflection n x)) = decide (Even x) := by
        exact decide_eq_decide.mpr (activeReflection_odd_iff_even_of_mem_segment hxSegment)
      have ih' := ih htail
      simp only [oddTrace, evenTrace, trace] at ih' ⊢
      simp only [List.map_cons, List.filter_cons, hparity, ih']
      split <;> simp

lemma evenTrace_map_activeReflection {n : Nat} {word : List Nat}
    (hword : ∀ x ∈ word, x ∈ segment (reflectedActiveAmbient n)) :
    evenTrace (word.map (activeReflection n)) =
      (oddTrace word).map (activeReflection n) := by
  induction word with
  | nil => simp [oddTrace, evenTrace, trace]
  | cons x xs ih =>
      have hxSegment := hword x (by simp)
      have htail : ∀ y ∈ xs, y ∈ segment (reflectedActiveAmbient n) := by
        intro y hy
        exact hword y (by simp [hy])
      have hparity : decide (Even (activeReflection n x)) = decide (Odd x) := by
        exact decide_eq_decide.mpr (activeReflection_even_iff_odd_of_mem_segment hxSegment)
      have ih' := ih htail
      simp only [oddTrace, evenTrace, trace] at ih' ⊢
      simp only [List.map_cons, List.filter_cons, hparity, ih']
      split <;> simp

lemma evenTrace_filter_reflectedActiveAmbient_eq (n : Nat) (word : List Nat)
    (hmem : ∀ x ∈ word, x ∈ segment n) :
    evenTrace (word.filter fun x => decide (x ≤ reflectedActiveAmbient n)) =
      evenTrace word := by
  induction word with
  | nil => simp [evenTrace, trace]
  | cons x xs ih =>
      have hxSegment := hmem x (by simp)
      have htail : ∀ y ∈ xs, y ∈ segment n := by
        intro y hy
        exact hmem y (by simp [hy])
      specialize ih htail
      by_cases hxLe : x ≤ reflectedActiveAmbient n
      · have hxLeBool : decide (x ≤ reflectedActiveAmbient n) = true :=
          decide_eq_true hxLe
        simp only [List.filter_cons, hxLeBool, if_true]
        simp only [evenTrace, trace] at ih ⊢
        simp only [List.filter_cons]
        rw [ih]
      · have hxOdd : Odd x := by
          rcases reflectedActiveAmbient_eq_self_or_pred n with hN | hN
          · simp only [segment, Finset.mem_Icc] at hxSegment
            omega
          · have hxEq : x = reflectedActiveAmbient n + 1 := by
              simp only [segment, Finset.mem_Icc] at hxSegment
              omega
            rw [hxEq]
            rcases reflectedActiveAmbient_even n with ⟨k, hk⟩
            exact ⟨k, by omega⟩
        have hxNotEven : ¬ Even x := Nat.not_even_iff_odd.mpr hxOdd
        have hxLeBool : decide (x ≤ reflectedActiveAmbient n) = false :=
          decide_eq_false hxLe
        have hxEvenBool : decide (Even x) = false := decide_eq_false hxNotEven
        simp only [List.filter_cons, hxLeBool, Bool.false_eq_true, if_false]
        simp only [evenTrace, trace, List.filter_cons, hxEvenBool,
          Bool.false_eq_true, if_false] at ih ⊢
        exact ih

lemma evenTrace_reflectedActiveCore {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    evenTrace (reflectedActiveCore n word) = evenTrace word := by
  apply evenTrace_filter_reflectedActiveAmbient_eq n word
  intro x hx
  exact mem_segment_of_mem_of_isTheta hword hx

lemma oddTrace_reflectedActiveCore (n : Nat) (word : List Nat) :
    oddTrace (reflectedActiveCore n word) =
      (oddTrace word).filter fun x => decide (x ≤ reflectedActiveAmbient n) := by
  unfold oddTrace trace reflectedActiveCore
  exact List.filter_comm (p := fun x => decide (Odd x))
    (fun x => decide (x ≤ reflectedActiveAmbient n)) word

lemma evenTrace_reversal_eq (word : List Nat) :
    evenTrace (reversal word) = reversal (evenTrace word) := by
  simp [evenTrace, trace, reversal]

lemma oddTrace_reflectedActiveWord {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    oddTrace (reflectedActiveWord n word) =
      (reversal (evenTrace word)).map (activeReflection n) := by
  have hmem : ∀ x ∈ reversal (reflectedActiveCore n word),
      x ∈ segment (reflectedActiveAmbient n) := by
    intro x hx
    apply mem_segment_of_mem_reflectedActiveCore hword
    simpa only [reversal, List.mem_reverse] using hx
  have htrace := oddTrace_map_activeReflection hmem
  change oddTrace ((reversal (reflectedActiveCore n word)).map (activeReflection n)) = _
  simpa only [evenTrace_reversal_eq, evenTrace_reflectedActiveCore hword] using htrace

lemma evenTrace_reflectedActiveWord {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    evenTrace (reflectedActiveWord n word) =
      (reversal (oddTrace (reflectedActiveCore n word))).map
        (activeReflection n) := by
  have hmem : ∀ x ∈ reversal (reflectedActiveCore n word),
      x ∈ segment (reflectedActiveAmbient n) := by
    intro x hx
    apply mem_segment_of_mem_reflectedActiveCore hword
    simpa only [reversal, List.mem_reverse] using hx
  have htrace := evenTrace_map_activeReflection hmem
  change evenTrace ((reversal (reflectedActiveCore n word)).map (activeReflection n)) = _
  simpa only [oddTrace_reversal_eq] using htrace

lemma sameHalf_activeReflection_iff_of_mem_segment {n x y : Nat}
    (hx : x ∈ segment (reflectedActiveAmbient n))
    (hy : y ∈ segment (reflectedActiveAmbient n)) :
    SameHalf (reflectedActiveAmbient n) (activeReflection n x) (activeReflection n y) ↔
      SameHalf n x y := by
  simp only [segment, Finset.mem_Icc, reflectedActiveAmbient] at hx hy
  simp only [SameHalf, lowerHalf, upperHalf, Finset.mem_Icc,
    activeReflection, reflectedActiveAmbient]
  omega

lemma takeWhile_eq_of_eq_on {α : Type*} {p q : α → Bool} {word : List α}
    (h : ∀ x ∈ word, p x = q x) : word.takeWhile p = word.takeWhile q := by
  induction word with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, p y = q y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.takeWhile_cons, hx]
      split <;> simp_all

lemma prologue_map_eq_map_prologue_of_sameHalf_iff
    {sourceAmbient targetAmbient : Nat} {f : Nat → Nat} {word : List Nat}
    (h : ∀ x ∈ word, ∀ y ∈ word,
      SameHalf targetAmbient (f x) (f y) ↔ SameHalf sourceAmbient x y) :
    prologue targetAmbient (word.map f) = (prologue sourceAmbient word).map f := by
  cases word with
  | nil => simp [prologue]
  | cons x xs =>
      simp only [prologue, List.map_cons, List.takeWhile_map]
      congr 1
      apply congrArg (List.map f)
      apply takeWhile_eq_of_eq_on
      intro y hy
      exact decide_eq_decide.mpr (h x (by simp) y (by simp [hy]))

lemma prologue_map_activeReflection {n : Nat} {word : List Nat}
    (hword : ∀ x ∈ word, x ∈ segment (reflectedActiveAmbient n)) :
    prologue (reflectedActiveAmbient n) (word.map (activeReflection n)) =
      (prologue n word).map (activeReflection n) := by
  apply prologue_map_eq_map_prologue_of_sameHalf_iff
  intro x hx y hy
  exact sameHalf_activeReflection_iff_of_mem_segment (hword x hx) (hword y hy)

private lemma reflected_prologue_idempotent (n : Nat) (word : List Nat) :
    prologue n (prologue n word) = prologue n word := by
  classical
  cases word with
  | nil => simp [prologue]
  | cons first tail =>
      simp only [prologue]
      congr 1
      apply List.takeWhile_eq_self_iff.mpr
      intro x hx
      exact List.mem_takeWhile_imp
        (p := fun y => decide (SameHalf n first y)) (l := tail) hx

private lemma reflected_prologue_length_le_append
    (n : Nat) (left right : List Nat) :
    (prologue n left).length ≤ (prologue n (left ++ right)).length := by
  cases left with
  | nil => simp [prologue]
  | cons first tail =>
      simp only [List.cons_append, prologue, List.length_cons]
      rw [List.takeWhile_append]
      split <;> simp_all

private lemma reflected_filter_preserves_true_prefix {α : Type*} {p : α → Bool}
    {pre word : List α} (hprefix : pre <+: word)
    (htrue : ∀ x ∈ pre, p x = true) :
    ∃ suffix, word.filter p = pre ++ suffix := by
  rcases hprefix with ⟨suffix, rfl⟩
  refine ⟨suffix.filter p, ?_⟩
  rw [List.filter_append, List.filter_eq_self.mpr htrue]

lemma evenTrace_mem_reflectedActiveAmbient {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    ∀ x ∈ evenTrace word, x ∈ segment (reflectedActiveAmbient n) := by
  intro x hx
  have hxCoreTrace : x ∈ evenTrace (reflectedActiveCore n word) := by
    rw [evenTrace_reflectedActiveCore hword]
    exact hx
  have hxCore : x ∈ reflectedActiveCore n word :=
    (List.mem_filter.mp hxCoreTrace).1
  exact mem_segment_of_mem_reflectedActiveCore hword hxCore

lemma oddBoundaryActiveList_reflectedActiveWord {n : Nat} {word : List Nat}
    (hword : IsTheta n word) :
    oddBoundaryActiveList (reflectedActiveAmbient n) (reflectedActiveWord n word) =
      reflectedOddActiveList n word := by
  rw [oddBoundaryActiveList, oddTrace_reflectedActiveWord hword]
  have hreverse :
      reversal ((reversal (evenTrace word)).map (activeReflection n)) =
        (evenTrace word).map (activeReflection n) := by
    simp [reversal]
  rw [epilogue, hreverse,
    prologue_map_activeReflection (evenTrace_mem_reflectedActiveAmbient hword)]
  rfl

/-- Filtering out the possible odd ambient maximum can extend the transformed
even active list, but it cannot shorten the reflected original odd active
list.  In particular, equality is false without an extra hypothesis: for
`n = 7` the standing word `[5, 1, 7, 3, 6, 2, 4]` has original odd active
list `[3]`, while removing `7` exposes `[3, 1]` in the core. -/
lemma oddBoundaryActiveList_length_le_reflected_even {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    (oddBoundaryActiveList n gamma).length ≤
      (evenBoundaryActiveList (reflectedActiveAmbient n)
        (reflectedActiveWord n gamma)).length := by
  have htheta : IsTheta n gamma := hstanding.1.1
  have hcoreMem : ∀ x ∈ reversal (oddTrace (reflectedActiveCore n gamma)),
      x ∈ segment (reflectedActiveAmbient n) := by
    intro x hx
    apply mem_segment_of_mem_reflectedActiveCore htheta
    have hxTrace : x ∈ oddTrace (reflectedActiveCore n gamma) := by
      simpa only [reversal, List.mem_reverse] using hx
    exact (List.mem_filter.mp hxTrace).1
  rw [evenBoundaryActiveList, evenTrace_reflectedActiveWord htheta,
    prologue_map_activeReflection hcoreMem, List.length_map]
  have hreverseCore :
      reversal (oddTrace (reflectedActiveCore n gamma)) =
        (reversal (oddTrace gamma)).filter
          (fun x => decide (x ≤ reflectedActiveAmbient n)) := by
    rw [oddTrace_reflectedActiveCore]
    simp only [reversal, List.filter_reverse]
  rw [hreverseCore]
  let B := prologue n (reversal (oddTrace gamma))
  have hBPrefix : B <+: reversal (oddTrace gamma) := by
    simpa only [B] using prologue_prefix n (reversal (oddTrace gamma))
  rcases hstanding.2 with
    ⟨b, c, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hreverseStart : StartsWith (reversal (oddTrace gamma)) b :=
    startsWith_reversal_of_endsWith hbEnd
  have hBTrue : ∀ x ∈ B,
      decide (x ≤ reflectedActiveAmbient n) = true := by
    intro x hx
    apply decide_eq_true
    have hxLower : x ∈ lowerHalf n :=
      mem_lowerHalf_of_mem_prologue hreverseStart hbLower (by simpa only [B] using hx)
    simp only [lowerHalf, Finset.mem_Icc, reflectedActiveAmbient] at hxLower ⊢
    omega
  obtain ⟨suffix, hfilter⟩ :=
    reflected_filter_preserves_true_prefix hBPrefix hBTrue
  rw [hfilter]
  have hself : prologue n B = B := by
    simpa only [B] using reflected_prologue_idempotent n (reversal (oddTrace gamma))
  calc
    (oddBoundaryActiveList n gamma).length = B.length := rfl
    _ = (prologue n B).length := congrArg List.length hself.symm
    _ ≤ (prologue n (B ++ suffix)).length :=
      reflected_prologue_length_le_append n B suffix

lemma endsWith_filter_of_true {p : Nat → Bool} {word : List Nat} {x : Nat}
    (hend : EndsWith word x) (hx : p x = true) :
    EndsWith (word.filter p) x := by
  unfold EndsWith at hend ⊢
  rw [List.getLast?_eq_some_iff] at hend ⊢
  rcases hend with ⟨pre, rfl⟩
  refine ⟨pre.filter p, ?_⟩
  simp [hx]

lemma endsWith_map_of_endsWith {f : Nat → Nat} {word : List Nat} {x : Nat}
    (hend : EndsWith word x) : EndsWith (word.map f) (f x) := by
  unfold EndsWith at hend ⊢
  simp only [List.getLast?_map, hend, Option.map_some]

lemma even_mem_segment_reflectedActiveAmbient {n x : Nat}
    (hxSegment : x ∈ segment n) (hxEven : Even x) :
    x ∈ segment (reflectedActiveAmbient n) := by
  simp only [segment, Finset.mem_Icc] at hxSegment ⊢
  rcases reflectedActiveAmbient_eq_self_or_pred n with hN | hN
  · omega
  · rcases hxEven with ⟨k, hk⟩
    rcases reflectedActiveAmbient_even n with ⟨j, hj⟩
    omega

lemma isTheta12_reflectedActiveWord {n : Nat} {word : List Nat}
    (hn : 2 ≤ n) (hword : IsTheta12 n word) :
    IsTheta12 (reflectedActiveAmbient n) (reflectedActiveWord n word) := by
  rcases hword.2 with ⟨first, hfirst, hfirstOdd⟩
  obtain ⟨first', last, hfirst', hlast, hparity⟩ :=
    proposition_2_1_holds n word hn hword.1
  have hfirstEq : first' = first := by
    unfold StartsWith at hfirst hfirst'
    exact Option.some.inj (hfirst'.symm.trans hfirst)
  subst first'
  have hlastEven : Even last := by
    rcases Nat.even_or_odd last with hlastEven | hlastOdd
    · exact hlastEven
    · exfalso
      apply hparity
      rcases hfirstOdd with ⟨a, ha⟩
      rcases hlastOdd with ⟨b, hb⟩
      unfold Nat.ModEq
      omega
  have hlastSegment : last ∈ segment n :=
    mem_segment_of_mem_of_isTheta hword.1 (mem_of_endsWith hlast)
  have hlastCoreSegment :=
    even_mem_segment_reflectedActiveAmbient hlastSegment hlastEven
  have hlastCore : EndsWith (reflectedActiveCore n word) last := by
    apply endsWith_filter_of_true hlast
    exact decide_eq_true (Finset.mem_Icc.mp hlastCoreSegment).2
  have hdeltaStart :
      StartsWith (reflectedActiveWord n word) (activeReflection n last) := by
    have hreverseStart := startsWith_reversal_of_endsWith hlastCore
    have hcomplementStart := startsWith_complement
      (n := reflectedActiveAmbient n) hreverseStart
    simpa only [reflectedActiveWord, activeReflection] using hcomplementStart
  exact ⟨isTheta_reflectedActiveWord hword.1,
    ⟨activeReflection n last, hdeltaStart,
      (activeReflection_odd_iff_even_of_mem_segment hlastCoreSegment).2 hlastEven⟩⟩

lemma occursLeftOf_filter_of_true {p : Nat → Bool} {word : List Nat} {x y : Nat}
    (hword : word.Nodup) (hxy : OccursLeftOf word x y)
    (hx : p x = true) (hy : p y = true) :
    OccursLeftOf (word.filter p) x y := by
  have hne : x ≠ y := by
    rintro rfl
    rcases hxy with ⟨i, j, hij, hi, hj⟩
    exact (Nat.ne_of_lt hij) (getElem?_index_unique_of_nodup hword hi hj)
  induction word with
  | nil => simp [OccursLeftOf] at hxy
  | cons a tail ih =>
      have htailNodup := hword.of_cons
      by_cases ha : p a = true
      · simp only [List.filter_cons, ha, if_true]
        by_cases hax : a = x
        · subst a
          have hyMemWord : y ∈ x :: tail := by
            rcases hxy with ⟨i, j, hij, hi, hj⟩
            exact List.mem_iff_getElem?.mpr ⟨j, hj⟩
          have hyTail : y ∈ tail := by simpa [hne.symm] using hyMemWord
          have hfilteredNodup : (x :: tail.filter p).Nodup := by
            simpa only [List.filter_cons, hx, if_true] using hword.filter p
          apply occursLeftOf_of_startsWith_of_mem hfilteredNodup
          · simp [StartsWith]
          · exact List.mem_cons_of_mem x (List.mem_filter.mpr ⟨hyTail, hy⟩)
          · exact hne
        · apply (occursLeftOf_cons_iff_of_ne hax).2
          apply ih htailNodup
          exact (occursLeftOf_cons_iff_of_ne hax).1 hxy
      · have hax : a ≠ x := by
          intro h
          subst a
          exact ha hx
        simp only [List.filter_cons, ha, Bool.false_eq_true, if_false]
        apply ih htailNodup
        exact (occursLeftOf_cons_iff_of_ne hax).1 hxy

lemma reflectedActiveWord_standing {n : Nat} {gamma : List Nat}
    (hstanding : StandingInterleavingHypotheses n gamma) :
    StandingInterleavingHypotheses (reflectedActiveAmbient n)
      (reflectedActiveWord n gamma) := by
  have hn : 3 ≤ n := three_le_of_standingInterleavingHypotheses hstanding
  rcases hstanding.2 with
    ⟨b, c, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hbOdd : Odd b :=
    of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hbEnd)).2
  have hcEven : Even c :=
    of_decide_eq_true (List.mem_filter.mp (mem_of_startsWith hcStart)).2
  have hbCoreSegment : b ∈ segment (reflectedActiveAmbient n) := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hbLower ⊢
    simp only [reflectedActiveAmbient]
    omega
  have hcSegment : c ∈ segment n := by
    simp only [upperHalf, segment, Finset.mem_Icc] at hcUpper ⊢
    omega
  have hcCoreSegment : c ∈ segment (reflectedActiveAmbient n) :=
    even_mem_segment_reflectedActiveAmbient hcSegment hcEven
  have hbCoreEnd : EndsWith (oddTrace (reflectedActiveCore n gamma)) b := by
    rw [oddTrace_reflectedActiveCore]
    apply endsWith_filter_of_true hbEnd
    exact decide_eq_true (Finset.mem_Icc.mp hbCoreSegment).2
  have hdeltaOddEnd :
      EndsWith (oddTrace (reflectedActiveWord n gamma)) (activeReflection n c) := by
    rw [oddTrace_reflectedActiveWord hstanding.1.1]
    apply endsWith_map_of_endsWith
    exact endsWith_reversal_of_startsWith hcStart
  have hdeltaEvenStart :
      StartsWith (evenTrace (reflectedActiveWord n gamma)) (activeReflection n b) := by
    rw [evenTrace_reflectedActiveWord hstanding.1.1]
    apply startsWith_map_activeReflection
    exact startsWith_reversal_of_endsWith hbCoreEnd
  have hdeltaCommute :
      Commute (reflectedActiveAmbient n) (activeReflection n c) (activeReflection n b) := by
    rcases hcommute with ⟨beta, hbeta12, hcb⟩
    have hcbCore : OccursLeftOf (reflectedActiveCore n beta) c b := by
      apply occursLeftOf_filter_of_true (isTheta_nodup hbeta12.1) hcb
      · exact decide_eq_true (Finset.mem_Icc.mp hcCoreSegment).2
      · exact decide_eq_true (Finset.mem_Icc.mp hbCoreSegment).2
    have hbcReverse := occursLeftOf_reversal_of_occursLeftOf hcbCore
    have hbcMap := occursLeftOf_map (activeReflection n) hbcReverse
    refine ⟨reflectedActiveWord n beta,
      isTheta12_reflectedActiveWord (by omega) hbeta12, ?_⟩
    change OccursLeftOf
      ((reversal (reflectedActiveCore n beta)).map (activeReflection n))
      (activeReflection n b) (activeReflection n c)
    exact hbcMap
  have hcReflected := activeReflection_of_even_upper hcUpper hcEven
  have hbReflected := activeReflection_of_odd_lower hbLower hbOdd
  exact ⟨isTheta12_reflectedActiveWord (by omega) hstanding.1,
    ⟨activeReflection n c, activeReflection n b,
      hdeltaOddEnd, hdeltaEvenStart, hdeltaCommute,
      hcReflected.1, hbReflected.1⟩⟩

/-- **Theorem 2.6.** Either active end block having length at least four forces
the other to have length at most two. -/
theorem theorem_2_6_holds : theorem_2_6 := by
  intro n gamma hstanding
  dsimp only
  constructor
  · exact theorem_2_6_left hstanding
  · intro hv
    let N := reflectedActiveAmbient n
    let delta := reflectedActiveWord n gamma
    have hdeltaStanding : StandingInterleavingHypotheses N delta := by
      simpa only [N, delta] using reflectedActiveWord_standing hstanding
    have hdeltaOddFour : 4 ≤ (epilogue N (oddTrace delta)).length := by
      change 4 ≤ (oddBoundaryActiveList N delta).length
      rw [show oddBoundaryActiveList N delta = reflectedOddActiveList n gamma by
        simpa only [N, delta] using
          oddBoundaryActiveList_reflectedActiveWord hstanding.1.1]
      simpa only [reflectedOddActiveList_length] using hv
    have hdeltaEvenTwo : (prologue N (evenTrace delta)).length ≤ 2 :=
      theorem_2_6_left hdeltaStanding hdeltaOddFour
    have hmonotone := oddBoundaryActiveList_length_le_reflected_even hstanding
    change (oddBoundaryActiveList n gamma).length ≤ 2
    exact hmonotone.trans (by
      simpa only [N, delta, evenBoundaryActiveList_length] using hdeltaEvenTwo)

end LeanProofs.Sharma2012
