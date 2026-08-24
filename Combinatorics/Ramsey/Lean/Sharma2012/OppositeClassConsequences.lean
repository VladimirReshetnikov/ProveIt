import Sharma2012.CorollaryConsequences

/-!
# Opposite-orientation interleaving classes

This module reflects the upper-odd/lower-even commuting orientation to the
standing lower-odd/upper-even orientation, transfers the active end-block
bounds, and closes the globally quantified form of Corollary 2.7.1 from
Theorems 2.6 and 2.7.
-/

set_option autoImplicit false

open Finset

namespace LeanProofs.Sharma2012

lemma any_oddFixed_before_evenTrace
    {n : Nat} {gamma beta : List Nat}
    (_hgamma12 : IsTheta12 n gamma)
    (hbeta12 : IsTheta12 n beta)
    (hoddTrace : oddTrace beta = oddTrace gamma)
    (hevenTrace : evenTrace beta = evenTrace gamma) :
    ∀ x ∈ oddFixedBlock n (oddTrace gamma),
      ∀ y ∈ evenTrace gamma, OccursLeftOf beta x y := by
  intro x hx y hy
  have hyBeta : y ∈ evenTrace beta := by simpa only [hevenTrace] using hy
  have hyBetaWord : y ∈ beta := (List.mem_filter.mp hyBeta).1
  have hySegment := mem_segment_of_mem_of_isTheta hbeta12.1 hyBetaWord
  have hx' : x ∈ oddFixedBlock n (oddTrace beta) := by
    simpa only [hoddTrace] using hx
  apply fixedPrefix_before_target
    (word := beta) (trace := oddTrace beta) (y := y)
    (isTheta_nodup hbeta12.1) ((isTheta_nodup hbeta12.1).filter _)
    List.filter_sublist hySegment
  · intro z hz
    exact mem_segment_of_mem_of_isTheta hbeta12.1 (List.mem_filter.mp hz).1
  · intro z hz hsame
    have hzWord : z ∈ beta := (List.mem_filter.mp hz).1
    have hzSegment := mem_segment_of_mem_of_isTheta hbeta12.1 hzWord
    have hzOdd : Odd z := of_decide_eq_true (List.mem_filter.mp hz).2
    have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hyBeta).2
    exact (corollary_2_2_1_holds n z y hzSegment hySegment hsame).1
      hzOdd hyEven beta hbeta12
  · exact hx'

lemma reverse_evenFixed_eq_oddFixed_reverse (n : Nat) (word : List Nat) :
    (evenFixedBlock n word).reverse = oddFixedBlock n (reversal word) := by
  simp [evenFixedBlock, oddFixedBlock, epilogue, reversal]

lemma any_oddTrace_before_evenFixed
    {n : Nat} {gamma beta : List Nat}
    (_hgamma12 : IsTheta12 n gamma)
    (hbeta12 : IsTheta12 n beta)
    (hoddTrace : oddTrace beta = oddTrace gamma)
    (hevenTrace : evenTrace beta = evenTrace gamma) :
    ∀ x ∈ oddTrace gamma,
      ∀ y ∈ evenFixedBlock n (evenTrace gamma), OccursLeftOf beta x y := by
  intro x hx y hy
  have hxBeta : x ∈ oddTrace beta := by simpa only [hoddTrace] using hx
  have hxBetaWord : x ∈ beta := (List.mem_filter.mp hxBeta).1
  have hxSegment := mem_segment_of_mem_of_isTheta hbeta12.1 hxBetaWord
  have hyBeta : y ∈ evenFixedBlock n (evenTrace beta) := by
    simpa only [hevenTrace] using hy
  have hyReverseFixed : y ∈ oddFixedBlock n (reversal (evenTrace beta)) := by
    rw [← reverse_evenFixed_eq_oddFixed_reverse]
    simpa using hyBeta
  have hreverseNodup : (reversal beta).Nodup := by
    simpa [reversal] using List.nodup_reverse.mpr (isTheta_nodup hbeta12.1)
  have htraceNodup : (reversal (evenTrace beta)).Nodup := by
    simpa [reversal, evenTrace, trace] using
      List.nodup_reverse.mpr ((isTheta_nodup hbeta12.1).filter _)
  have htraceSub : List.Sublist (reversal (evenTrace beta)) (reversal beta) := by
    have h : List.Sublist (evenTrace beta) beta := by
      exact List.filter_sublist
    simpa [reversal] using h.reverse
  have hxReverse : x ∈ reversal beta := by simpa [reversal] using hxBetaWord
  have hxReverseSegment := mem_segment_of_mem_of_isTheta hbeta12.1 hxBetaWord
  have hbeforeReverse : OccursLeftOf (reversal beta) y x := by
    apply fixedPrefix_before_target
      (word := reversal beta) (trace := reversal (evenTrace beta)) (y := x)
      hreverseNodup htraceNodup htraceSub hxReverseSegment
    · intro z hz
      have hzEvenTrace : z ∈ evenTrace beta := by simpa [reversal] using hz
      exact mem_segment_of_mem_of_isTheta hbeta12.1
        (List.mem_filter.mp hzEvenTrace).1
    · intro z hz hsame
      have hzEvenTrace : z ∈ evenTrace beta := by simpa [reversal] using hz
      have hzWord : z ∈ beta := (List.mem_filter.mp hzEvenTrace).1
      have hzSegment := mem_segment_of_mem_of_isTheta hbeta12.1 hzWord
      have hxOdd : Odd x := of_decide_eq_true (List.mem_filter.mp hxBeta).2
      have hzEven : Even z := of_decide_eq_true (List.mem_filter.mp hzEvenTrace).2
      have horiginal :=
        (corollary_2_2_1_holds n x z hxSegment hzSegment
          (sameHalf_symm hsame)).1 hxOdd hzEven beta hbeta12
      exact occursLeftOf_reversal_of_occursLeftOf horiginal
    · exact hyReverseFixed
  exact occursLeftOf_of_occursLeftOf_reversal hbeforeReverse

lemma any_fixedBlocks_interleaving_decomposition
    {n : Nat} {gamma beta : List Nat}
    (hgamma12 : IsTheta12 n gamma)
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
    apply any_oddFixed_before_evenTrace hgamma12 hbeta12 hoddTrace hevenTrace x hx y
    rw [← evenActive_append_evenFixed n (evenTrace gamma)]
    exact hy
  · intro x hx y hy
    apply any_oddTrace_before_evenFixed hgamma12 hbeta12 hoddTrace hevenTrace x _ y hy
    rw [← oddFixed_append_oddActive n (oddTrace gamma)]
    exact hx

theorem any_interleavingClass_card_le_choose
    {n : Nat} {gamma : List Nat} (hgamma12 : IsTheta12 n gamma) :
    (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card ≤
      Nat.choose
        ((epilogue n (oddTrace gamma)).length +
          (prologue n (evenTrace gamma)).length)
        (prologue n (evenTrace gamma)).length := by
  classical
  let source := interleavingClass n (oddTrace gamma) (evenTrace gamma)
  let target :=
    (admissibleInterleavingWords n (oddTrace gamma) (evenTrace gamma)).toFinset
  have hle : source.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (fun sigma => permutationWord sigma)
    · intro sigma hsigma
      have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
          oddTrace (permutationWord sigma) = oddTrace gamma ∧
          evenTrace (permutationWord sigma) = evenTrace gamma := by
        simpa [source, interleavingClass] using hsigma
      obtain ⟨middle, hmiddle, hword⟩ := any_fixedBlocks_interleaving_decomposition
        hgamma12 hsigmaData.1 hsigmaData.2.1 hsigmaData.2.2
      change permutationWord sigma ∈ target
      rw [List.mem_toFinset]
      unfold admissibleInterleavingWords
      apply List.mem_map.mpr
      exact ⟨middle, hmiddle, hword.symm⟩
    · intro sigma hsigma tau htau heq
      exact permutationWord_injective heq
  calc
    (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card =
        source.card := rfl
    _ ≤ target.card := hle
    _ = (admissibleInterleavingWords n (oddTrace gamma)
          (evenTrace gamma)).length := by
      rw [List.toFinset_card_of_nodup
        (nodup_admissibleInterleavingWords hgamma12.1)]
    _ = Nat.choose
        ((epilogue n (oddTrace gamma)).length +
          (prologue n (evenTrace gamma)).length)
        (prologue n (evenTrace gamma)).length :=
      length_admissibleInterleavingWords n (oddTrace gamma) (evenTrace gamma)

def OppositeStandingInterleavingHypotheses (n : Nat) (gamma : List Nat) : Prop :=
  IsTheta12 n gamma ∧
    ∃ b c : Nat,
      EndsWith (oddTrace gamma) b ∧ StartsWith (evenTrace gamma) c ∧
      Commute n b c ∧ b ∈ upperHalf n ∧ c ∈ lowerHalf n

lemma opposite_boundary_data {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    ∃ b c : Nat,
      EndsWith (oddTrace gamma) b ∧ StartsWith (evenTrace gamma) c ∧
      b ∈ upperHalf n ∧ c ∈ lowerHalf n ∧
      2 * c ≤ b ∧ n < 2 * b - c := by
  rcases hopposite with
    ⟨hgamma12, b, c, hbEnd, hcStart, hcommute, hbUpper, hcLower⟩
  have hbTrace : b ∈ oddTrace gamma := mem_of_endsWith hbEnd
  have hcTrace : c ∈ evenTrace gamma := mem_of_startsWith hcStart
  have hbSegment := mem_segment_of_mem_of_isTheta hgamma12.1
    (List.mem_filter.mp hbTrace).1
  have hcSegment := mem_segment_of_mem_of_isTheta hgamma12.1
    (List.mem_filter.mp hcTrace).1
  have hbOdd : Odd b := of_decide_eq_true (List.mem_filter.mp hbTrace).2
  have hcEven : Even c := of_decide_eq_true (List.mem_filter.mp hcTrace).2
  have hn : 3 ≤ n := by
    rcases hcEven with ⟨k, hk⟩
    simp only [lowerHalf, Finset.mem_Icc] at hcLower
    omega
  have hnotForced : ¬ DoNotCommute n b c := by
    intro hforced
    rcases hcommute with ⟨word, hword12, hcb⟩
    exact (occursLeftOf_asymm (isTheta_nodup hword12.1)
      (hforced word hword12)) hcb
  have hnoReflections :
      ¬ ((c ≤ 2 * b ∧ 2 * b - c ∈ segment n) ∨
        (b ≤ 2 * c ∧ 2 * c - b ∈ segment n)) := by
    intro hreflections
    exact hnotForced
      ((theorem_2_2_holds n b c hn hbSegment hcSegment hbOdd hcEven).2
        hreflections)
  have hcb : 2 * c ≤ b := by
    by_contra hnot
    apply hnoReflections
    right
    constructor
    · omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hcLower hbUpper
      rcases hbOdd with ⟨j, hj⟩
      rcases hcEven with ⟨k, hk⟩
      omega
  have hreflect : n < 2 * b - c := by
    by_contra hnot
    apply hnoReflections
    left
    constructor
    · simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hcLower hbUpper
      omega
    · simp only [segment, Finset.mem_Icc]
      simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hcLower hbUpper
      omega
  exact ⟨b, c, hbEnd, hcStart, hbUpper, hcLower, hcb, hreflect⟩

lemma oddEpilogue_last_le_entry {n : Nat} {gamma : List Nat} {last x : Nat}
    (htheta : IsTheta n gamma) (hlast : EndsWith (oddTrace gamma) last)
    (hlastUpper : last ∈ upperHalf n) (hx : x ∈ epilogue n (oddTrace gamma)) :
    last ≤ x := by
  let word := reversal (oddTrace gamma)
  have hstart : StartsWith word last := startsWith_reversal_of_endsWith hlast
  have hfree : ThreeFree word := threeFree_reverse (oddTrace_threeFree htheta)
  have hxWord : x ∈ prologue n word := by simpa [word, epilogue] using hx
  have hupper : ∀ z ∈ prologue n word, z ∈ upperHalf n :=
    fun z hz => mem_upperHalf_of_mem_prologue hstart hlastUpper hz
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxWord
  obtain ⟨hiLength, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hlastBound : last ≤ n := by
    simp only [upperHalf, Finset.mem_Icc] at hlastUpper
    omega
  refine first_le_upperPrologue_entry_of_reflection_mem hfree hstart
    hlastBound hupper ?_ hiLength hi ?_
  · intro z hz hzLast hlastTwo
    have hzUpper := hupper z hz
    have hlastOdd : Odd last := by
      exact of_decide_eq_true (List.mem_filter.mp (mem_of_endsWith hlast)).2
    have hzTrace : z ∈ oddTrace gamma := by
      have hzReverse : z ∈ reversal (oddTrace gamma) :=
        (prologue_prefix n word).mem (by simpa [word] using hz)
      simpa [reversal] using hzReverse
    have hzOdd : Odd z := of_decide_eq_true (List.mem_filter.mp hzTrace).2
    have hreflectSegment : 2 * z - last ∈ segment n := by
      simp only [upperHalf, segment, Finset.mem_Icc] at hzUpper hlastUpper ⊢
      rcases hlastOdd with ⟨a, ha⟩
      rcases hzOdd with ⟨d, hd⟩
      omega
    have hreflectOdd : Odd (2 * z - last) := by
      rcases hlastOdd with ⟨a, ha⟩
      rcases hzOdd with ⟨d, hd⟩
      refine ⟨2 * d - a, ?_⟩
      omega
    have hreflectGamma := mem_of_mem_segment_of_isTheta htheta hreflectSegment
    have hreflectTrace : 2 * z - last ∈ oddTrace gamma :=
      List.mem_filter.2 ⟨hreflectGamma, decide_eq_true hreflectOdd⟩
    simpa [word, reversal] using hreflectTrace
  · have hxUpper := hupper x hxWord
    simp only [upperHalf, Finset.mem_Icc] at hxUpper hlastUpper
    omega

lemma evenPrologue_entry_le_first {n : Nat} {gamma : List Nat} {first y : Nat}
    (htheta : IsTheta n gamma) (hfirst : StartsWith (evenTrace gamma) first)
    (hfirstLower : first ∈ lowerHalf n)
    (hy : y ∈ prologue n (evenTrace gamma)) : y ≤ first := by
  have hfree := evenTrace_threeFree htheta
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨hiLength, _⟩ := List.getElem?_eq_some_iff.mp hi
  refine lowerPrologue_entry_le_first_of_reflection_mem hfree hfirst ?_
    hiLength hi
  intro z hz hfirstZ
  have hzLower := mem_lowerHalf_of_mem_prologue hfirst hfirstLower hz
  have hfirstEven : Even first := by
    exact of_decide_eq_true (List.mem_filter.mp (mem_of_startsWith hfirst)).2
  have hzTrace : z ∈ evenTrace gamma := (prologue_prefix n _).mem hz
  have hzEven : Even z := of_decide_eq_true (List.mem_filter.mp hzTrace).2
  have hreflectSegment : 2 * z - first ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hzLower hfirstLower ⊢
    rcases hfirstEven with ⟨a, ha⟩
    rcases hzEven with ⟨d, hd⟩
    omega
  have hreflectEven : Even (2 * z - first) := by
    rcases hfirstEven with ⟨a, ha⟩
    rcases hzEven with ⟨d, hd⟩
    refine ⟨2 * d - a, ?_⟩
    omega
  have hreflectGamma := mem_of_mem_segment_of_isTheta htheta hreflectSegment
  exact List.mem_filter.2 ⟨hreflectGamma, decide_eq_true hreflectEven⟩

def oddMirror (n x : Nat) : Nat :=
  2 * (((n + 1) / 2) + 1 - (x + 1) / 2) - 1

def evenMirror (n x : Nat) : Nat :=
  2 * ((n / 2) + 1 - x / 2)

lemma oddMirror_active_mem_lower_odd {n b c x : Nat}
    (hbUpper : b ∈ upperHalf n) (hcLower : c ∈ lowerHalf n)
    (hbOdd : Odd b) (hcEven : Even c)
    (hxUpper : x ∈ upperHalf n) (hxOdd : Odd x)
    (hreflect : n < 2 * b - c) (hbx : b ≤ x) :
    oddMirror n x ∈ lowerHalf n ∧ Odd (oddMirror n x) := by
  rcases hbOdd with ⟨i, hi⟩
  rcases hcEven with ⟨j, hj⟩
  rcases hxOdd with ⟨k, hk⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · simp only [upperHalf, lowerHalf, Finset.mem_Icc] at hbUpper hcLower hxUpper ⊢
    simp only [oddMirror, hm]
    constructor
    · constructor <;> omega
    · refine ⟨m - k - 1, ?_⟩
      omega
  · simp only [upperHalf, lowerHalf, Finset.mem_Icc] at hbUpper hcLower hxUpper ⊢
    simp only [oddMirror, hm]
    constructor
    · constructor <;> omega
    · refine ⟨m - k, ?_⟩
      omega

lemma evenMirror_mem_upper_even {n x : Nat}
    (hxLower : x ∈ lowerHalf n) (hxEven : Even x) :
    evenMirror n x ∈ upperHalf n ∧ Even (evenMirror n x) := by
  rcases hxEven with ⟨k, hk⟩
  simp only [lowerHalf, upperHalf, Finset.mem_Icc] at hxLower ⊢
  simp only [evenMirror]
  constructor
  · constructor <;> omega
  · exact ⟨n / 2 + 1 - k, by omega⟩

lemma mirrored_boundary_separated {n b c : Nat}
    (hbUpper : b ∈ upperHalf n) (hcLower : c ∈ lowerHalf n)
    (hbOdd : Odd b) (hcEven : Even c)
    (hcb : 2 * c ≤ b) (hreflect : n < 2 * b - c) :
    2 * oddMirror n b ≤ evenMirror n c ∧
      n < 2 * evenMirror n c - oddMirror n b := by
  rcases hbOdd with ⟨i, hi⟩
  rcases hcEven with ⟨j, hj⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · simp only [upperHalf, lowerHalf, Finset.mem_Icc] at hbUpper hcLower
    simp only [oddMirror, evenMirror, hm]
    constructor <;> omega
  · simp only [upperHalf, lowerHalf, Finset.mem_Icc] at hbUpper hcLower
    simp only [oddMirror, evenMirror, hm]
    constructor <;> omega

def mirroredOddTrace (n : Nat) (gamma : List Nat) : List Nat :=
  oddLift (complement ((n + 1) / 2) (oddBase gamma))

def mirroredEvenTrace (n : Nat) (gamma : List Nat) : List Nat :=
  evenLift (complement (n / 2) (evenBase gamma))

def mirroredDelta (n : Nat) (gamma : List Nat) : List Nat :=
  mirroredOddTrace n gamma ++ mirroredEvenTrace n gamma

lemma mirroredOddTrace_eq_map (n : Nat) (gamma : List Nat) :
    mirroredOddTrace n gamma = (oddTrace gamma).map (oddMirror n) := by
  simp [mirroredOddTrace, oddBase, oddLift, complement, oddMirror, List.map_map,
    Function.comp_def]

lemma mirroredEvenTrace_eq_map (n : Nat) (gamma : List Nat) :
    mirroredEvenTrace n gamma = (evenTrace gamma).map (evenMirror n) := by
  simp [mirroredEvenTrace, evenBase, evenLift, complement, evenMirror, List.map_map,
    Function.comp_def]

lemma oddTrace_oddLift_append_evenLift {oddWord evenWord : List Nat}
    (hpositive : ∀ x ∈ oddWord, 0 < x) :
    oddTrace (oddLift oddWord ++ evenLift evenWord) = oddLift oddWord := by
  unfold oddTrace trace
  rw [List.filter_append]
  have hoddSelf : (oddLift oddWord).filter (fun x => decide (Odd x)) =
      oddLift oddWord := by
    apply List.filter_eq_self.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    apply decide_eq_true
    refine ⟨a - 1, ?_⟩
    have haPos := hpositive a ha
    omega
  have hevenNil : (evenLift evenWord).filter (fun x => decide (Odd x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    intro hodd
    exact (Nat.not_odd_iff_even.mpr ⟨a, by omega⟩)
      (of_decide_eq_true hodd)
  rw [hoddSelf, hevenNil, List.append_nil]

lemma evenTrace_oddLift_append_evenLift {oddWord evenWord : List Nat}
    (hpositive : ∀ x ∈ oddWord, 0 < x) :
    evenTrace (oddLift oddWord ++ evenLift evenWord) = evenLift evenWord := by
  unfold evenTrace trace
  rw [List.filter_append]
  have hoddNil : (oddLift oddWord).filter (fun x => decide (Even x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    intro heven
    apply (Nat.not_even_iff_odd.mpr ?_) (of_decide_eq_true heven)
    refine ⟨a - 1, ?_⟩
    have haPos := hpositive a ha
    omega
  have hevenSelf : (evenLift evenWord).filter (fun x => decide (Even x)) =
      evenLift evenWord := by
    apply List.filter_eq_self.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact decide_eq_true ⟨a, by omega⟩
  rw [hoddNil, hevenSelf, List.nil_append]

lemma mirroredDelta_isTheta12 {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    IsTheta12 n (mirroredDelta n gamma) := by
  have hgamma := hopposite.1.1
  let oddWord := complement ((n + 1) / 2) (oddBase gamma)
  let evenWord := complement (n / 2) (evenBase gamma)
  have hodd : IsTheta ((n + 1) / 2) oddWord := by
    simpa only [oddWord] using isTheta_complement (isTheta_oddBase hgamma)
  have heven : IsTheta (n / 2) evenWord := by
    simpa only [evenWord] using isTheta_complement (isTheta_evenBase hgamma)
  have hkPos : 0 < (n + 1) / 2 := by
    rcases hopposite.2 with ⟨b, c, hbEnd, hcStart, hcommute, hbUpper, hcLower⟩
    simp only [upperHalf, Finset.mem_Icc] at hbUpper
    omega
  have htheta : IsTheta n (oddLift oddWord ++ evenLift evenWord) := by
    rcases Nat.even_or_odd n with hnEven | hnOdd
    · rcases hnEven with ⟨k, hk⟩
      have hnEq : n = 2 * (n / 2) := by omega
      have hceil : (n + 1) / 2 = n / 2 := by omega
      rw [hnEq]
      exact isTheta_oddEvenLifts_even (by simpa only [hceil] using hodd) heven
    · rcases hnOdd with ⟨k, hk⟩
      have hnEq : n = 2 * (n / 2) + 1 := by omega
      have hceil : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [hnEq]
      exact isTheta_oddEvenLifts_odd (by simpa only [hceil] using hodd) heven
  have hstarts : StartsOdd (oddLift oddWord ++ evenLift evenWord) :=
    startsOdd_oddEvenLifts hodd hkPos
  simpa [mirroredDelta, mirroredOddTrace, mirroredEvenTrace, oddWord, evenWord]
    using (show IsTheta12 n (oddLift oddWord ++ evenLift evenWord) from
      ⟨htheta, hstarts⟩)

lemma oddTrace_mirroredDelta {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    oddTrace (mirroredDelta n gamma) = mirroredOddTrace n gamma := by
  let oddWord := complement ((n + 1) / 2) (oddBase gamma)
  have hodd : IsTheta ((n + 1) / 2) oddWord := by
    simpa only [oddWord] using
      isTheta_complement (isTheta_oddBase hopposite.1.1)
  have hpositive : ∀ x ∈ oddWord, 0 < x :=
    fun x hx => positive_of_mem_of_isTheta hodd hx
  simpa [mirroredDelta, mirroredOddTrace, mirroredEvenTrace, oddWord] using
    (oddTrace_oddLift_append_evenLift
      (oddWord := oddWord)
      (evenWord := complement (n / 2) (evenBase gamma)) hpositive)

lemma evenTrace_mirroredDelta {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    evenTrace (mirroredDelta n gamma) = mirroredEvenTrace n gamma := by
  let oddWord := complement ((n + 1) / 2) (oddBase gamma)
  have hodd : IsTheta ((n + 1) / 2) oddWord := by
    simpa only [oddWord] using
      isTheta_complement (isTheta_oddBase hopposite.1.1)
  have hpositive : ∀ x ∈ oddWord, 0 < x :=
    fun x hx => positive_of_mem_of_isTheta hodd hx
  simpa [mirroredDelta, mirroredOddTrace, mirroredEvenTrace, oddWord] using
    (evenTrace_oddLift_append_evenLift
      (oddWord := oddWord)
      (evenWord := complement (n / 2) (evenBase gamma)) hpositive)

lemma endsWith_mirroredOddTrace {n : Nat} {gamma : List Nat} {b : Nat}
    (hbEnd : EndsWith (oddTrace gamma) b) :
    EndsWith (mirroredOddTrace n gamma) (oddMirror n b) := by
  rw [mirroredOddTrace_eq_map]
  simpa [EndsWith] using
    congrArg (Option.map (oddMirror n)) hbEnd

lemma startsWith_mirroredEvenTrace {n : Nat} {gamma : List Nat} {c : Nat}
    (hcStart : StartsWith (evenTrace gamma) c) :
    StartsWith (mirroredEvenTrace n gamma) (evenMirror n c) := by
  rw [mirroredEvenTrace_eq_map]
  simpa [StartsWith] using
    congrArg (Option.map (evenMirror n)) hcStart

theorem mirroredDelta_standing {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    StandingInterleavingHypotheses n (mirroredDelta n gamma) := by
  obtain ⟨b, c, hbEnd, hcStart, hbUpper, hcLower, hcb, hreflect⟩ :=
    opposite_boundary_data hopposite
  have hbTrace : b ∈ oddTrace gamma := mem_of_endsWith hbEnd
  have hcTrace : c ∈ evenTrace gamma := mem_of_startsWith hcStart
  have hbOdd : Odd b := of_decide_eq_true (List.mem_filter.mp hbTrace).2
  have hcEven : Even c := of_decide_eq_true (List.mem_filter.mp hcTrace).2
  let b' := oddMirror n b
  let c' := evenMirror n c
  have hb'Data : b' ∈ lowerHalf n ∧ Odd b' := by
    simpa only [b'] using oddMirror_active_mem_lower_odd hbUpper hcLower
      hbOdd hcEven hbUpper hbOdd hreflect (by omega)
  have hc'Data : c' ∈ upperHalf n ∧ Even c' := by
    simpa only [c'] using evenMirror_mem_upper_even hcLower hcEven
  have hsep : 2 * b' ≤ c' ∧ n < 2 * c' - b' := by
    simpa only [b', c'] using mirrored_boundary_separated hbUpper hcLower
      hbOdd hcEven hcb hreflect
  have hn : 3 ≤ n := by
    rcases hcEven with ⟨k, hk⟩
    simp only [lowerHalf, Finset.mem_Icc] at hcLower
    omega
  have hb'Segment : b' ∈ segment n := by
    simp only [lowerHalf, segment, Finset.mem_Icc] at hb'Data ⊢
    omega
  have hc'Segment : c' ∈ segment n := by
    simp only [upperHalf, segment, Finset.mem_Icc] at hc'Data ⊢
    omega
  have hnoReflections :
      ¬ ((c' ≤ 2 * b' ∧ 2 * b' - c' ∈ segment n) ∨
        (b' ≤ 2 * c' ∧ 2 * c' - b' ∈ segment n)) := by
    rintro (⟨_, hfirst⟩ | ⟨_, hsecond⟩)
    · simp only [segment, Finset.mem_Icc] at hfirst
      rcases hb'Data.2 with ⟨i, hi⟩
      rcases hc'Data.2 with ⟨j, hj⟩
      omega
    · simp only [segment, Finset.mem_Icc] at hsecond
      omega
  have hcommute : Commute n b' c' :=
    exists_theta12_reverse_pair_of_no_reflections hn hb'Segment hc'Segment
      hb'Data.2 hc'Data.2 hnoReflections
  refine ⟨mirroredDelta_isTheta12 hopposite, b', c', ?_, ?_, hcommute,
    hb'Data.1, hc'Data.1⟩
  · rw [oddTrace_mirroredDelta hopposite]
    simpa only [b'] using endsWith_mirroredOddTrace hbEnd
  · rw [evenTrace_mirroredDelta hopposite]
    simpa only [c'] using startsWith_mirroredEvenTrace hcStart

lemma prefix_length_le_prologue_of_sameHalf
    {n : Nat} {pre word : List Nat} {a : Nat}
    (hstart : StartsWith pre a) (hprefix : pre <+: word)
    (hsame : ∀ x ∈ pre, SameHalf n a x) :
    pre.length ≤ (prologue n word).length := by
  classical
  rcases hprefix with ⟨suffix, rfl⟩
  cases pre with
  | nil => simp [StartsWith] at hstart
  | cons first tail =>
      have hfirst : first = a := by simpa [StartsWith] using hstart
      subst first
      have htail : ∀ x ∈ tail, decide (SameHalf n a x) = true := by
        intro x hx
        exact decide_eq_true (hsame x (by simp [hx]))
      simp only [List.cons_append, prologue, List.length_cons]
      rw [List.takeWhile_append_of_pos htail]
      simp

lemma opposite_odd_length_le_mirrored {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    (epilogue n (oddTrace gamma)).length ≤
      (epilogue n (oddTrace (mirroredDelta n gamma))).length := by
  obtain ⟨b, c, hbEnd, hcStart, hbUpper, hcLower, hcb, hreflect⟩ :=
    opposite_boundary_data hopposite
  have hbTrace : b ∈ oddTrace gamma := mem_of_endsWith hbEnd
  have hcTrace : c ∈ evenTrace gamma := mem_of_startsWith hcStart
  have hbOdd : Odd b := of_decide_eq_true (List.mem_filter.mp hbTrace).2
  have hcEven : Even c := of_decide_eq_true (List.mem_filter.mp hcTrace).2
  let B := epilogue n (oddTrace gamma)
  let mappedB := B.map (oddMirror n)
  have hreverseStart : StartsWith (reversal (oddTrace gamma)) b :=
    startsWith_reversal_of_endsWith hbEnd
  have hBStart : StartsWith B b := by
    simpa only [B, epilogue] using startsWith_prologue_of_startsWith hreverseStart
  have hmappedStart : StartsWith mappedB (oddMirror n b) := by
    unfold StartsWith at hBStart ⊢
    simp only [mappedB, List.head?_map, hBStart, Option.map_some]
  have hBPrefix : B <+: reversal (oddTrace gamma) := by
    simpa only [B, epilogue] using prologue_prefix n (reversal (oddTrace gamma))
  have hmappedPrefix : mappedB <+: reversal (mirroredOddTrace n gamma) := by
    have h := hBPrefix.map (oddMirror n)
    simpa only [mappedB, mirroredOddTrace_eq_map, reversal, List.map_reverse] using h
  have hb'Mem : oddMirror n b ∈ lowerHalf n :=
    (oddMirror_active_mem_lower_odd hbUpper hcLower hbOdd hcEven hbUpper hbOdd
      hreflect (by omega)).1
  have hmappedSame : ∀ z ∈ mappedB, SameHalf n (oddMirror n b) z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨x, hxB, rfl⟩
    have hxPro : x ∈ prologue n (reversal (oddTrace gamma)) := by
      simpa only [B, epilogue] using hxB
    have hxUpper := mem_upperHalf_of_mem_prologue hreverseStart hbUpper hxPro
    have hxTrace : x ∈ oddTrace gamma := by
      have hxReverse := (prologue_prefix n (reversal (oddTrace gamma))).mem hxPro
      simpa [reversal] using hxReverse
    have hxOdd : Odd x := of_decide_eq_true (List.mem_filter.mp hxTrace).2
    have hbx := oddEpilogue_last_le_entry hopposite.1.1 hbEnd hbUpper
      (by simpa only [B] using hxB)
    have hxLower := (oddMirror_active_mem_lower_odd hbUpper hcLower hbOdd hcEven
      hxUpper hxOdd hreflect hbx).1
    exact Or.inl ⟨hb'Mem, hxLower⟩
  have hlength := prefix_length_le_prologue_of_sameHalf hmappedStart
    hmappedPrefix hmappedSame
  rw [oddTrace_mirroredDelta hopposite]
  simpa only [B, mappedB, List.length_map, epilogue] using hlength

lemma opposite_even_length_le_mirrored {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    (prologue n (evenTrace gamma)).length ≤
      (prologue n (evenTrace (mirroredDelta n gamma))).length := by
  obtain ⟨b, c, hbEnd, hcStart, hbUpper, hcLower, hcb, hreflect⟩ :=
    opposite_boundary_data hopposite
  have hcTrace : c ∈ evenTrace gamma := mem_of_startsWith hcStart
  have hcEven : Even c := of_decide_eq_true (List.mem_filter.mp hcTrace).2
  let C := prologue n (evenTrace gamma)
  let mappedC := C.map (evenMirror n)
  have hCStart : StartsWith C c := by
    simpa only [C] using startsWith_prologue_of_startsWith hcStart
  have hmappedStart : StartsWith mappedC (evenMirror n c) := by
    unfold StartsWith at hCStart ⊢
    simp only [mappedC, List.head?_map, hCStart, Option.map_some]
  have hCPrefix : C <+: evenTrace gamma := by
    simpa only [C] using prologue_prefix n (evenTrace gamma)
  have hmappedPrefix : mappedC <+: mirroredEvenTrace n gamma := by
    have h := hCPrefix.map (evenMirror n)
    simpa only [mappedC, mirroredEvenTrace_eq_map] using h
  have hc'Mem : evenMirror n c ∈ upperHalf n :=
    (evenMirror_mem_upper_even hcLower hcEven).1
  have hmappedSame : ∀ z ∈ mappedC, SameHalf n (evenMirror n c) z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨y, hyC, rfl⟩
    have hyPro : y ∈ prologue n (evenTrace gamma) := by
      simpa only [C] using hyC
    have hyLower := mem_lowerHalf_of_mem_prologue hcStart hcLower hyPro
    have hyTrace := (prologue_prefix n (evenTrace gamma)).mem hyPro
    have hyEven : Even y := of_decide_eq_true (List.mem_filter.mp hyTrace).2
    have hyUpper := (evenMirror_mem_upper_even hyLower hyEven).1
    exact Or.inr ⟨hc'Mem, hyUpper⟩
  have hlength := prefix_length_le_prologue_of_sameHalf hmappedStart
    hmappedPrefix hmappedSame
  rw [evenTrace_mirroredDelta hopposite]
  simpa only [C, mappedC, List.length_map] using hlength

theorem opposite_endblock_bounds
    (h26 : theorem_2_6) (h27 : theorem_2_7)
    {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    let u := (epilogue n (oddTrace gamma)).length
    let v := (prologue n (evenTrace gamma)).length
    ((4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2)) ∧
      ((5 ≤ u → v = 1) ∧ (5 ≤ v → u = 1)) := by
  dsimp only
  let delta := mirroredDelta n gamma
  let u' := (epilogue n (oddTrace delta)).length
  let v' := (prologue n (evenTrace delta)).length
  have hstanding : StandingInterleavingHypotheses n delta := by
    simpa only [delta] using mirroredDelta_standing hopposite
  have huLe : (epilogue n (oddTrace gamma)).length ≤ u' := by
    simpa only [u', delta] using opposite_odd_length_le_mirrored hopposite
  have hvLe : (prologue n (evenTrace gamma)).length ≤ v' := by
    simpa only [v', delta] using opposite_even_length_le_mirrored hopposite
  have h26' : (4 ≤ u' → v' ≤ 2) ∧ (4 ≤ v' → u' ≤ 2) := by
    simpa only [u', v'] using h26 n delta hstanding
  have h27' : (5 ≤ u' → v' = 1) ∧ (5 ≤ v' → u' = 1) := by
    simpa only [u', v'] using h27 n delta hstanding
  obtain ⟨b, c, hbEnd, hcStart, hbUpper, hcLower, hcb, hreflect⟩ :=
    opposite_boundary_data hopposite
  have huPos : 0 < (epilogue n (oddTrace gamma)).length := by
    have hstart : StartsWith (reversal (oddTrace gamma)) b :=
      startsWith_reversal_of_endsWith hbEnd
    have hbPro : b ∈ prologue n (reversal (oddTrace gamma)) :=
      mem_of_startsWith (startsWith_prologue_of_startsWith hstart)
    simpa only [epilogue] using List.length_pos_of_ne_nil (List.ne_nil_of_mem hbPro)
  have hvPos : 0 < (prologue n (evenTrace gamma)).length := by
    have hcPro : c ∈ prologue n (evenTrace gamma) :=
      mem_of_startsWith (startsWith_prologue_of_startsWith hcStart)
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem hcPro)
  constructor
  · constructor
    · intro hu
      have hv' := h26'.1 (by omega)
      omega
    · intro hv
      have hu' := h26'.2 (by omega)
      omega
  · constructor
    · intro hu
      have hv' := h27'.1 (by omega)
      omega
    · intro hv
      have hu' := h27'.2 (by omega)
      omega

theorem opposite_interleavingClass_card_le_twenty
    (h26 : theorem_2_6) (h27 : theorem_2_7)
    {n : Nat} {gamma : List Nat}
    (hopposite : OppositeStandingInterleavingHypotheses n gamma) :
    (interleavingClass n (oddTrace gamma) (evenTrace gamma)).card ≤ 20 := by
  let u := (epilogue n (oddTrace gamma)).length
  let v := (prologue n (evenTrace gamma)).length
  have hcard := any_interleavingClass_card_le_choose hopposite.1
  have hu : u ≤ 6 := by
    simpa only [u] using epilogue_oddTrace_length_le_six hopposite.1.1
  have hv : v ≤ 6 := by
    simpa only [v] using prologue_evenTrace_length_le_six hopposite.1.1
  have hbounds := opposite_endblock_bounds h26 h27 hopposite
  have h26' : (4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2) := by
    simpa only [u, v] using hbounds.1
  have h27' : (5 ≤ u → v = 1) ∧ (5 ≤ v → u = 1) := by
    simpa only [u, v] using hbounds.2
  have hchoose : Nat.choose (u + v) v ≤ 20 := by
    interval_cases u <;> interval_cases v <;>
      first | omega | norm_num [Nat.choose]
  exact hcard.trans (by simpa only [u, v] using hchoose)

theorem corollary_2_7_1_of_theorems
    (h26 : theorem_2_6) (h27 : theorem_2_7) : corollary_2_7_1 := by
  intro n gammaOdd gammaEven
  by_cases hn : 2 ≤ n
  · by_cases hempty : interleavingClass n gammaOdd gammaEven = ∅
    · simp [hempty]
    · obtain ⟨sigma, hsigma⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
          oddTrace (permutationWord sigma) = gammaOdd ∧
          evenTrace (permutationWord sigma) = gammaEven := by
        simpa [interleavingClass] using hsigma
      let gamma := permutationWord sigma
      have hgamma12 : IsTheta12 n gamma := hsigmaData.1
      have hodd : oddTrace gamma = gammaOdd := hsigmaData.2.1
      have heven : evenTrace gamma = gammaEven := hsigmaData.2.2
      have honeSegment : 1 ∈ segment n := by simp [segment]; omega
      have htwoSegment : 2 ∈ segment n := by simp [segment]; omega
      have honeGamma := mem_of_mem_segment_of_isTheta hgamma12.1 honeSegment
      have htwoGamma := mem_of_mem_segment_of_isTheta hgamma12.1 htwoSegment
      have honeTrace : 1 ∈ oddTrace gamma := by
        exact List.mem_filter.2 ⟨honeGamma, decide_eq_true (by norm_num)⟩
      have htwoTrace : 2 ∈ evenTrace gamma := by
        exact List.mem_filter.2 ⟨htwoGamma, decide_eq_true (by norm_num)⟩
      have hoddNe : oddTrace gamma ≠ [] := List.ne_nil_of_mem honeTrace
      have hevenNe : evenTrace gamma ≠ [] := List.ne_nil_of_mem htwoTrace
      let b := (oddTrace gamma).getLast hoddNe
      let c := (evenTrace gamma).head hevenNe
      have hbEnd : EndsWith (oddTrace gamma) b := by
        show (oddTrace gamma).getLast? = some b
        simpa only [b] using List.getLast?_eq_getLast_of_ne_nil hoddNe
      have hcStart : StartsWith (evenTrace gamma) c := by
        show (evenTrace gamma).head? = some c
        simpa only [c] using List.head?_eq_some_head hevenNe
      have hbTrace : b ∈ oddTrace gamma := mem_of_endsWith hbEnd
      have hcTrace : c ∈ evenTrace gamma := mem_of_startsWith hcStart
      have hbGamma : b ∈ gamma := (List.mem_filter.mp hbTrace).1
      have hcGamma : c ∈ gamma := (List.mem_filter.mp hcTrace).1
      have hbSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hbGamma
      have hcSegment := mem_segment_of_mem_of_isTheta hgamma12.1 hcGamma
      have hbOdd : Odd b := of_decide_eq_true (List.mem_filter.mp hbTrace).2
      have hcEven : Even c := of_decide_eq_true (List.mem_filter.mp hcTrace).2
      by_cases hcommute : Commute n b c
      · have hbHalves : b ∈ lowerHalf n ∨ b ∈ upperHalf n := by
          simp only [segment, lowerHalf, upperHalf, Finset.mem_Icc] at hbSegment ⊢
          omega
        have hcHalves : c ∈ lowerHalf n ∨ c ∈ upperHalf n := by
          simp only [segment, lowerHalf, upperHalf, Finset.mem_Icc] at hcSegment ⊢
          omega
        rcases hbHalves with hbLower | hbUpper <;>
          rcases hcHalves with hcLower | hcUpper
        · have hforced :=
            (corollary_2_2_1_holds n b c hbSegment hcSegment
              (Or.inl ⟨hbLower, hcLower⟩)).1 hbOdd hcEven
          rcases hcommute with ⟨word, hword12, hcb⟩
          exact False.elim ((occursLeftOf_asymm (isTheta_nodup hword12.1)
            (hforced word hword12)) hcb)
        · have hstanding : StandingInterleavingHypotheses n gamma :=
            ⟨hgamma12, b, c, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
          have hbound := standing_interleavingClass_card_le_twenty h26 h27 hstanding
          simpa only [hodd, heven] using hbound
        · have hopposite : OppositeStandingInterleavingHypotheses n gamma :=
            ⟨hgamma12, b, c, hbEnd, hcStart, hcommute, hbUpper, hcLower⟩
          have hbound := opposite_interleavingClass_card_le_twenty h26 h27 hopposite
          simpa only [hodd, heven] using hbound
        · have hforced :=
            (corollary_2_2_1_holds n b c hbSegment hcSegment
              (Or.inr ⟨hbUpper, hcUpper⟩)).1 hbOdd hcEven
          rcases hcommute with ⟨word, hword12, hcb⟩
          exact False.elim ((occursLeftOf_asymm (isTheta_nodup hword12.1)
            (hforced word hword12)) hcb)
      · have hforced : DoNotCommute n b c := by
          intro word hword12
          have hbMem := mem_of_mem_segment_of_isTheta hword12.1 hbSegment
          have hcMem := mem_of_mem_segment_of_isTheta hword12.1 hcSegment
          have hbc : b ≠ c := by
            rcases hbOdd with ⟨i, hi⟩
            rcases hcEven with ⟨j, hj⟩
            omega
          rcases occursLeftOf_total_of_mem (isTheta_nodup hword12.1)
              hbMem hcMem hbc with hleft | hright
          · exact hleft
          · exact False.elim (hcommute ⟨word, hword12, hright⟩)
        have hsingle := interleavingClass_card_le_one_of_doNotCommute
          (n := n) (gammaOdd := gammaOdd) (gammaEven := gammaEven)
          (b := b) (c := c) (by simpa only [hodd] using hbEnd)
          (by simpa only [heven] using hcStart) hforced
        omega
  · classical
    have hsubset : interleavingClass n gammaOdd gammaEven ⊆
        (Finset.univ : Finset (Equiv.Perm (Fin n))) := Finset.subset_univ _
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hcard
    interval_cases n <;> norm_num [Nat.factorial] at hcard ⊢ <;> omega

end LeanProofs.Sharma2012
