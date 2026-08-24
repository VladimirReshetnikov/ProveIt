import LeSaulnierVijay2011.Statements

/-!
# Proofs for LeSaulnier--Vijay (2011)

This file proves the established results in the statement catalogue for
Timothy D. LeSaulnier and Sujith Vijay, "On permutations avoiding arithmetic
progressions", *Discrete Mathematics* 311 (2011), 205--207.  Open questions
and conjectures are intentionally not asserted.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace LeanProofs.LeSaulnierVijay2011

/-! ## Elementary facts about rankings and the block endpoints -/

private lemma exists_rank_minimizer (S : Set Nat) (rank : Nat -> Nat)
    (hS : S.Nonempty) :
    exists x, x ∈ S /\ forall y, y ∈ S -> rank x <= rank y := by
  let R : Set Nat := rank '' S
  have hR : R.Nonempty := hS.image rank
  have hmin : sInf R ∈ R := Nat.sInf_mem hR
  obtain ⟨x, hx, hxeq⟩ := hmin
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [hxeq]
  exact Nat.sInf_le ⟨y, hy, rfl⟩

private lemma q_pos (k : Nat) : 0 < q k := by
  induction k with
  | zero => simp [q]
  | succ k ih =>
      simp only [q]
      omega

private lemma two_mul_q (k : Nat) : 2 * q k = 3 ^ (k + 1) + 1 := by
  induction k with
  | zero => norm_num [q]
  | succ k ih =>
      rw [q, Nat.pow_succ]
      have hk : 0 < q k := q_pos k
      omega

private lemma q_mono : Monotone q := by
  intro k l hkl
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
      simp only [q]
      have hl : 0 < q l := q_pos l
      omega

/-- The recursively defined endpoint has the closed form used in the paper. -/
theorem p_closed_form_holds : p_closed_form := by
  intro k hk
  cases k with
  | zero => omega
  | succ j =>
      constructor
      · change 2 * q j = 3 ^ (j + 1) + 1
        exact two_mul_q j
      · rfl

/-- Distinct `T`-blocks are separated by a factor of two. -/
theorem TBlock_cross_gap_holds : TBlock_cross_gap := by
  intro k l x y hkl hx hy
  simp only [TBlock, Finset.mem_Icc] at hx hy
  have hq_mono : q k <= q (l - 1) := by
    have hindex : k <= l - 1 := by omega
    exact q_mono hindex
  have hp : 2 * q (l - 1) = p l := by
    cases l with
    | zero => omega
    | succ m => rfl
  omega

/-- The within-block and preceding-block gaps cannot be equal. -/
theorem TBlock_same_block_gap_holds : TBlock_same_block_gap := by
  intro k l x1 x2 x3 hk hlk hx1 hx2 hx3 hx23
  simp only [TBlock, Finset.mem_Icc] at hx1 hx2 hx3
  have hq_mono : q l <= q (k - 1) := by
    have hindex : l <= k - 1 := by omega
    exact q_mono hindex
  have hp : 2 * q (k - 1) = p k := by
    cases k with
    | zero => omega
    | succ m => rfl
  have hq_rec : q k = 3 * q (k - 1) - 1 := by
    cases k with
    | zero => omega
    | succ m => rfl
  constructor <;> omega

/-! ## The basic infinite-permutation observation -/

/-- Every ranking of the positive integers contains a three-term arithmetic
progression, by the first-term/first-larger-term argument of Davis et al. -/
theorem every_permutation_of_positives_has_three_AP_holds :
    every_permutation_of_positives_has_three_AP := by
  intro rank hrank
  obtain ⟨a, ha_pos, ha_min⟩ :=
    exists_rank_minimizer positiveIntegers rank ⟨1, by simp [positiveIntegers]⟩
  let U : Set Nat := {x | a < x}
  have hU : U.Nonempty := ⟨a + 1, by simp [U]⟩
  obtain ⟨b, hb, hb_min⟩ := exists_rank_minimizer U rank hU
  have hab : a < b := hb
  let c := b + (b - a)
  have hbc : b < c := by simp [c]; omega
  have hc_pos : c ∈ positiveIntegers := by simp [positiveIntegers, c]; omega
  have hra_lt_hrb : rank a < rank b := by
    have hb_pos : b ∈ positiveIntegers := by simp [positiveIntegers]; omega
    have hr_ne : rank a ≠ rank b := fun h => hab.ne (hrank ha_pos hb_pos h)
    exact lt_of_le_of_ne (ha_min b hb_pos) hr_ne
  have hrb_lt_hrc : rank b < rank c := by
    have hb_pos : b ∈ positiveIntegers := by simp [positiveIntegers]; omega
    have hr_ne : rank b ≠ rank c := fun h => hbc.ne (hrank hb_pos hc_pos h)
    exact lt_of_le_of_ne (hb_min c (by simp [U, c]; omega)) hr_ne
  let x : Fin 3 -> Nat := ![a, b, c]
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha_pos
    · simp [x, positiveIntegers]
      omega
    · exact hc_pos
  · apply (Fin.strictMono_iff_lt_succ).2
    intro i
    fin_cases i
    · simpa [x] using hra_lt_hrb
    · simpa [x] using hrb_lt_hrc
  · refine ⟨(a : Int), (b : Int) - a, ?_, ?_, ?_⟩
    · apply bne_iff_ne.mpr
      exact sub_ne_zero.mpr (by exact_mod_cast hab.ne')
    · trivial
    · intro i
      fin_cases i
      · simp [x]
      · simp [x]
      · simp [x, c, Nat.cast_sub hab.le]
        ring

/-! ## Arithmetic-progressions across ordered blocks -/

private lemma three_ap_relation {x : Fin 3 -> Nat} (hx : IsArithmeticProgression x) :
    (x 0 : Int) + x 2 = 2 * x 1 := by
  obtain ⟨a, d, hd, _, hformula⟩ := hx
  have h0 := hformula (0 : Fin 3)
  have h1 := hformula (1 : Fin 3)
  have h2 := hformula (2 : Fin 3)
  norm_num at h0 h1 h2
  omega

private lemma four_ap_relations {x : Fin 4 -> Nat} (hx : IsArithmeticProgression x) :
    ((x 0 : Int) + x 2 = 2 * x 1) /\ ((x 1 : Int) + x 3 = 2 * x 2) := by
  obtain ⟨a, d, hd, _, hformula⟩ := hx
  have h0 := hformula (0 : Fin 4)
  have h1 := hformula (1 : Fin 4)
  have h2 := hformula (2 : Fin 4)
  have h3 := hformula (3 : Fin 4)
  norm_num at h0 h1 h2 h3
  constructor <;> omega

private lemma four_ap_tail_is_three_ap {x : Fin 4 -> Nat}
    (hx : IsArithmeticProgression x) :
    IsArithmeticProgression (fun i : Fin 3 => x ⟨i + 1, by omega⟩) := by
  obtain ⟨a, d, hd, _, hformula⟩ := hx
  refine ⟨a + d, d, hd, trivial, ?_⟩
  intro i
  rw [hformula]
  push_cast
  ring

private lemma indices_nondecreasing_of_blocks_in_order
    (blocks : Nat -> Finset Nat) (rank : Nat -> Nat)
    (hblocks : BlocksInOrder blocks rank) {i j : Nat} {x y : Nat}
    (hx : x ∈ blocks i) (hy : y ∈ blocks j) (hrank : rank x < rank y) :
    i <= j := by
  by_contra hij
  have hji : j < i := Nat.lt_of_not_ge hij
  have := hblocks j i hji y hy x hx
  omega

private lemma TBlock_member_pos {k x : Nat} (hx : x ∈ TBlock k) : 0 < x := by
  simp only [TBlock, Finset.mem_Icc] at hx
  cases k with
  | zero => simp [p] at hx; omega
  | succ k =>
      simp only [p] at hx
      have := q_pos k
      omega

/-- Concatenating arbitrary 3-avoiding orders of the `T_k` in increasing block
order gives a 3-avoiding order of their union. -/
theorem TBlock_concatenation_is_three_avoiding_holds :
    TBlock_concatenation_is_three_avoiding := by
  intro rank hrank hblocks hlocal
  refine ⟨hrank, ?_⟩
  rintro ⟨x, hxT, hxrank, hxAP⟩
  obtain ⟨k0, hk0⟩ := hxT (0 : Fin 3)
  obtain ⟨k1, hk1⟩ := hxT (1 : Fin 3)
  obtain ⟨k2, hk2⟩ := hxT (2 : Fin 3)
  have hr01 : rank (x 0) < rank (x 1) := hxrank (by decide)
  have hr12 : rank (x 1) < rank (x 2) := hxrank (by decide)
  have hk01 : k0 <= k1 :=
    indices_nondecreasing_of_blocks_in_order TBlock rank hblocks hk0 hk1 hr01
  have hk12 : k1 <= k2 :=
    indices_nondecreasing_of_blocks_in_order TBlock rank hblocks hk1 hk2 hr12
  have hrelInt := three_ap_relation hxAP
  have hrel : x 0 + x 2 = 2 * x 1 := by exact_mod_cast hrelInt
  rcases hk01.eq_or_lt with hk01eq | hk01lt
  · subst k1
    rcases hk12.eq_or_lt with hk12eq | hk12lt
    · subst k2
      have hmem : forall i, x i ∈ (TBlock k0 : Set Nat) := by
        intro i
        fin_cases i
        · exact hk0
        · exact hk1
        · exact hk2
      exact (hlocal k0).2 ⟨x, hmem, hxrank, hxAP⟩
    · have hgap := TBlock_cross_gap_holds k0 k2 (x 1) (x 2) hk12lt hk1 hk2
      have hpos := TBlock_member_pos hk0
      omega
  · have hgap01 := TBlock_cross_gap_holds k0 k1 (x 0) (x 1) hk01lt hk0 hk1
    have hx01 : x 0 < x 1 := by
      have := TBlock_member_pos hk0
      omega
    have hx12 : x 1 < x 2 := by omega
    rcases hk12.eq_or_lt with hk12eq | hk12lt
    · subst k2
      obtain ⟨hsmall, hlarge⟩ :=
        TBlock_same_block_gap_holds k1 k0 (x 0) (x 1) (x 2)
          (by omega) hk01lt hk0 hk1 hk2 hx12
      omega
    · have hgap12 := TBlock_cross_gap_holds k1 k2 (x 1) (x 2) hk12lt hk1 hk2
      have := TBlock_member_pos hk0
      omega

private lemma geometricBlock_member_pos {a i x : Nat} (ha : 2 <= a)
    (hx : x ∈ geometricBlock a i) : 0 < x := by
  simp only [geometricBlock, Finset.mem_Icc] at hx
  have hpow : 0 < a ^ (2 * i) := Nat.pow_pos (by omega)
  omega

/-- Distinct geometric blocks are separated by a factor of two. -/
theorem geometricBlock_cross_gap_holds : geometricBlock_cross_gap := by
  intro a i j x y ha hij hx hy
  simp only [geometricBlock, Finset.mem_Icc] at hx hy
  have hexp : 2 * i + 2 <= 2 * j := by omega
  have hpows : a ^ (2 * i + 2) <= a ^ (2 * j) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hdouble : 2 * a ^ (2 * i + 1) <= a ^ (2 * i + 2) := by
    calc
      2 * a ^ (2 * i + 1) <= a * a ^ (2 * i + 1) :=
        Nat.mul_le_mul_right (a ^ (2 * i + 1)) ha
      _ = a ^ ((2 * i + 1) + 1) := (Nat.pow_succ' (m := a) (n := 2 * i + 1)).symm
      _ = a ^ (2 * i + 2) := by congr 1 <;> omega
  calc
    2 * x <= 2 * a ^ (2 * i + 1) := Nat.mul_le_mul_left 2 hx.2
    _ <= a ^ (2 * i + 2) := hdouble
    _ <= a ^ (2 * j) := hpows
    _ <= y := hy.1

/-- Concatenating arbitrary 3-avoiding orders of the geometric blocks in
increasing block order gives a 4-avoiding order of their union. -/
theorem geometricBlock_concatenation_is_four_avoiding_holds :
    geometricBlock_concatenation_is_four_avoiding := by
  intro a rank ha hrank hblocks hlocal
  refine ⟨hrank, ?_⟩
  rintro ⟨x, hxS, hxrank, hxAP⟩
  obtain ⟨k0, hk0⟩ := hxS (0 : Fin 4)
  obtain ⟨k1, hk1⟩ := hxS (1 : Fin 4)
  obtain ⟨k2, hk2⟩ := hxS (2 : Fin 4)
  obtain ⟨k3, hk3⟩ := hxS (3 : Fin 4)
  have hr01 : rank (x 0) < rank (x 1) := hxrank (by decide)
  have hr12 : rank (x 1) < rank (x 2) := hxrank (by decide)
  have hr23 : rank (x 2) < rank (x 3) := hxrank (by decide)
  have hk01 : k0 <= k1 :=
    indices_nondecreasing_of_blocks_in_order (geometricBlock a) rank hblocks hk0 hk1 hr01
  have hk12 : k1 <= k2 :=
    indices_nondecreasing_of_blocks_in_order (geometricBlock a) rank hblocks hk1 hk2 hr12
  have hk23 : k2 <= k3 :=
    indices_nondecreasing_of_blocks_in_order (geometricBlock a) rank hblocks hk2 hk3 hr23
  obtain ⟨hrel012Int, hrel123Int⟩ := four_ap_relations hxAP
  have hrel012 : x 0 + x 2 = 2 * x 1 := by exact_mod_cast hrel012Int
  have hrel123 : x 1 + x 3 = 2 * x 2 := by exact_mod_cast hrel123Int
  rcases hk12.eq_or_lt with hk12eq | hk12lt
  · subst k2
    rcases hk23.eq_or_lt with hk23eq | hk23lt
    · subst k3
      let tail : Fin 3 -> Nat := fun i => x ⟨i + 1, by omega⟩
      have htailMem : forall i, tail i ∈ (geometricBlock a k1 : Set Nat) := by
        intro i
        fin_cases i <;> simp [tail, hk1, hk2, hk3]
      have htailRank : StrictMono (fun i => rank (tail i)) := by
        apply (Fin.strictMono_iff_lt_succ).2
        intro i
        fin_cases i
        · simpa [tail] using hr12
        · simpa [tail] using hr23
      exact (hlocal k1).2
        ⟨tail, htailMem, htailRank, four_ap_tail_is_three_ap hxAP⟩
    · have hgap := geometricBlock_cross_gap_holds a k1 k3 (x 2) (x 3) ha hk23lt hk2 hk3
      have := geometricBlock_member_pos ha hk1
      omega
  · have hgap := geometricBlock_cross_gap_holds a k1 k2 (x 1) (x 2) ha hk12lt hk1 hk2
    have := geometricBlock_member_pos ha hk0
    omega

/-! ## The parity concatenation -/

private lemma parity_concatenated_ranking_avoids_three
    (n : Nat) (rankEven rankOdd rank : Nat -> Nat)
    (hEven : IsKAvoidingRanking 3 (evenIntervalPart n : Set Nat) rankEven)
    (hOdd : IsKAvoidingRanking 3 (oddIntervalPart n : Set Nat) rankOdd)
    (hrank : IsPermutationRanking (Finset.Icc 1 (2 * n) : Set Nat) rank)
    (hsameEven : SameOrderOn (evenIntervalPart n : Set Nat) rankEven rank)
    (hsameOdd : SameOrderOn (oddIntervalPart n : Set Nat) rankOdd rank)
    (horder :
      (forall x, x ∈ evenIntervalPart n -> forall y, y ∈ oddIntervalPart n ->
        rank x < rank y) \/
      (forall x, x ∈ oddIntervalPart n -> forall y, y ∈ evenIntervalPart n ->
        rank x < rank y)) :
    IsKAvoidingRanking 3 (Finset.Icc 1 (2 * n) : Set Nat) rank := by
  refine ⟨hrank, ?_⟩
  rintro ⟨x, hxmem, hxmono, hxAP⟩
  have hrelInt := three_ap_relation hxAP
  have hrel : x 0 + x 2 = 2 * x 1 := by exact_mod_cast hrelInt
  have heven02 : Even (x 0) <-> Even (x 2) := by
    simp only [even_iff_two_dvd]
    omega
  have hr01 : rank (x 0) < rank (x 1) := hxmono (by decide)
  have hr12 : rank (x 1) < rank (x 2) := hxmono (by decide)
  have memEven (i : Fin 3) (hi : Even (x i)) : x i ∈ evenIntervalPart n := by
    have hiIcc := hxmem i
    change x i ∈ Finset.Icc 1 (2 * n) at hiIcc
    simp only [evenIntervalPart, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨Finset.mem_Icc.mp hiIcc, hi⟩
  have memOdd (i : Fin 3) (hi : Odd (x i)) : x i ∈ oddIntervalPart n := by
    have hiIcc := hxmem i
    change x i ∈ Finset.Icc 1 (2 * n) at hiIcc
    simp only [oddIntervalPart, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨Finset.mem_Icc.mp hiIcc, hi⟩
  by_cases he0 : Even (x 0)
  · have he2 : Even (x 2) := heven02.mp he0
    by_cases he1 : Even (x 1)
    · apply hEven.2
      refine ⟨x, ?_, ?_, hxAP⟩
      · intro i
        fin_cases i
        · exact memEven 0 he0
        · exact memEven 1 he1
        · exact memEven 2 he2
      · apply (Fin.strictMono_iff_lt_succ).2
        intro i
        fin_cases i
        · exact (hsameEven (x 0) (memEven 0 he0) (x 1) (memEven 1 he1)).mpr hr01
        · exact (hsameEven (x 1) (memEven 1 he1) (x 2) (memEven 2 he2)).mpr hr12
    · have ho1 : Odd (x 1) := Nat.not_even_iff_odd.mp he1
      rcases horder with hEO | hOE
      · have := hEO (x 2) (memEven 2 he2) (x 1) (memOdd 1 ho1)
        omega
      · have := hOE (x 1) (memOdd 1 ho1) (x 0) (memEven 0 he0)
        omega
  · have ho0 : Odd (x 0) := Nat.not_even_iff_odd.mp he0
    have ho2 : Odd (x 2) := Nat.not_even_iff_odd.mp (fun he2 => he0 (heven02.mpr he2))
    by_cases he1 : Even (x 1)
    · rcases horder with hEO | hOE
      · have := hEO (x 1) (memEven 1 he1) (x 0) (memOdd 0 ho0)
        omega
      · have := hOE (x 2) (memOdd 2 ho2) (x 1) (memEven 1 he1)
        omega
    · have ho1 : Odd (x 1) := Nat.not_even_iff_odd.mp he1
      apply hOdd.2
      refine ⟨x, ?_, ?_, hxAP⟩
      · intro i
        fin_cases i
        · exact memOdd 0 ho0
        · exact memOdd 1 ho1
        · exact memOdd 2 ho2
      · apply (Fin.strictMono_iff_lt_succ).2
        intro i
        fin_cases i
        · exact (hsameOdd (x 0) (memOdd 0 ho0) (x 1) (memOdd 1 ho1)).mpr hr01
        · exact (hsameOdd (x 1) (memOdd 1 ho1) (x 2) (memOdd 2 ho2)).mpr hr12

/-- The two parity block orders used in the counting recurrences both avoid
three-term progressions. -/
theorem parity_concatenation_is_three_avoiding_holds :
    parity_concatenation_is_three_avoiding := by
  classical
  intro n rankEven rankOdd hn hEven hOdd
  let evenMax := (evenIntervalPart n).sup rankEven
  let oddMax := (oddIntervalPart n).sup rankOdd
  let evenFirst : Nat -> Nat := fun x =>
    if Even x then rankEven x else evenMax + 1 + rankOdd x
  let oddFirst : Nat -> Nat := fun x =>
    if Odd x then rankOdd x else oddMax + 1 + rankEven x
  have fullParity (x : Nat) (hx : x ∈ Finset.Icc 1 (2 * n)) :
      Even x \/ Odd x := by
    by_cases he : Even x
    · exact Or.inl he
    · exact Or.inr (Nat.not_even_iff_odd.mp he)
  have memEvenIcc (x : Nat) (hx : x ∈ Finset.Icc 1 (2 * n)) (he : Even x) :
      x ∈ evenIntervalPart n := by
    exact Finset.mem_filter.mpr ⟨hx, he⟩
  have memOddIcc (x : Nat) (hx : x ∈ Finset.Icc 1 (2 * n)) (ho : Odd x) :
      x ∈ oddIntervalPart n := by
    exact Finset.mem_filter.mpr ⟨hx, ho⟩
  have evenFirst_rank :
      IsPermutationRanking (Finset.Icc 1 (2 * n) : Set Nat) evenFirst := by
    intro x hx y hy hxy
    change x ∈ Finset.Icc 1 (2 * n) at hx
    change y ∈ Finset.Icc 1 (2 * n) at hy
    rcases fullParity x hx with hxEven | hxOdd <;>
      rcases fullParity y hy with hyEven | hyOdd
    · simp only [evenFirst, if_pos hxEven, if_pos hyEven] at hxy
      exact hEven.1 (memEvenIcc x hx hxEven) (memEvenIcc y hy hyEven) hxy
    · simp only [evenFirst, if_pos hxEven, if_neg (Nat.not_even_iff_odd.mpr hyOdd)] at hxy
      have hxle : rankEven x <= evenMax :=
        Finset.le_sup (memEvenIcc x hx hxEven)
      omega
    · simp only [evenFirst, if_neg (Nat.not_even_iff_odd.mpr hxOdd), if_pos hyEven] at hxy
      have hyle : rankEven y <= evenMax :=
        Finset.le_sup (memEvenIcc y hy hyEven)
      omega
    · simp only [evenFirst, if_neg (Nat.not_even_iff_odd.mpr hxOdd),
        if_neg (Nat.not_even_iff_odd.mpr hyOdd)] at hxy
      have := hOdd.1 (memOddIcc x hx hxOdd) (memOddIcc y hy hyOdd)
        (by omega : rankOdd x = rankOdd y)
      exact this
  have oddFirst_rank :
      IsPermutationRanking (Finset.Icc 1 (2 * n) : Set Nat) oddFirst := by
    intro x hx y hy hxy
    change x ∈ Finset.Icc 1 (2 * n) at hx
    change y ∈ Finset.Icc 1 (2 * n) at hy
    rcases fullParity x hx with hxEven | hxOdd <;>
      rcases fullParity y hy with hyEven | hyOdd
    · simp only [oddFirst, if_neg (Nat.not_odd_iff_even.mpr hxEven),
        if_neg (Nat.not_odd_iff_even.mpr hyEven)] at hxy
      exact hEven.1 (memEvenIcc x hx hxEven) (memEvenIcc y hy hyEven) (by omega)
    · simp only [oddFirst, if_neg (Nat.not_odd_iff_even.mpr hxEven), if_pos hyOdd] at hxy
      have hyle : rankOdd y <= oddMax :=
        Finset.le_sup (memOddIcc y hy hyOdd)
      omega
    · simp only [oddFirst, if_pos hxOdd, if_neg (Nat.not_odd_iff_even.mpr hyEven)] at hxy
      have hxle : rankOdd x <= oddMax :=
        Finset.le_sup (memOddIcc x hx hxOdd)
      omega
    · simp only [oddFirst, if_pos hxOdd, if_pos hyOdd] at hxy
      exact hOdd.1 (memOddIcc x hx hxOdd) (memOddIcc y hy hyOdd) hxy
  have evenFirst_same_even :
      SameOrderOn (evenIntervalPart n : Set Nat) rankEven evenFirst := by
    intro x hx y hy
    have hxEven : Even x := (Finset.mem_filter.mp hx).2
    have hyEven : Even y := (Finset.mem_filter.mp hy).2
    simp [evenFirst, hxEven, hyEven]
  have evenFirst_same_odd :
      SameOrderOn (oddIntervalPart n : Set Nat) rankOdd evenFirst := by
    intro x hx y hy
    have hxOdd : Odd x := (Finset.mem_filter.mp hx).2
    have hyOdd : Odd y := (Finset.mem_filter.mp hy).2
    simp [evenFirst, Nat.not_even_iff_odd.mpr hxOdd,
      Nat.not_even_iff_odd.mpr hyOdd]
  have oddFirst_same_even :
      SameOrderOn (evenIntervalPart n : Set Nat) rankEven oddFirst := by
    intro x hx y hy
    have hxEven : Even x := (Finset.mem_filter.mp hx).2
    have hyEven : Even y := (Finset.mem_filter.mp hy).2
    simp [oddFirst, Nat.not_odd_iff_even.mpr hxEven,
      Nat.not_odd_iff_even.mpr hyEven]
  have oddFirst_same_odd :
      SameOrderOn (oddIntervalPart n : Set Nat) rankOdd oddFirst := by
    intro x hx y hy
    have hxOdd : Odd x := (Finset.mem_filter.mp hx).2
    have hyOdd : Odd y := (Finset.mem_filter.mp hy).2
    simp [oddFirst, hxOdd, hyOdd]
  have evenBeforeOdd : forall x, x ∈ evenIntervalPart n ->
      forall y, y ∈ oddIntervalPart n -> evenFirst x < evenFirst y := by
    intro x hx y hy
    have hxEven : Even x := (Finset.mem_filter.mp hx).2
    have hyOdd : Odd y := (Finset.mem_filter.mp hy).2
    simp only [evenFirst, if_pos hxEven, if_neg (Nat.not_even_iff_odd.mpr hyOdd)]
    have hxle : rankEven x <= evenMax := Finset.le_sup hx
    omega
  have oddBeforeEven : forall x, x ∈ oddIntervalPart n ->
      forall y, y ∈ evenIntervalPart n -> oddFirst x < oddFirst y := by
    intro x hx y hy
    have hxOdd : Odd x := (Finset.mem_filter.mp hx).2
    have hyEven : Even y := (Finset.mem_filter.mp hy).2
    simp only [oddFirst, if_pos hxOdd, if_neg (Nat.not_odd_iff_even.mpr hyEven)]
    have hxle : rankOdd x <= oddMax := Finset.le_sup hx
    omega
  refine ⟨evenFirst, oddFirst, ?_, evenFirst_same_even, evenFirst_same_odd,
    evenBeforeOdd, ?_, oddFirst_same_even, oddFirst_same_odd, oddBeforeEven⟩
  · exact parity_concatenated_ranking_avoids_three n rankEven rankOdd evenFirst
      hEven hOdd evenFirst_rank evenFirst_same_even evenFirst_same_odd (Or.inl evenBeforeOdd)
  · exact parity_concatenated_ranking_avoids_three n rankEven rankOdd oddFirst
      hEven hOdd oddFirst_rank oddFirst_same_even oddFirst_same_odd (Or.inr oddBeforeEven)

end LeanProofs.LeSaulnierVijay2011
