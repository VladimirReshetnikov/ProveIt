import LeSaulnierVijay2011.Statements
import DavisEntringerGrahamSimmons1977.Proofs

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

private lemma finiteAPFree_iff_isFiniteKAvoiding {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma 3 <->
      IsFiniteKAvoiding 3 sigma := by
  constructor
  · intro hD hHere
    apply hD
    obtain ⟨indices, hmono, a, d, hd, _, hformula⟩ := hHere
    refine ⟨indices, hmono, a, d, hd, ?_⟩
    intro i
    simpa [LeanProofs.DavisEntringerGrahamSimmons1977.finitePermutationSequence,
      finitePermutationValue] using hformula i
  · intro hHere hD
    apply hHere
    obtain ⟨indices, hmono, a, d, hd, hformula⟩ := hD
    refine ⟨indices, hmono, a, d, hd, trivial, ?_⟩
    intro i
    simpa [LeanProofs.DavisEntringerGrahamSimmons1977.finitePermutationSequence,
      finitePermutationValue] using hformula i

private theorem finite_three_avoiding_exists (n : Nat) (hn : 0 < n) :
    exists sigma : Equiv.Perm (Fin n), IsFiniteKAvoiding 3 sigma := by
  obtain ⟨sigma, hsigma⟩ :=
    LeanProofs.DavisEntringerGrahamSimmons1977.finite_ap_free_permutation_exists_holds n hn
  exact ⟨sigma, (finiteAPFree_iff_isFiniteKAvoiding sigma).mp hsigma⟩

private theorem shifted_interval_is_three_avoidable (lo len : Nat) (hlen : 0 < len) :
    IsKAvoidable 3 (Finset.Icc (lo + 1) (lo + len) : Set Nat) := by
  classical
  letI : NeZero len := ⟨hlen.ne'⟩
  obtain ⟨sigma, hsigma⟩ := finite_three_avoiding_exists len hlen
  let intervalIndex (x : Nat) : Fin len := Fin.ofNat len (x - (lo + 1))
  let rank : Nat -> Nat := fun x => (sigma.symm (intervalIndex x) : Nat)
  have index_value (x : Nat) (hx : x ∈ Finset.Icc (lo + 1) (lo + len)) :
      (intervalIndex x : Nat) = x - (lo + 1) := by
    simp only [intervalIndex, Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [Finset.mem_Icc] at hx
    omega
  refine ⟨rank, ?_, ?_⟩
  · intro x hx y hy hxy
    change x ∈ Finset.Icc (lo + 1) (lo + len) at hx
    change y ∈ Finset.Icc (lo + 1) (lo + len) at hy
    have hfin : intervalIndex x = intervalIndex y := by
      apply sigma.symm.injective
      apply Fin.ext
      exact hxy
    have hval : x - (lo + 1) = y - (lo + 1) := by
      simpa [index_value x hx, index_value y hy] using congrArg Fin.val hfin
    simp only [Finset.mem_Icc] at hx hy
    omega
  · rintro ⟨x, hxmem, hxmono, hxAP⟩
    apply hsigma
    let indices : Fin 3 -> Fin len := fun i => sigma.symm (intervalIndex (x i))
    refine ⟨indices, ?_, ?_⟩
    · intro i j hij
      change ((sigma.symm (intervalIndex (x i)) : Fin len) : Nat) <
        (sigma.symm (intervalIndex (x j)) : Nat)
      exact hxmono hij
    · obtain ⟨a, d, hd, _, hformula⟩ := hxAP
      refine ⟨a - lo, d, hd, trivial, ?_⟩
      intro i
      have hxi : x i ∈ Finset.Icc (lo + 1) (lo + len) := hxmem i
      have hindex := index_value (x i) hxi
      have hform := hformula i
      simp only [finitePermutationValue, indices, Equiv.apply_symm_apply]
      rw [hindex]
      push_cast
      simp only [Finset.mem_Icc] at hxi
      omega

private lemma compressedRank_lt_iff (s : Finset Nat) (localRank : Nat -> Nat)
    (hinj : Set.InjOn localRank (s : Set Nat)) {x y : Nat} (hx : x ∈ s) (hy : y ∈ s) :
    ((s.filter fun z => localRank z < localRank x).card <
      (s.filter fun z => localRank z < localRank y).card) <->
      localRank x < localRank y := by
  have forward {u v : Nat} (hu : u ∈ s) (hv : v ∈ s)
      (huv : localRank u < localRank v) :
      (s.filter fun z => localRank z < localRank u).card <
        (s.filter fun z => localRank z < localRank v).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, lt_trans hz.2 huv⟩
    · intro heq
      have hvMem : u ∈ s.filter fun z => localRank z < localRank v := by
        simp [hu, huv]
      rw [← heq] at hvMem
      simp at hvMem
  constructor
  · intro hcard
    by_contra huv
    have hne : localRank x ≠ localRank y := by
      intro h
      have hxy := hinj hx hy h
      subst y
      exact (lt_irrefl _ hcard)
    have hyx : localRank y < localRank x := lt_of_le_of_ne (not_lt.mp huv) hne.symm
    have := forward hy hx hyx
    omega
  · exact forward hx hy

private theorem exists_ordered_block_concatenation
    (blocks : Nat -> Finset Nat)
    (hdisjoint : forall i j : Nat, i ≠ j -> Disjoint (blocks i) (blocks j))
    (havoidable : forall i : Nat, IsKAvoidable 3 (blocks i : Set Nat)) :
    exists rank : Nat -> Nat,
      IsPermutationRanking {x | exists i : Nat, x ∈ blocks i} rank /\
      BlocksInOrder blocks rank /\
      forall i : Nat, IsKAvoidingRanking 3 (blocks i : Set Nat) rank := by
  classical
  choose localRank hlocal using havoidable
  let offsets : Nat -> Nat := fun i => (Finset.range i).sum fun j => (blocks j).card
  let compressed : Nat -> Nat -> Nat := fun i x =>
    ((blocks i).filter fun y => localRank i y < localRank i x).card
  let belongsToBlock (x : Nat) : Prop := exists i : Nat, x ∈ blocks i
  let blockIndex (x : Nat) : Nat := if hx : belongsToBlock x then Nat.find hx else 0
  have blockIndex_mem {x : Nat} (hx : belongsToBlock x) :
      x ∈ blocks (blockIndex x) := by
    simp only [blockIndex, dif_pos hx]
    exact Nat.find_spec hx
  have blockIndex_eq {x i : Nat} (hx : x ∈ blocks i) : blockIndex x = i := by
    have hbelongs : belongsToBlock x := ⟨i, hx⟩
    have hchosen := blockIndex_mem hbelongs
    by_contra hne
    have hd := hdisjoint (blockIndex x) i hne
    exact (Finset.disjoint_left.mp hd hchosen hx).elim
  have compressed_lt_card {i x : Nat} (hx : x ∈ blocks i) :
      compressed i x < (blocks i).card := by
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.mpr ⟨x, hx, lt_irrefl _⟩
  have offsets_mono : Monotone offsets := by
    intro i j hij
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  let rank : Nat -> Nat := fun x => offsets (blockIndex x) + compressed (blockIndex x) x
  have rank_on_block {i x : Nat} (hx : x ∈ blocks i) :
      rank x = offsets i + compressed i x := by
    simp [rank, blockIndex_eq hx]
  have sameOrder (i : Nat) : SameOrderOn (blocks i : Set Nat) (localRank i) rank := by
    intro x hx y hy
    rw [rank_on_block hx, rank_on_block hy, Nat.add_lt_add_iff_left]
    exact (compressedRank_lt_iff (blocks i) (localRank i) (hlocal i).1 hx hy).symm
  have blocksOrder : BlocksInOrder blocks rank := by
    intro i j hij x hx y hy
    rw [rank_on_block hx, rank_on_block hy]
    have hpos := compressed_lt_card hx
    have hprefixSucc : offsets i + (blocks i).card = offsets (i + 1) := by
      simp [offsets, Finset.sum_range_succ]
    have hprefix : offsets (i + 1) <= offsets j := offsets_mono (by omega)
    omega
  refine ⟨rank, ?_, blocksOrder, ?_⟩
  · intro x hx y hy hxy
    change belongsToBlock x at hx
    change belongsToBlock y at hy
    have hxmem := blockIndex_mem hx
    have hymem := blockIndex_mem hy
    rcases lt_trichotomy (blockIndex x) (blockIndex y) with hlt | heq | hgt
    · have := blocksOrder (blockIndex x) (blockIndex y) hlt x hxmem y hymem
      omega
    · have hsamerank : localRank (blockIndex x) x = localRank (blockIndex x) y := by
        apply le_antisymm
        · by_contra hnot
          have hlocalLt : localRank (blockIndex x) y < localRank (blockIndex x) x :=
            lt_of_not_ge hnot
          have hglobalLt := (sameOrder (blockIndex x) y (heq ▸ hymem) x hxmem).mp hlocalLt
          omega
        · by_contra hnot
          have hlocalLt : localRank (blockIndex x) x < localRank (blockIndex x) y :=
            lt_of_not_ge hnot
          have hglobalLt := (sameOrder (blockIndex x) x hxmem y (heq ▸ hymem)).mp hlocalLt
          omega
      exact (hlocal (blockIndex x)).1 hxmem (heq ▸ hymem) hsamerank
    · have := blocksOrder (blockIndex y) (blockIndex x) hgt y hymem x hxmem
      omega
  · intro i
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rcases lt_trichotomy (localRank i x) (localRank i y) with hlt | heq | hgt
      · have := (sameOrder i x hx y hy).mp hlt
        omega
      · exact (hlocal i).1 hx hy heq
      · have := (sameOrder i y hy x hx).mp hgt
        omega
    · rintro ⟨x, hxmem, hxmono, hxAP⟩
      apply (hlocal i).2
      refine ⟨x, hxmem, ?_, hxAP⟩
      intro u v huv
      exact (sameOrder i (x u) (hxmem u) (x v) (hxmem v)).mpr (hxmono huv)

private lemma q_pos (k : Nat) : 0 < q k := by
  induction k with
  | zero => simp [q]
  | succ k ih =>
      simp only [q]
      omega

private lemma p_pos (k : Nat) : 0 < p k := by
  cases k with
  | zero => simp [p]
  | succ k =>
      simp only [p]
      have := q_pos k
      omega

private lemma p_le_q (k : Nat) : p k <= q k := by
  cases k with
  | zero => norm_num [p, q]
  | succ k =>
      simp only [p, q]
      have := q_pos k
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

private lemma TBlock_is_three_avoidable (k : Nat) :
    IsKAvoidable 3 (TBlock k : Set Nat) := by
  let len := q k - p k + 1
  have hlen : 0 < len := by simp [len]
  have hav := shifted_interval_is_three_avoidable (p k - 1) len hlen
  have hlo : p k - 1 + 1 = p k := by have := p_pos k; omega
  have hhi : p k - 1 + len = q k := by
    have hpq := p_le_q k
    have hp := p_pos k
    simp only [len]
    omega
  simpa [TBlock, hlo, hhi] using hav

private lemma TBlocks_pairwise_disjoint :
    forall i j : Nat, i ≠ j -> Disjoint (TBlock i) (TBlock j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := TBlock_cross_gap_holds i j x x hij hxi hxj
    have hpos := TBlock_member_pos hxi
    omega
  · have hgap := TBlock_cross_gap_holds j i x x hji hxj hxi
    have hpos := TBlock_member_pos hxi
    omega

/-- The explicitly concatenated `T`-block construction witnesses that `T` is
3-avoidable. -/
theorem TSet_is_three_avoidable_holds : TSet_is_three_avoidable := by
  obtain ⟨rank, hrank, horder, hlocal⟩ :=
    exists_ordered_block_concatenation TBlock TBlocks_pairwise_disjoint
      TBlock_is_three_avoidable
  change IsPermutationRanking TSet rank at hrank
  exact ⟨rank, TBlock_concatenation_is_three_avoiding_holds rank hrank horder hlocal⟩

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
      _ = a ^ (2 * i + 2) := by congr 1
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

private lemma geometricBlock_is_three_avoidable (a i : Nat) (ha : 2 <= a) :
    IsKAvoidable 3 (geometricBlock a i : Set Nat) := by
  let first := a ^ (2 * i)
  let last := a ^ (2 * i + 1)
  let len := last - first + 1
  have hfirst : 0 < first := Nat.pow_pos (by omega)
  have hfirstLast : first <= last := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hlen : 0 < len := by simp [len]
  have hav := shifted_interval_is_three_avoidable (first - 1) len hlen
  have hlo : first - 1 + 1 = first := by omega
  have hhi : first - 1 + len = last := by simp only [len]; omega
  simpa [geometricBlock, first, last, hlo, hhi] using hav

private lemma geometricBlocks_pairwise_disjoint (a : Nat) (ha : 2 <= a) :
    forall i j : Nat, i ≠ j -> Disjoint (geometricBlock a i) (geometricBlock a j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := geometricBlock_cross_gap_holds a i j x x ha hij hxi hxj
    have hpos := geometricBlock_member_pos ha hxi
    omega
  · have hgap := geometricBlock_cross_gap_holds a j i x x ha hji hxj hxi
    have hpos := geometricBlock_member_pos ha hxi
    omega

/-- The explicitly concatenated geometric-block construction witnesses that
every `S^(a)` with `a >= 2` is 4-avoidable. -/
theorem geometricSet_is_four_avoidable_holds : geometricSet_is_four_avoidable := by
  intro a ha
  obtain ⟨rank, hrank, horder, hlocal⟩ :=
    exists_ordered_block_concatenation (geometricBlock a)
      (geometricBlocks_pairwise_disjoint a ha) (fun i => geometricBlock_is_three_avoidable a i ha)
  change IsPermutationRanking (geometricSet a) rank at hrank
  exact ⟨rank,
    geometricBlock_concatenation_is_four_avoiding_holds a rank ha hrank horder hlocal⟩

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

/-! ## The finite forcing argument in Theorem 2 -/

/-- The paper's forced-order argument on the eleven entries beginning `2,1`. -/
theorem theorem_2_finite_claim_holds : theorem_2_finite_claim := by
  intro sigma hfirst hsecond
  let pos : Fin 11 -> Fin 11 := sigma.symm
  have hsigma0 : sigma 0 = (1 : Fin 11) := by
    apply Fin.ext
    simp only [finitePermutationValue] at hfirst
    omega
  have hsigma1 : sigma 1 = (0 : Fin 11) := by
    apply Fin.ext
    simp only [finitePermutationValue] at hsecond
    omega
  have hpos2 : pos 1 = 0 := by simp [pos, ← hsigma0]
  have hpos1 : pos 0 = 1 := by simp [pos, ← hsigma1]
  have pos_ne {u v : Fin 11} (huv : u ≠ v) : pos u ≠ pos v := by
    exact fun h => huv (sigma.symm.injective h)
  have pos_gt_one (v : Fin 11) (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
      (1 : Fin 11) < pos v := by
    have hne0 : pos v ≠ 0 := by rw [← hpos2]; exact pos_ne hv1
    have hne1 : pos v ≠ 1 := by rw [← hpos1]; exact pos_ne hv0
    omega
  have makeAP (u v w : Fin 11) (huv : pos u < pos v) (hvw : pos v < pos w)
      (hAP : IsOddArithmeticProgression ![(u : Nat) + 1, (v : Nat) + 1,
        (w : Nat) + 1]) :
      HasOddAPSubsequence 3 (finitePermutationValue sigma) := by
    let indices : Fin 3 -> Fin 11 := ![pos u, pos v, pos w]
    refine ⟨indices, ?_, ?_⟩
    · apply (Fin.strictMono_iff_lt_succ).2
      intro i
      fin_cases i
      · simpa [indices] using huv
      · simpa [indices] using hvw
    · convert hAP using 1
      funext i
      fin_cases i <;> simp [indices, pos, finitePermutationValue]
  have hp2_lt (v : Fin 11) (hv : v ≠ 1) : pos 1 < pos v := by
    rw [hpos2]
    have := pos_ne hv
    omega
  have hp1_lt (v : Fin 11) (hv0 : v ≠ 0) (hv1 : v ≠ 1) : pos 0 < pos v := by
    rw [hpos1]
    exact pos_gt_one v hv0 hv1
  by_cases h43 : pos 3 < pos 2
  · by_cases h45 : pos 3 < pos 4
    · by_cases h74 : pos 6 < pos 3
      · by_cases h65 : pos 5 < pos 4
        · by_cases h67 : pos 5 < pos 6
          · by_cases h116 : pos 10 < pos 5
            · by_cases h811 : pos 7 < pos 10
              · by_cases h89 : pos 7 < pos 8
                · by_cases h710 : pos 6 < pos 9
                  · have h8_lt_10 : pos 7 < pos 9 := lt_trans h811 (lt_trans h116 (lt_trans h67 h710))
                    have h11_lt_10 : pos 10 < pos 9 := lt_trans h116 (lt_trans h67 h710)
                    by_cases h9_lt_10 : pos 8 < pos 9
                    · exact makeAP 7 8 9 h89 h9_lt_10 (by
                        refine ⟨8, 1, by decide, by norm_num [Odd], ?_⟩
                        intro i
                        fin_cases i <;> norm_num)
                    · have h10_lt_9 : pos 9 < pos 8 := by
                        have := pos_ne (show (9 : Fin 11) ≠ 8 by decide)
                        omega
                      exact makeAP 10 9 8 h11_lt_10 h10_lt_9 (by
                        refine ⟨11, -1, by decide, by norm_num [Odd], ?_⟩
                        intro i
                        fin_cases i <;> norm_num)
                  · have h10_lt_7 : pos 9 < pos 6 := by
                      have := pos_ne (show (9 : Fin 11) ≠ 6 by decide)
                      omega
                    exact makeAP 9 6 3 h10_lt_7 h74 (by
                      refine ⟨10, -3, by decide, by norm_num [Odd], ?_⟩
                      intro i
                      fin_cases i <;> norm_num)
                · have h9_lt_8 : pos 8 < pos 7 := by
                    have := pos_ne (show (8 : Fin 11) ≠ 7 by decide)
                    omega
                  exact makeAP 8 7 6 h9_lt_8 (lt_trans h811 (lt_trans h116 h67)) (by
                    refine ⟨9, -1, by decide, by norm_num [Odd], ?_⟩
                    intro i
                    fin_cases i <;> norm_num)
              · have h11_lt_8 : pos 10 < pos 7 := by
                  have := pos_ne (show (10 : Fin 11) ≠ 7 by decide)
                  omega
                by_cases h5_lt_8 : pos 4 < pos 7
                · exact makeAP 1 4 7 (hp2_lt 4 (by decide)) h5_lt_8 (by
                    refine ⟨2, 3, by decide, by norm_num [Odd], ?_⟩
                    intro i
                    fin_cases i <;> norm_num)
                · have h8_lt_5 : pos 7 < pos 4 := by
                    have := pos_ne (show (7 : Fin 11) ≠ 4 by decide)
                    omega
                  exact makeAP 10 7 4 h11_lt_8 h8_lt_5 (by
                    refine ⟨11, -3, by decide, by norm_num [Odd], ?_⟩
                    intro i
                    fin_cases i <;> norm_num)
            · have h6_lt_11 : pos 5 < pos 10 := by
                have := pos_ne (show (5 : Fin 11) ≠ 10 by decide)
                omega
              exact makeAP 0 5 10 (hp1_lt 5 (by decide) (by decide)) h6_lt_11 (by
                refine ⟨1, 5, by decide, by norm_num [Odd], ?_⟩
                intro i
                fin_cases i <;> norm_num)
          · have h7_lt_6 : pos 6 < pos 5 := by
              have := pos_ne (show (6 : Fin 11) ≠ 5 by decide)
              omega
            exact makeAP 6 5 4 h7_lt_6 h65 (by
              refine ⟨7, -1, by decide, by norm_num [Odd], ?_⟩
              intro i
              fin_cases i <;> norm_num)
        · have h5_lt_6 : pos 4 < pos 5 := by
            have := pos_ne (show (4 : Fin 11) ≠ 5 by decide)
            omega
          exact makeAP 3 4 5 h45 h5_lt_6 (by
            refine ⟨4, 1, by decide, by norm_num [Odd], ?_⟩
            intro i
            fin_cases i <;> norm_num)
      · have h4_lt_7 : pos 3 < pos 6 := by
          have := pos_ne (show (3 : Fin 11) ≠ 6 by decide)
          omega
        exact makeAP 0 3 6 (hp1_lt 3 (by decide) (by decide)) h4_lt_7 (by
          refine ⟨1, 3, by decide, by norm_num [Odd], ?_⟩
          intro i
          fin_cases i <;> norm_num)
    · have h5_lt_4 : pos 4 < pos 3 := by
        have := pos_ne (show (4 : Fin 11) ≠ 3 by decide)
        omega
      exact makeAP 4 3 2 h5_lt_4 h43 (by
        refine ⟨5, -1, by decide, by norm_num [Odd], ?_⟩
        intro i
        fin_cases i <;> norm_num)
  · have h3_lt_4 : pos 2 < pos 3 := by
      have := pos_ne (show (2 : Fin 11) ≠ 3 by decide)
      omega
    exact makeAP 1 2 3 (hp2_lt 2 (by decide)) h3_lt_4 (by
      refine ⟨2, 1, by decide, by norm_num [Odd], ?_⟩
      intro i
      fin_cases i <;> norm_num)

/-! ## The alternating blocks in Theorem 2 -/

/-- The geometric sum `(4^k - 1) / 3`, defined recursively so that the
divisions in the displayed block endpoints can be eliminated before doing
interval arithmetic. -/
private def fourthGeometricSum : Nat -> Nat
  | 0 => 0
  | k + 1 => 4 * fourthGeometricSum k + 1

private lemma four_pow_eq_three_mul_fourthGeometricSum_add_one (k : Nat) :
    4 ^ k = 3 * fourthGeometricSum k + 1 := by
  induction k with
  | zero => simp [fourthGeometricSum]
  | succ k ih =>
      rw [pow_succ, ih]
      simp only [fourthGeometricSum]
      ring

private lemma fourthGeometricSum_lt_succ (k : Nat) :
    fourthGeometricSum k < fourthGeometricSum (k + 1) := by
  simp only [fourthGeometricSum]
  omega

private lemma fourthGeometricSum_strictMono : StrictMono fourthGeometricSum :=
  strictMono_nat_of_lt_succ fourthGeometricSum_lt_succ

private lemma fourthGeometricSum_ge_id (k : Nat) : k <= fourthGeometricSum k := by
  induction k with
  | zero => simp [fourthGeometricSum]
  | succ k ih =>
      simp only [fourthGeometricSum]
      omega

private lemma fourthGeometricSum_eq_four_mul_pred_add_one (k : Nat) (hk : 0 < k) :
    fourthGeometricSum k = 4 * fourthGeometricSum (k - 1) + 1 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [fourthGeometricSum]

private lemma theorem2EvenBlock_succ (k : Nat) :
    theorem2EvenBlock (k + 1) =
      (Finset.Icc (4 * fourthGeometricSum k + 2)
        (16 * fourthGeometricSum k + 4)).filter Even := by
  have hpow := four_pow_eq_three_mul_fourthGeometricSum_add_one k
  have hpowOne : 4 ^ (k + 1) = 12 * fourthGeometricSum k + 4 := by
    rw [pow_succ, hpow]
    ring
  have hpowTwo : 4 ^ (k + 1 + 1) = 48 * fourthGeometricSum k + 16 := by
    rw [pow_succ, hpowOne]
    ring
  unfold theorem2EvenBlock
  rw [hpowOne, hpowTwo]
  congr 2 <;> omega

private lemma theorem2OddBlock_succ (k : Nat) :
    theorem2OddBlock (k + 1) =
      (Finset.Icc (2 * fourthGeometricSum k + 1)
        (8 * fourthGeometricSum k + 1)).filter Odd := by
  have hpow := four_pow_eq_three_mul_fourthGeometricSum_add_one k
  have hpowOne : 4 ^ (k + 1) = 12 * fourthGeometricSum k + 4 := by
    rw [pow_succ, hpow]
    ring
  have hpowTwo : 4 ^ (k + 1 + 1) = 48 * fourthGeometricSum k + 16 := by
    rw [pow_succ, hpowOne]
    ring
  unfold theorem2OddBlock
  rw [hpowOne, hpowTwo]
  congr 2 <;> omega

private lemma card_even_Icc_two_mul (lo hi : Nat) :
    ((Finset.Icc (2 * lo) (2 * hi)).filter Even).card = hi + 1 - lo := by
  have hcard :
      (Finset.Icc lo hi).card =
        ((Finset.Icc (2 * lo) (2 * hi)).filter Even).card := by
    apply Finset.card_bij (fun x _ => 2 * x)
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨by omega, even_iff_exists_two_mul.mpr ⟨x, rfl⟩⟩
    · intro x hx y hy hxy
      omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨y, rfl⟩ := even_iff_exists_two_mul.mp hx.2
      refine ⟨y, ?_, rfl⟩
      simp only [Finset.mem_Icc]
      omega
  rw [← hcard, Nat.card_Icc]

private lemma card_odd_Icc_two_mul_add_one (lo hi : Nat) :
    ((Finset.Icc (2 * lo + 1) (2 * hi + 1)).filter Odd).card = hi + 1 - lo := by
  have hcard :
      (Finset.Icc lo hi).card =
        ((Finset.Icc (2 * lo + 1) (2 * hi + 1)).filter Odd).card := by
    apply Finset.card_bij (fun x _ => 2 * x + 1)
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨by omega, odd_iff_exists_bit1.mpr ⟨x, rfl⟩⟩
    · intro x hx y hy hxy
      omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨y, rfl⟩ := odd_iff_exists_bit1.mp hx.2
      refine ⟨y, ?_, rfl⟩
      simp only [Finset.mem_Icc]
      omega
  rw [← hcard, Nat.card_Icc]

/-- The displayed even and odd blocks have the cardinalities claimed in the
paper. -/
theorem theorem_2_block_cardinalities_holds : theorem_2_block_cardinalities := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  let r := fourthGeometricSum k
  have hpow := four_pow_eq_three_mul_fourthGeometricSum_add_one k
  have heven : (theorem2EvenBlock (k + 1)).card = 6 * r + 2 := by
    rw [theorem2EvenBlock_succ]
    rw [show 4 * fourthGeometricSum k + 2 = 2 * (2 * r + 1) by simp only [r]; omega,
      show 16 * fourthGeometricSum k + 4 = 2 * (8 * r + 2) by simp only [r]; omega,
      card_even_Icc_two_mul]
    omega
  have hodd : (theorem2OddBlock (k + 1)).card = 3 * r + 1 := by
    rw [theorem2OddBlock_succ]
    rw [show 2 * fourthGeometricSum k + 1 = 2 * r + 1 by rfl,
      show 8 * fourthGeometricSum k + 1 = 2 * (4 * r) + 1 by simp only [r]; omega,
      card_odd_Icc_two_mul_add_one]
    omega
  constructor
  · rw [heven]
    have hpowTwo : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]
      norm_num [mul_comm]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hpowTwo, hpow]
    simp only [r]
    omega
  · rw [hodd, show k + 1 - 1 = k by omega, hpow]

/-- The alternating even and odd blocks cover every positive integer. -/
theorem theorem_2_blocks_cover_positive_integers_holds :
    theorem_2_blocks_cover_positive_integers := by
  intro n
  constructor
  · intro hn
    have hnpos : 0 < n := by simpa [positiveIntegers] using hn
    by_cases heven : Even n
    · let P : Nat -> Prop := fun k => n <= 16 * fourthGeometricSum k + 4
      have hexists : exists k, P k := by
        refine ⟨n, ?_⟩
        dsimp only [P]
        have := fourthGeometricSum_ge_id n
        omega
      let k := Nat.find hexists
      have hupper : n <= 16 * fourthGeometricSum k + 4 := by
        exact Nat.find_spec hexists
      have hlower : 4 * fourthGeometricSum k + 2 <= n := by
        by_cases hk : k = 0
        · rw [hk, fourthGeometricSum]
          have hnmod : n % 2 = 0 := Nat.even_iff.mp heven
          omega
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          have hminimal := Nat.find_min hexists (show k - 1 < k by omega)
          have hr := fourthGeometricSum_eq_four_mul_pred_add_one k hkpos
          dsimp only [P] at hminimal
          have hnmod : n % 2 = 0 := Nat.even_iff.mp heven
          omega
      refine ⟨k + 1, by omega, Or.inl ?_⟩
      rw [theorem2EvenBlock_succ]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hlower, hupper⟩, heven⟩
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      let P : Nat -> Prop := fun k => n <= 8 * fourthGeometricSum k + 1
      have hexists : exists k, P k := by
        refine ⟨n, ?_⟩
        dsimp only [P]
        have := fourthGeometricSum_ge_id n
        omega
      let k := Nat.find hexists
      have hupper : n <= 8 * fourthGeometricSum k + 1 := by
        exact Nat.find_spec hexists
      have hlower : 2 * fourthGeometricSum k + 1 <= n := by
        by_cases hk : k = 0
        · rw [hk, fourthGeometricSum]
          omega
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          have hminimal := Nat.find_min hexists (show k - 1 < k by omega)
          have hr := fourthGeometricSum_eq_four_mul_pred_add_one k hkpos
          dsimp only [P] at hminimal
          have hnmod : n % 2 = 1 := Nat.odd_iff.mp hodd
          omega
      refine ⟨k + 1, by omega, Or.inr ?_⟩
      rw [theorem2OddBlock_succ]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hlower, hupper⟩, hodd⟩
  · rintro ⟨i, hi, hmem | hmem⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      rw [theorem2EvenBlock_succ] at hmem
      simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
      simp only [positiveIntegers, Set.mem_Ioi]
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      rw [theorem2OddBlock_succ] at hmem
      simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
      simp only [positiveIntegers, Set.mem_Ioi]
      omega

private lemma theorem2EvenBlocks_disjoint {i j : Nat} (hi : 1 <= i) (hj : 1 <= j)
    (hij : i ≠ j) : Disjoint (theorem2EvenBlock i) (theorem2EvenBlock j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  apply Finset.disjoint_left.mpr
  intro x hxk hxl
  rw [theorem2EvenBlock_succ] at hxk hxl
  simp only [Finset.mem_filter, Finset.mem_Icc] at hxk hxl
  have hkl : k ≠ l := by
    intro h
    subst l
    simp at hij
  rcases lt_or_gt_of_ne hkl with hkl | hlk
  · have hr := fourthGeometricSum_strictMono hkl
    have hrsucc := fourthGeometricSum_strictMono.monotone (show k + 1 <= l by omega)
    simp only [fourthGeometricSum] at hrsucc
    omega
  · have hrsucc := fourthGeometricSum_strictMono.monotone (show l + 1 <= k by omega)
    simp only [fourthGeometricSum] at hrsucc
    omega

private lemma theorem2OddBlocks_disjoint {i j : Nat} (hi : 1 <= i) (hj : 1 <= j)
    (hij : i ≠ j) : Disjoint (theorem2OddBlock i) (theorem2OddBlock j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  apply Finset.disjoint_left.mpr
  intro x hxk hxl
  rw [theorem2OddBlock_succ] at hxk hxl
  simp only [Finset.mem_filter, Finset.mem_Icc] at hxk hxl
  have hkl : k ≠ l := by
    intro h
    subst l
    simp at hij
  rcases lt_or_gt_of_ne hkl with hkl | hlk
  · have hrsucc := fourthGeometricSum_strictMono.monotone (show k + 1 <= l by omega)
    simp only [fourthGeometricSum] at hrsucc
    omega
  · have hrsucc := fourthGeometricSum_strictMono.monotone (show l + 1 <= k by omega)
    simp only [fourthGeometricSum] at hrsucc
    omega

/-- The even blocks, odd blocks, and the two parity families are pairwise
disjoint. -/
theorem theorem_2_blocks_pairwise_disjoint_holds :
    theorem_2_blocks_pairwise_disjoint := by
  constructor
  · intro i j hi hj hij
    have hij' : i ≠ j := bne_iff_ne.mp hij
    exact ⟨theorem2EvenBlocks_disjoint hi hj hij',
      theorem2OddBlocks_disjoint hi hj hij'⟩
  · intro i j hi hj
    apply Finset.disjoint_left.mpr
    intro x hxe hxo
    have heven : Even x := by
      unfold theorem2EvenBlock at hxe
      exact (Finset.mem_filter.mp hxe).2
    have hodd : Odd x := by
      unfold theorem2OddBlock at hxo
      exact (Finset.mem_filter.mp hxo).2
    exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- An odd entry from an earlier odd block is less than half every even entry
of a later even block. -/
theorem theorem_2_odd_even_separation_holds : theorem_2_odd_even_separation := by
  intro i j x y hi hij hx hy
  have hj : 1 <= j := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [theorem2OddBlock_succ] at hx
  rw [theorem2EvenBlock_succ] at hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  have hrsucc := fourthGeometricSum_strictMono.monotone (show k + 1 <= l by omega)
  simp only [fourthGeometricSum] at hrsucc
  omega

private lemma theorem2EvenBlock_nonempty (i : Nat) (hi : 1 <= i) :
    (theorem2EvenBlock i).Nonempty := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [theorem2EvenBlock_succ]
  refine ⟨4 * fourthGeometricSum k + 2, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨by omega, even_iff_exists_two_mul.mpr
    ⟨2 * fourthGeometricSum k + 1, by omega⟩⟩

private lemma theorem2OddBlock_nonempty (i : Nat) (hi : 1 <= i) :
    (theorem2OddBlock i).Nonempty := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [theorem2OddBlock_succ]
  refine ⟨2 * fourthGeometricSum k + 1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨by omega, odd_iff_exists_bit1.mpr ⟨fourthGeometricSum k, rfl⟩⟩

private lemma theorem2_even_before_even (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (hi : 1 <= i) (hij : i < j)
    (hx : x ∈ theorem2EvenBlock i) (hy : y ∈ theorem2EvenBlock j) :
    rank x < rank y := by
  have core : forall j : Nat, 1 <= j -> forall i : Nat, 1 <= i -> i < j ->
      forall x, x ∈ theorem2EvenBlock i ->
        forall y, y ∈ theorem2EvenBlock j -> rank x < rank y := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hj i hi hij x hx y hy
        let m := j - 1
        have hm : 1 <= m := by simp only [m]; omega
        have hmj : m + 1 = j := by simp only [m]; omega
        obtain ⟨w, hw⟩ := theorem2OddBlock_nonempty m hm
        have hwy : rank w < rank y := by
          have := (horder m hm).2 w hw y
          rw [hmj] at this
          exact this hy
        by_cases him : i = m
        · subst i
          exact ((horder m hm).1 x hx w hw).trans hwy
        · have himlt : i < m := by simp only [m] at him ⊢; omega
          obtain ⟨z, hz⟩ := theorem2EvenBlock_nonempty m hm
          have hxz := ih m (by simp only [m]; omega) hm i hi himlt x hx z hz
          exact hxz.trans (((horder m hm).1 z hz w hw).trans hwy)
  exact core j (by omega) i hi hij x hx y hy

private lemma theorem2_even_before_odd (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (hi : 1 <= i) (hj : 1 <= j) (hij : i <= j)
    (hx : x ∈ theorem2EvenBlock i) (hy : y ∈ theorem2OddBlock j) :
    rank x < rank y := by
  rcases hij.eq_or_lt with rfl | hij
  · exact (horder i hi).1 x hx y hy
  · obtain ⟨z, hz⟩ := theorem2EvenBlock_nonempty j hj
    exact (theorem2_even_before_even rank horder hi hij hx hz).trans
      ((horder j hj).1 z hz y hy)

private lemma theorem2_odd_before_even (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (hi : 1 <= i) (hij : i < j)
    (hx : x ∈ theorem2OddBlock i) (hy : y ∈ theorem2EvenBlock j) :
    rank x < rank y := by
  by_cases hijSucc : j = i + 1
  · subst j
    exact (horder i hi).2 x hx y hy
  · have hiSucc : 1 <= i + 1 := by omega
    have hiSuccJ : i + 1 < j := by omega
    obtain ⟨z, hz⟩ := theorem2EvenBlock_nonempty (i + 1) hiSucc
    exact ((horder i hi).2 x hx z hz).trans
      (theorem2_even_before_even rank horder hiSucc hiSuccJ hz hy)

private lemma theorem2_odd_before_odd (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (hi : 1 <= i) (hj : 1 <= j) (hij : i < j)
    (hx : x ∈ theorem2OddBlock i) (hy : y ∈ theorem2OddBlock j) :
    rank x < rank y := by
  obtain ⟨z, hz⟩ := theorem2EvenBlock_nonempty j hj
  exact (theorem2_odd_before_even rank horder hi hij hx hz).trans
    ((horder j hj).1 z hz y hy)

private lemma theorem2_even_odd_index_le_of_rank_lt (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (_hi : 1 <= i) (hj : 1 <= j)
    (hx : x ∈ theorem2EvenBlock i) (hy : y ∈ theorem2OddBlock j)
    (hxy : rank x < rank y) : i <= j := by
  by_contra hij
  have hreverse := theorem2_odd_before_even rank horder hj (by omega) hy hx
  omega

private lemma theorem2_odd_even_index_lt_of_rank_lt (rank : Nat -> Nat)
    (horder : Theorem2BlocksInOrder rank) {i j x y : Nat}
    (hi : 1 <= i) (hj : 1 <= j)
    (hx : x ∈ theorem2OddBlock i) (hy : y ∈ theorem2EvenBlock j)
    (hxy : rank x < rank y) : i < j := by
  by_contra hij
  have hreverse := theorem2_even_before_odd rank horder hj hi (by omega) hy hx
  omega

private lemma odd_four_ap_parities {x : Fin 4 -> Nat}
    (hx : IsOddArithmeticProgression x) :
    (Even (x 0) /\ Odd (x 1) /\ Even (x 2) /\ Odd (x 3)) \/
      (Odd (x 0) /\ Even (x 1) /\ Odd (x 2) /\ Even (x 3)) := by
  obtain ⟨a, d, hd, hdOdd, hformula⟩ := hx
  have h0 := hformula (0 : Fin 4)
  have h1 := hformula (1 : Fin 4)
  have h2 := hformula (2 : Fin 4)
  have h3 := hformula (3 : Fin 4)
  norm_num at h0 h1 h2 h3
  have h01 : (x 1 : Int) = x 0 + d := by omega
  have h12 : (x 2 : Int) = x 1 + d := by omega
  have h23 : (x 3 : Int) = x 2 + d := by omega
  by_cases he0 : Even (x 0)
  · left
    have he0Int : Even (x 0 : Int) := (Int.even_coe_nat (x 0)).mpr he0
    have ho1Int : Odd (x 1 : Int) := by
      rw [h01]
      exact he0Int.add_odd hdOdd
    have he2Int : Even (x 2 : Int) := by
      rw [h12]
      exact ho1Int.add_odd hdOdd
    have ho3Int : Odd (x 3 : Int) := by
      rw [h23]
      exact he2Int.add_odd hdOdd
    exact ⟨he0, (Int.odd_coe_nat (x 1)).mp ho1Int,
      (Int.even_coe_nat (x 2)).mp he2Int, (Int.odd_coe_nat (x 3)).mp ho3Int⟩
  · right
    have ho0 : Odd (x 0) := Nat.not_even_iff_odd.mp he0
    have ho0Int : Odd (x 0 : Int) := (Int.odd_coe_nat (x 0)).mpr ho0
    have he1Int : Even (x 1 : Int) := by
      rw [h01]
      exact ho0Int.add_odd hdOdd
    have ho2Int : Odd (x 2 : Int) := by
      rw [h12]
      exact he1Int.add_odd hdOdd
    have he3Int : Even (x 3 : Int) := by
      rw [h23]
      exact ho2Int.add_odd hdOdd
    exact ⟨ho0, (Int.even_coe_nat (x 1)).mp he1Int,
      (Int.odd_coe_nat (x 2)).mp ho2Int, (Int.even_coe_nat (x 3)).mp he3Int⟩

private lemma positive_member_even_block {n : Nat} (hn : n ∈ positiveIntegers)
    (heven : Even n) :
    exists i : Nat, 1 <= i /\ n ∈ theorem2EvenBlock i := by
  obtain ⟨i, hi, hEven | hOdd⟩ :=
    (theorem_2_blocks_cover_positive_integers_holds n).mp hn
  · exact ⟨i, hi, hEven⟩
  · have hodd : Odd n := by
      unfold theorem2OddBlock at hOdd
      exact (Finset.mem_filter.mp hOdd).2
    exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim

private lemma positive_member_odd_block {n : Nat} (hn : n ∈ positiveIntegers)
    (hodd : Odd n) :
    exists i : Nat, 1 <= i /\ n ∈ theorem2OddBlock i := by
  obtain ⟨i, hi, hEven | hOdd⟩ :=
    (theorem_2_blocks_cover_positive_integers_holds n).mp hn
  · have heven : Even n := by
      unfold theorem2EvenBlock at hEven
      exact (Finset.mem_filter.mp hEven).2
    exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim
  · exact ⟨i, hi, hOdd⟩

/-- The alternating block concatenation contains no odd-difference four-term
arithmetic progression. -/
theorem theorem_2_block_concatenation_is_odd_four_avoiding_holds :
    theorem_2_block_concatenation_is_odd_four_avoiding := by
  intro rank hrank horder _hlocal
  refine ⟨hrank, ?_⟩
  rintro ⟨x, hxmem, hxrank, hxAP⟩
  have hr01 : rank (x 0) < rank (x 1) := hxrank (by decide)
  have hr12 : rank (x 1) < rank (x 2) := hxrank (by decide)
  have hr23 : rank (x 2) < rank (x 3) := hxrank (by decide)
  obtain ⟨a, d, hd, hdOdd, hformula⟩ := hxAP
  have hxOrdinary : IsArithmeticProgression x := ⟨a, d, hd, trivial, hformula⟩
  obtain ⟨hrel012Int, hrel123Int⟩ := four_ap_relations hxOrdinary
  have hrel012 : x 0 + x 2 = 2 * x 1 := by exact_mod_cast hrel012Int
  have hrel123 : x 1 + x 3 = 2 * x 2 := by exact_mod_cast hrel123Int
  rcases odd_four_ap_parities ⟨a, d, hd, hdOdd, hformula⟩ with
      ⟨he0, ho1, he2, ho3⟩ | ⟨ho0, he1, ho2, he3⟩
  · obtain ⟨i1, hi1, hx1⟩ := positive_member_odd_block (hxmem 1) ho1
    obtain ⟨i2, hi2, hx2⟩ := positive_member_even_block (hxmem 2) he2
    have hi12 := theorem2_odd_even_index_lt_of_rank_lt rank horder hi1 hi2 hx1 hx2 hr12
    have hgap := theorem_2_odd_even_separation_holds i1 i2 (x 1) (x 2)
      hi1 hi12 hx1 hx2
    omega
  · obtain ⟨i2, hi2, hx2⟩ := positive_member_odd_block (hxmem 2) ho2
    obtain ⟨i3, hi3, hx3⟩ := positive_member_even_block (hxmem 3) he3
    have hi23 := theorem2_odd_even_index_lt_of_rank_lt rank horder hi2 hi3 hx2 hx3 hr23
    have hgap := theorem_2_odd_even_separation_holds i2 i3 (x 2) (x 3)
      hi2 hi23 hx2 hx3
    omega

/-! ## General density facts used in the concluding obstruction -/

private lemma countingFunction_le (S : Set Nat) (n : Nat) : countingFunction S n <= n := by
  classical
  unfold countingFunction
  calc
    ((Finset.Icc 1 n).filter fun m => m ∈ S).card <= (Finset.Icc 1 n).card :=
      Finset.card_filter_le _ _
    _ = n := by simp

private lemma densityRatio_bounds (S : Set Nat) (n : Nat) :
    0 <= densityRatio S n /\ densityRatio S n <= 1 := by
  constructor
  · unfold densityRatio
    exact div_nonneg (by positivity) (by positivity)
  · by_cases hn : n = 0
    · simp [hn, densityRatio, countingFunction]
    · rw [densityRatio, div_le_one₀ (by positivity : (0 : Real) < n)]
      exact_mod_cast countingFunction_le S n

private lemma upperDensity_bounds (S : Set Nat) :
    0 <= upperDensity S /\ upperDensity S <= 1 := by
  let U : Set Real :=
    {b | exists N : Nat, forall n : Nat, N <= n -> densityRatio S n <= b}
  have hU1 : (1 : Real) ∈ U := ⟨0, fun n _ => (densityRatio_bounds S n).2⟩
  have hUnonneg : forall b, b ∈ U -> (0 : Real) <= b := by
    intro b hb
    obtain ⟨N, hN⟩ := hb
    exact (densityRatio_bounds S (max N 1)).1.trans (hN _ (le_max_left _ _))
  have hUbdd : BddBelow U := ⟨0, hUnonneg⟩
  change 0 <= sInf U /\ sInf U <= 1
  exact ⟨le_csInf ⟨1, hU1⟩ hUnonneg, csInf_le hUbdd hU1⟩

private lemma lowerDensity_bounds (S : Set Nat) :
    0 <= lowerDensity S /\ lowerDensity S <= 1 := by
  let L : Set Real :=
    {b | exists N : Nat, forall n : Nat, N <= n -> b <= densityRatio S n}
  have hL0 : (0 : Real) ∈ L := ⟨0, fun n _ => (densityRatio_bounds S n).1⟩
  have hLle : forall b, b ∈ L -> b <= (1 : Real) := by
    intro b hb
    obtain ⟨N, hN⟩ := hb
    exact (hN _ (le_max_left _ _)).trans (densityRatio_bounds S (max N 1)).2
  have hLbdd : BddAbove L := ⟨1, hLle⟩
  change 0 <= sSup L /\ sSup L <= 1
  exact ⟨le_csSup hLbdd hL0, csSup_le ⟨0, hL0⟩ hLle⟩

private lemma countingFunction_add_of_partition (A B : Set Nat)
    (hdisjoint : Disjoint A B) (hunion : A ∪ B = positiveIntegers) (n : Nat) :
    countingFunction A n + countingFunction B n = n := by
  classical
  let fA := (Finset.Icc 1 n).filter fun m => m ∈ A
  let fB := (Finset.Icc 1 n).filter fun m => m ∈ B
  have hd : Disjoint fA fB := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    simp only [fA, Finset.mem_filter] at hxA
    simp only [fB, Finset.mem_filter] at hxB
    exact Set.disjoint_left.mp hdisjoint hxA.2 hxB.2
  have hu : fA ∪ fB = Finset.Icc 1 n := by
    ext x
    simp only [fA, fB, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hxpos : x ∈ positiveIntegers := by
        simp only [Finset.mem_Icc] at hx
        simp [positiveIntegers]
        omega
      rw [← hunion] at hxpos
      rcases hxpos with hxA | hxB
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr ⟨hx, hxB⟩
  unfold countingFunction
  rw [← Finset.card_union_of_disjoint hd, hu]
  simp

private lemma lowerDensity_eq_one_sub_upperDensity_of_partition (A B : Set Nat)
    (hdisjoint : Disjoint A B) (hunion : A ∪ B = positiveIntegers) :
    lowerDensity B = 1 - upperDensity A := by
  let U : Set Real :=
    {u | exists N : Nat, forall n : Nat, N <= n -> densityRatio A n <= u}
  let L : Set Real :=
    {l | exists N : Nat, forall n : Nat, N <= n -> l <= densityRatio B n}
  have ratio_add (n : Nat) (hn : 1 <= n) :
      densityRatio A n + densityRatio B n = 1 := by
    have hcount := countingFunction_add_of_partition A B hdisjoint hunion n
    unfold densityRatio
    calc
      (countingFunction A n : Real) / n + (countingFunction B n : Real) / n =
          ((countingFunction A n + countingFunction B n : Nat) : Real) / n := by
            push_cast
            ring
      _ = (n : Real) / n := by rw [hcount]
      _ = 1 := div_self (by exact_mod_cast (show n ≠ 0 by omega))
  have hU1 : (1 : Real) ∈ U := ⟨0, fun n _ => (densityRatio_bounds A n).2⟩
  have hL0 : (0 : Real) ∈ L := ⟨0, fun n _ => (densityRatio_bounds B n).1⟩
  have hUnonneg : forall u, u ∈ U -> (0 : Real) <= u := by
    intro u hu
    obtain ⟨N, hN⟩ := hu
    exact (densityRatio_bounds A (max N 1)).1.trans (hN _ (le_max_left _ _))
  have hLle : forall l, l ∈ L -> l <= (1 : Real) := by
    intro l hl
    obtain ⟨N, hN⟩ := hl
    exact (hN _ (le_max_left _ _)).trans (densityRatio_bounds B (max N 1)).2
  have hUbdd : BddBelow U := ⟨0, hUnonneg⟩
  have hLbdd : BddAbove L := ⟨1, hLle⟩
  have mapU {u : Real} (hu : u ∈ U) : 1 - u ∈ L := by
    obtain ⟨N, hN⟩ := hu
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hnN : N <= n := le_trans (le_max_left _ _) hn
    have hn1 : 1 <= n := le_trans (le_max_right _ _) hn
    have hsum := ratio_add n hn1
    have hbound := hN n hnN
    linarith
  have mapL {l : Real} (hl : l ∈ L) : 1 - l ∈ U := by
    obtain ⟨N, hN⟩ := hl
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hnN : N <= n := le_trans (le_max_left _ _) hn
    have hn1 : 1 <= n := le_trans (le_max_right _ _) hn
    have hsum := ratio_add n hn1
    have hbound := hN n hnN
    linarith
  change sSup L = 1 - sInf U
  apply le_antisymm
  · apply csSup_le ⟨0, hL0⟩
    intro l hl
    have hinf := csInf_le hUbdd (mapL hl)
    linarith
  · have hinf : 1 - sSup L <= sInf U := by
      apply le_csInf ⟨1, hU1⟩
      intro u hu
      have hsup := le_csSup hLbdd (mapU hu)
      linarith
    linarith

/-- A two-set partition would force the sum of the two extremal densities to
be at least one, proving the paper's stated obstruction. -/
theorem alpha_beta_sum_obstructs_partition_holds : alpha_beta_sum_obstructs_partition := by
  intro hsum
  rintro ⟨A, B, hAavoid, hBavoid, hdisjoint, hunion⟩
  have hAsub : A ⊆ positiveIntegers := by
    intro x hx
    rw [← hunion]
    exact Or.inl hx
  have hBsub : B ⊆ positiveIntegers := by
    intro x hx
    rw [← hunion]
    exact Or.inr hx
  let AU : Set Real := {d | exists S : Set Nat, S ⊆ positiveIntegers /\
    IsKAvoidable 3 S /\ upperDensity S = d}
  let BL : Set Real := {d | exists S : Set Nat, S ⊆ positiveIntegers /\
    IsKAvoidable 3 S /\ lowerDensity S = d}
  have hAUbdd : BddAbove AU := by
    refine ⟨1, ?_⟩
    rintro d ⟨S, hSsub, hSavoid, rfl⟩
    exact (upperDensity_bounds S).2
  have hBLbdd : BddAbove BL := by
    refine ⟨1, ?_⟩
    rintro d ⟨S, hSsub, hSavoid, rfl⟩
    exact (lowerDensity_bounds S).2
  have hAlpha : upperDensity A <= alpha 3 := by
    change upperDensity A <= sSup AU
    exact le_csSup hAUbdd ⟨A, hAsub, hAavoid, rfl⟩
  have hBeta : lowerDensity B <= beta 3 := by
    change lowerDensity B <= sSup BL
    exact le_csSup hBLbdd ⟨B, hBsub, hBavoid, rfl⟩
  have hcomplement :=
    lowerDensity_eq_one_sub_upperDensity_of_partition A B hdisjoint hunion
  linarith

end LeanProofs.LeSaulnierVijay2011
