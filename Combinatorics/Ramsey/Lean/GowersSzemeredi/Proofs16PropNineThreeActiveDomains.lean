import GowersSzemeredi.Proofs16PropNineThree
import GowersSzemeredi.Proofs16ActiveChartGlue

/-! Proposition 9.3 retains the stronger active-domain conclusions.
This records the tests needed for completing inactive common-window values.
Window selection is still performed on good quadruples before any later
chart restriction; all numerical counts are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The same assembly, with local and quadruple tests on the actual active
index sets. The common window can subsequently be completed off those sets. -/
theorem milicevic_prop_9_3_active_domains {N : Nat} [NeZero N] [Fact N.Prime] (T : ZMod N → Finset (ZMod N))
    {d : Nat} (hT : ∀ z, (T z).card ≤ d) (L : ZMod N → ZMod N → ZMod N) {r : Real}
    (hr : 0 < r) (hr4 : r < 4) (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x))
    (hL0 : ∀ x, L x 0 = 0) {rk : Nat} (hrk : 8 * d ≤ rk) (M : Nat) [NeZero M]
    (hM : 2 ≤ r / 4 * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius rk M (r / 4)) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε ε₁ ε₂ : Real}
    (hε : 0 < ε) (hsmall : 5 * ε₁ + ε ≤ 1 / 2)
    (h1 : ((incompatibleTriples (colComp T L r)).card : Real) ≤ ε₁ * (N : Real) ^ 3)
    (h2x : ((Finset.univ.filter fun u : Fin 11 → ZMod N =>
      ¬ ColumnTupleRespected T L r (twelveXSide u)).card : Real) ≤ ε₂ * (N : Real) ^ 11)
    (h2y : ((Finset.univ.filter fun u : Fin 11 → ZMod N =>
      ¬ ColumnTupleRespected T L r (twelveYSide u)).card : Real) ≤ ε₂ * (N : Real) ^ 11) :
    ∃ (m : Nat) (θ : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
      (I : ZMod N → ZMod N → Finset Nat) (J : Finset Nat) (X : Finset (ZMod N))
      (c : ZMod N → ZMod N × ZMod N),
      J.card = 8 * s₀ ∧
      (∀ i ∈ J, i < m → FreimanHom 8 (D i) (θ i)) ∧
      (∀ a ∈ X, ∀ i ∈ chosenIndices I c a, i ∈ J ∧ i < m ∧ a ∈ D i) ∧
      (∀ a ∈ X, IsFreimanLinearOn (bohr ((chosenIndices I c a).image fun i => θ i a) η) (chosenGlued T L r c a) ∧
        chosenGlued T L r c a 0 = 0) ∧
      (∀ a ∈ X, (N : Real) / 2 ≤ (Finset.univ.filter fun z => colComp T L r (c a).1 z a).card ∧
        ∀ z, colComp T L r (c a).1 z a →
          ∀ w ∈ bohr (columnDifferenceSpectrum T (colPair (c a).1 a)) (r / 4),
            w ∈ bohr (columnDifferenceSpectrum T (colPair z a)) (r / 4) →
            chosenGlued T L r c a w = columnDifferenceMap L (colPair z a) w) ∧
      ((1 - 2 * (5 * ε₁ + ε)) ^ 3 - 2 * (5 * ε₁ + ε) - 16 * (ε + 2 * ε₂)) * (N : Real) ^ 3 -
          6 * (N : Real) ^ 2 ≤
        ((m + 8 * s₀).choose (8 * s₀) : Real) *
          ((additiveQuadruplesIn X).filter fun q => ∀ w,
            (∀ j, w ∈ bohr ((chosenIndices I c (q j)).image fun i => θ i (q j)) η) →
            chosenGlued T L r c (q 0) w + chosenGlued T L r c (q 1) w =
              chosenGlued T L r c (q 2) w + chosenGlued T L r c (q 3) w).card ∧
      ⌈min (claimNineFourDensity ε (propNineThreeRadius rk M (r / 4)) d)
          (claimNineFiveDensity ε (propNineThreeRadius rk M (r / 4)) d) * (N : Real) ^ 2⌉₊ * m ≤
        N * N * s₀ := by
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- 1. the iteration
  obtain ⟨m, θ, D, I, hinv, hb4, hb12, hm⟩ := milicevic_prop_9_3_iteration T hT hrk M
    (by positivity : 0 < r / 4) (by linarith : r / 4 < 1) hM hs₀ hη0 hη hε
  set Comp := colComp T L r with hComp
  set Bad4 := propNineThreeBad T (r / 4) η θ I with hBad4
  set η' := 5 * ε₁ + ε with hη'
  -- 2. good pairs and the Markov set
  have hsum := good_pair_fibers_sum_ge Comp Bad4 h1 hb4
  have hGle : ∀ a, ((goodPairs Comp Bad4 a).card : Real) ≤ (N : Real) ^ 2 := by
    intro a
    have := Finset.card_le_univ (goodPairs Comp Bad4 a)
    rw [Fintype.card_prod, ZMod.card] at this
    have h' : ((goodPairs Comp Bad4 a).card : Real) ≤ ((N * N : Nat) : Real) := by
      exact_mod_cast this
    simpa [sq] using h'
  have hA' := markov_large_fibers (fun a => (goodPairs Comp Bad4 a).card) (M := (N : Real) ^ 2)
    (by positivity) hGle hsum
  set A' := Finset.univ.filter fun a : ZMod N =>
    (N : Real) ^ 2 / 2 ≤ ((goodPairs Comp Bad4 a).card : Real) with hA'def
  have hA'mem : ∀ a ∈ A', (N : Real) ^ 2 / 2 ≤ ((goodPairs Comp Bad4 a).card : Real) :=
    fun a ha => (Finset.mem_filter.mp ha).2
  -- 3. the pair choice
  let F : ZMod N → Finset (ZMod N × ZMod N) := fun a =>
    if a ∈ A' then goodPairs Comp Bad4 a else {(0, 0)}
  have hF : ∀ a, (F a).Nonempty := by
    intro a
    by_cases ha : a ∈ A'
    · simp only [F, if_pos ha]
      apply Finset.card_pos.mp
      have := hA'mem a ha
      have h0 : (0 : Real) < ((goodPairs Comp Bad4 a).card : Real) := by
        have : (0 : Real) < (N : Real) ^ 2 / 2 := by positivity
        linarith
      exact_mod_cast h0
    · simp only [F, if_neg ha]
      exact Finset.singleton_nonempty _
  have hFA : ∀ a ∈ A', F a = goodPairs Comp Bad4 a := fun a ha => by simp only [F, if_pos ha]
  let Q := (additiveQuadruplesIn A').filter fun q => Function.Injective q
  have hQmem : ∀ q ∈ Q, q 0 + q 1 = q 2 + q 3 ∧ ∀ j, q j ∈ A' := fun q hq =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hprod : ∀ q ∈ Q, ((N : Real) ^ 2 / 2) ^ 4 ≤
      ((∏ j : Fin 4, (F (q j)).card : Nat) : Real) := by
    intro q hq
    push_cast
    calc ((N : Real) ^ 2 / 2) ^ 4 = ∏ _j : Fin 4, (N : Real) ^ 2 / 2 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin 4, ((F (q j)).card : Real) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro j _
          rw [hFA _ ((hQmem q hq).2 j)]
          exact hA'mem _ ((hQmem q hq).2 j)
  set UX := Finset.univ.filter fun u : Fin 11 → ZMod N =>
    ¬ ColumnTupleRespected T L r (twelveXSide u) with hUX
  set UY := Finset.univ.filter fun u : Fin 11 → ZMod N =>
    ¬ ColumnTupleRespected T L r (twelveYSide u) with hUY
  set Bad := propNineThreeBad12 T (r / 4) η θ I ∪ UX ∪ UY with hBad
  have hBadcard : (Bad.card : Real) ≤ (ε + 2 * ε₂) * (N : Real) ^ 11 := by
    have h : Bad.card ≤ (propNineThreeBad12 T (r / 4) η θ I).card + UX.card + UY.card := by
      calc Bad.card ≤ (propNineThreeBad12 T (r / 4) η θ I ∪ UX).card + UY.card :=
            Finset.card_union_le _ _
        _ ≤ _ := by gcongr; exact Finset.card_union_le _ _
    have h' : (Bad.card : Real) ≤ (propNineThreeBad12 T (r / 4) η θ I).card + UX.card + UY.card := by
      exact_mod_cast h
    linarith
  obtain ⟨c, hcF, hfail⟩ := exists_pair_choice_few_bad F hF Q
    (fun q hq => (Finset.mem_filter.mp hq).2) (fun q hq => (hQmem q hq).1) Bad
    (by positivity) hprod
  have hcgood : ∀ a ∈ A', ((c a).1, (c a).2, a) ∈ goodTriples Comp Bad4 := by
    intro a ha
    have := hcF a
    rw [hFA a ha] at this
    exact (Finset.mem_filter.mp this).2
  have hfail' : ((Q.filter fun q => twelveOf q (fun j => c (q j)) ∈ Bad).card : Real) ≤
      16 * (ε + 2 * ε₂) * (N : Real) ^ 3 := by
    refine hfail.trans ?_
    rw [div_le_iff₀ (by positivity)]
    calc (Bad.card : Real) ≤ (ε + 2 * ε₂) * (N : Real) ^ 11 := hBadcard
      _ = 16 * (ε + 2 * ε₂) * (N : Real) ^ 3 * ((N : Real) ^ 2 / 2) ^ 4 := by ring
  set Qr := Q.filter fun q => twelveOf q (fun j => c (q j)) ∉ Bad with hQr
  have hQr : (Q.card : Real) - 16 * (ε + 2 * ε₂) * (N : Real) ^ 3 ≤ Qr.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Q)
      (fun q => twelveOf q (fun j => c (q j)) ∈ Bad)
    have h' : ((Q.filter fun q => twelveOf q (fun j => c (q j)) ∈ Bad).card : Real) +
        Qr.card = Q.card := by exact_mod_cast h
    linarith
  have hQcard : ((additiveQuadruplesIn A').card : Real) - 6 * (N : Real) ^ 2 ≤ Q.card := by
    have h := Finset.card_filter_add_card_filter_not (s := additiveQuadruplesIn A')
      (fun q => Function.Injective q)
    have hrep := additiveQuadruplesIn_repeated_card_le A'
    have h' : (Q.card : Real) + ((additiveQuadruplesIn A').filter fun q =>
        ¬ Function.Injective q).card = (additiveQuadruplesIn A').card := by exact_mod_cast h
    have hrep' : (((additiveQuadruplesIn A').filter fun q =>
        ¬ Function.Injective q).card : Real) ≤ 6 * (N : Real) ^ 2 := by exact_mod_cast hrep
    linarith
  have hdense := dense_additive_quadruples_ge A'
  -- 4. the window, chosen for quadruples
  have hcap := propNineThree_index_card_le T hT hs₀ hinv
  set S := chosenIndices I c with hS
  have hSprop : ∀ a, S a ⊆ Finset.range (m + 8 * s₀) ∧ (S a).card ≤ 2 * s₀ := by
    intro a
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Finset.mem_union.mp hi with h | h
      · exact Finset.range_mono (by omega) ((hinv.2 _ a).1 h)
      · exact Finset.range_mono (by omega) ((hinv.2 _ a).1 h)
    · refine (Finset.card_union_le _ _).trans ?_
      have := hcap (c a).1 a
      have := hcap (c a).2 a
      omega
  obtain ⟨J, -, hJcard, hwin⟩ := exists_quadruple_window Qr S (m := m + 8 * s₀) (k := 2 * s₀)
    (by omega) hSprop
  rw [show 4 * (2 * s₀) = 8 * s₀ by ring] at hJcard hwin
  set X := A'.filter fun a => S a ⊆ J with hX
  have hXA : ∀ a ∈ X, a ∈ A' ∧ S a ⊆ J := fun a ha => Finset.mem_filter.mp ha
  refine ⟨m, θ, D, I, J, X, c, hJcard, fun i _ hi => hinv.1 i hi, ?_, ?_, ?_, ?_, hm⟩
  · -- indices used by `a`
    intro a ha i hi
    obtain ⟨-, hSJ⟩ := hXA a ha
    refine ⟨hSJ hi, ?_⟩
    rcases Finset.mem_union.mp hi with h | h
    · exact ⟨Finset.mem_range.mp ((hinv.2 _ a).1 h), ((hinv.2 _ a).2.1 i h).1⟩
    · exact ⟨Finset.mem_range.mp ((hinv.2 _ a).1 h), ((hinv.2 _ a).2.1 i h).1⟩
  · -- the glued maps on the window Bohr sets
    intro a ha
    obtain ⟨haA, hSJ⟩ := hXA a ha
    obtain ⟨hcomp, hnb, -, -⟩ := (Finset.mem_filter.mp (hcgood a haA)).2
    obtain ⟨hFre, h0, -, -⟩ := gluedPairMap_spec T L hr.le hL hL0 hcomp
    have hdom := good_pair_domain T θ I hnb (Finset.Subset.refl (chosenIndices I c a))
    refine ⟨fun y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ he => hFre y₁ y₂ y₃ y₄ (hdom h₁) (hdom h₂) (hdom h₃)
      (hdom h₄) he, h0⟩
  · -- relating back
    intro a ha
    obtain ⟨haA, -⟩ := hXA a ha
    obtain ⟨hcomp, -, hwc, -⟩ := (Finset.mem_filter.mp (hcgood a haA)).2
    refine ⟨(Finset.mem_filter.mp hwc).2, fun z hz w hw hwz => ?_⟩
    exact gluedPairMap_relate T L hr.le hL hL0 hcomp hz hw hwz
  · -- the respected quadruples
    have hsub : (Qr.filter fun q => ∀ j, S (q j) ⊆ J) ⊆
        (additiveQuadruplesIn X).filter fun q => ∀ w,
          (∀ j, w ∈ bohr ((chosenIndices I c (q j)).image fun i => θ i (q j)) η) →
          chosenGlued T L r c (q 0) w + chosenGlued T L r c (q 1) w =
            chosenGlued T L r c (q 2) w + chosenGlued T L r c (q 3) w := by
      intro q hq
      obtain ⟨hqr, hqJ⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqQ, hqbad⟩ := Finset.mem_filter.mp hqr
      obtain ⟨hadd, hqA⟩ := hQmem q hqQ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadd,
        fun j => Finset.mem_filter.mpr ⟨hqA j, hqJ j⟩⟩, fun w hw => ?_⟩
      have hcompat : ∀ j, ColumnPairCompatible T L r (colPair (c (q j)).1 (q j))
          (colPair (c (q j)).2 (q j)) := fun j =>
        (Finset.mem_filter.mp (hcgood _ (hqA j))).2.1
      have hn12 : twelveOf q (fun j => c (q j)) ∉ propNineThreeBad12 T (r / 4) η θ I :=
        fun h => hqbad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hrx : ColumnTupleRespected T L r (twelveXSide (twelveOf q (fun j => c (q j)))) := by
        by_contra h
        exact hqbad (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
      have hry : ColumnTupleRespected T L r (twelveYSide (twelveOf q (fun j => c (q j)))) := by
        by_contra h
        exact hqbad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      exact twelve_good_respected_active T L hr.le hL hL0 θ I c q hadd hcompat hn12 hrx hry hw
    have hcount := (Finset.card_le_card hsub)
    have hwin' : (Qr.card : Real) ≤ ((m + 8 * s₀).choose (8 * s₀) : Real) *
        ((Qr.filter fun q => ∀ j, S (q j) ⊆ J).card : Real) := by exact_mod_cast hwin
    have hcount' : ((Qr.filter fun q => ∀ j, S (q j) ⊆ J).card : Real) ≤
        ((additiveQuadruplesIn X).filter fun q => ∀ w,
          (∀ j, w ∈ bohr ((chosenIndices I c (q j)).image fun i => θ i (q j)) η) →
          chosenGlued T L r c (q 0) w + chosenGlued T L r c (q 1) w =
            chosenGlued T L r c (q 2) w + chosenGlued T L r c (q 3) w).card := by
      exact_mod_cast hcount
    have hchoose : (0 : Real) ≤ ((m + 8 * s₀).choose (8 * s₀) : Real) := Nat.cast_nonneg _
    -- the lower bound on `|Qr|`
    have hA'N : (A'.card : Real) ≤ N := by
      have := Finset.card_le_univ A'
      rw [ZMod.card] at this
      exact_mod_cast this
    have h12 : 0 ≤ 1 - 2 * η' := by linarith
    have hcube : ((1 - 2 * η') * (N : Real)) ^ 3 ≤ (A'.card : Real) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hA' 3
    have hQrlow : ((1 - 2 * η') ^ 3 - 2 * η' - 16 * (ε + 2 * ε₂)) * (N : Real) ^ 3 -
        6 * (N : Real) ^ 2 ≤ Qr.card := by
      have e1 : ((N : Real) - A'.card) * (N : Real) ^ 2 ≤ 2 * η' * (N : Real) ^ 3 := by
        have : (N : Real) - A'.card ≤ 2 * η' * N := by linarith
        calc ((N : Real) - A'.card) * (N : Real) ^ 2 ≤ (2 * η' * N) * (N : Real) ^ 2 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = 2 * η' * (N : Real) ^ 3 := by ring
      have e2 : ((1 - 2 * η') * (N : Real)) ^ 3 = (1 - 2 * η') ^ 3 * (N : Real) ^ 3 := by ring
      linarith
    calc ((1 - 2 * η') ^ 3 - 2 * η' - 16 * (ε + 2 * ε₂)) * (N : Real) ^ 3 - 6 * (N : Real) ^ 2
        ≤ Qr.card := hQrlow
      _ ≤ ((m + 8 * s₀).choose (8 * s₀) : Real) *
          ((Qr.filter fun q => ∀ j, S (q j) ⊆ J).card : Real) := hwin'
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount' hchoose

end LeanProofs.GowersSzemeredi
