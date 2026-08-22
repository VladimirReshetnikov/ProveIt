import ExponentialIdentities.TwoBaseIntegerExponent.MixedDeterminantUnitBridge

/-!
# Global mixed-prefix cascade specialization

This module closes the finite combinatorial specialization left open by
`MixedDeterminantUnitBridge`: the first `N` pairs in its sorted finite box
are proved to be the genuine first `N` elements of the whole mixed exponent
semigroup.  Regrouping that prefix lexicographically and colexicographically
then supplies exact consecutive fiber certificates.

The endpoint theorems transfer both the all-layer row-block Laplace expansion
and the dyadic/triadic unit-ordering divisors to the raw mixed integer
determinant.  They deliberately make no claim that the residual signed sums
have bounded valuation; cancellation across the displayed layers remains the
arithmetic bottleneck.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset

noncomputable section

/-- The box index of the axial point `(k,0)`. -/
def mixedExponentAxisIndex (N : ℕ) (k : Fin N) :
    Fin ((N + 1) * (N + 1)) :=
  finProdFinEquiv
    (⟨k, Nat.lt_succ_of_lt k.isLt⟩, ⟨0, Nat.zero_lt_succ N⟩)

@[simp]
theorem mixedExponentBoxPair_axisIndex (N : ℕ) (k : Fin N) :
    mixedExponentBoxPair N (mixedExponentAxisIndex N k) = ((k : ℕ), 0) := by
  simp [mixedExponentBoxPair, mixedExponentAxisIndex]

/-- The position of `(k,0)` in the sorted exponent box. -/
def sortedMixedExponentAxisIndex (N : ℕ) (k : Fin N) :
    Fin ((N + 1) * (N + 1)) :=
  (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)).symm
    (mixedExponentAxisIndex N k)

@[simp]
theorem sortedMixedExponentBoxPair_axisIndex (N : ℕ) (k : Fin N) :
    sortedMixedExponentBoxPair N (sortedMixedExponentAxisIndex N k) = ((k : ℕ), 0) := by
  simp [sortedMixedExponentBoxPair, sortedMixedExponentAxisIndex]

theorem sortedMixedExponentAxisIndex_injective (N : ℕ) :
    Function.Injective (sortedMixedExponentAxisIndex N) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg
    (fun x => (sortedMixedExponentBoxPair N x).1) h
  simpa using h'

/-- At least `N` entries of the sorted box have mixed weight below `N`. -/
theorem N_le_card_sortedMixedExponentBox_lt (N : ℕ) :
    N ≤ #{j : Fin ((N + 1) * (N + 1)) |
      mixedExponent (sortedMixedExponentBoxPair N j) < (N : ℝ)} := by
  let S := {j : Fin ((N + 1) * (N + 1)) |
    mixedExponent (sortedMixedExponentBoxPair N j) < (N : ℝ)}
  let f : Fin N → S := fun k => ⟨sortedMixedExponentAxisIndex N k, by
    simp [S, mixedExponent_mk]⟩
  have hf : Function.Injective f := by
    intro i j h
    apply sortedMixedExponentAxisIndex_injective N
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [S] using hcard

/-- Every entry in the first `N` positions of the sorted box has weight below `N`. -/
theorem sortedMixedExponentBoxPrefix_weight_lt_nat (N : ℕ) (i : Fin N) :
    mixedExponent (sortedMixedExponentBoxPrefix N i) < (N : ℝ) := by
  let g : Fin ((N + 1) * (N + 1)) → ℝ :=
    mixedExponent ∘ sortedMixedExponentBoxPair N
  have hg : Monotone g := by
    exact (sortedMixedExponentBoxPair_weight_strictMono N).monotone
  let j : Fin ((N + 1) * (N + 1)) :=
    Fin.castLE (le_mixedExponentBox_card N) i
  have hj : (j : ℕ) < #{x | g x < (N : ℝ)} := by
    have hcard := N_le_card_sortedMixedExponentBox_lt N
    have hij : (j : ℕ) < N := i.isLt
    exact lt_of_lt_of_le hij hcard
  have := (Tuple.lt_card_lt_iff_apply_lt_of_monotone (j := j)
    (a := (N : ℝ)) hg).mp hj
  exact this

/-- Any exponent pair outside the `(N+1)×(N+1)` box has weight strictly above `N`. -/
theorem nat_lt_mixedExponent_of_outside_box
    (N : ℕ) (ab : ℕ × ℕ) (h : N < ab.1 ∨ N < ab.2) :
    (N : ℝ) < mixedExponent ab := by
  rcases ab with ⟨a, b⟩
  rcases h with ha | hb
  · have haR : (N : ℝ) < (a : ℝ) := by exact_mod_cast ha
    simp only [mixedExponent_mk]
    have hnonneg : 0 ≤ (b : ℝ) * logThreeDivLogTwo :=
      mul_nonneg (Nat.cast_nonneg b) logThreeDivLogTwo_pos.le
    linarith
  · have hbR : (N : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have htheta : 1 < logThreeDivLogTwo := one_lt_logThreeDivLogTwo
    have hbpos : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    have hmul : (b : ℝ) < (b : ℝ) * logThreeDivLogTwo := by
      nlinarith
    simp only [mixedExponent_mk]
    have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith

/-- **Global-prefix certificate.** Every one of the first `N` entries of the sorted
box precedes every exponent pair outside that box. Hence the finite sorted-box prefix
is also the genuine initial segment of the whole mixed semigroup. -/
theorem sortedMixedExponentBoxPrefix_weight_lt_of_outside
    (N : ℕ) (i : Fin N) (ab : ℕ × ℕ)
    (h : N < ab.1 ∨ N < ab.2) :
    mixedExponent (sortedMixedExponentBoxPrefix N i) < mixedExponent ab := by
  exact (sortedMixedExponentBoxPrefix_weight_lt_nat N i).trans
    (nat_lt_mixedExponent_of_outside_box N ab h)

/-- **Exact global initial-segment theorem.** An exponent pair omitted by the
sorted-box prefix has weight larger than every pair in the prefix, whether the omitted
pair lies inside or outside the finite box. -/
theorem sortedMixedExponentBoxPrefix_weight_lt_of_not_mem
    (N : ℕ) (i : Fin N) (ab : ℕ × ℕ)
    (hnot : ∀ j : Fin N, sortedMixedExponentBoxPrefix N j ≠ ab) :
    mixedExponent (sortedMixedExponentBoxPrefix N i) < mixedExponent ab := by
  by_cases hout : N < ab.1 ∨ N < ab.2
  · exact sortedMixedExponentBoxPrefix_weight_lt_of_outside N i ab hout
  · have ha : ab.1 < N + 1 := by omega
    have hb : ab.2 < N + 1 := by omega
    let idx : Fin ((N + 1) * (N + 1)) :=
      finProdFinEquiv (⟨ab.1, ha⟩, ⟨ab.2, hb⟩)
    let pos : Fin ((N + 1) * (N + 1)) :=
      (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)).symm idx
    have hpair : sortedMixedExponentBoxPair N pos = ab := by
      simp [sortedMixedExponentBoxPair, pos, idx, mixedExponentBoxPair]
    have hpos : N ≤ (pos : ℕ) := by
      by_contra h
      have hlt : (pos : ℕ) < N := by omega
      let j : Fin N := ⟨pos, hlt⟩
      have hcast : Fin.castLE (le_mixedExponentBox_card N) j = pos := by
        apply Fin.ext
        rfl
      have hj := hnot j
      apply hj
      rw [sortedMixedExponentBoxPrefix, Function.comp_apply, hcast, hpair]
    have hindex :
        Fin.castLE (le_mixedExponentBox_card N) i < pos := by
      change (i : ℕ) < (pos : ℕ)
      omega
    have hweight := sortedMixedExponentBoxPair_weight_strictMono N hindex
    simpa [sortedMixedExponentBoxPrefix, hpair] using hweight

/-! ## Generic consecutive-fiber certificate -/

theorem fiberDegree_lt_card_of_lowerClosed
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (hinj : Function.Injective fun i => (b i, degree i))
    (hlower : ∀ (i : Fin N) (d : ℕ), d < degree i →
      ∃ j : Fin N, b j = b i ∧ degree j = d)
    (k : o) (i : {i : Fin N // b i = k}) :
    degree i.1 < Fintype.card {i : Fin N // b i = k} := by
  classical
  let F := {i : Fin N // b i = k}
  let deg : F → ℕ := fun j => degree j.1
  have hdegInj : Function.Injective deg := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    apply Prod.ext
    · change b x.1 = b y.1
      rw [x.property, y.property]
    · exact hxy
  have hsubset : Finset.range (degree i.1 + 1) ⊆
      Finset.univ.image deg := by
    intro d hd
    simp only [Finset.mem_range] at hd
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_cases heq : d = degree i.1
    · exact ⟨i, by simpa [deg] using heq.symm⟩
    · have hlt : d < degree i.1 := by omega
      obtain ⟨j, hjb, hjd⟩ := hlower i.1 d hlt
      have hjk : b j = k := hjb.trans i.property
      exact ⟨⟨j, hjk⟩, by simpa [deg] using hjd⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_range,
    Finset.card_image_of_injective _ hdegInj,
    Finset.card_univ] at hcard
  exact Nat.lt_of_succ_le hcard

/-- A lower-closed injective degree on each fiber canonically identifies that fiber
with `Fin` of its cardinality, and the equivalence is exactly degree-preserving. -/
noncomputable def lowerClosedFiberDegreeEquiv
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (hinj : Function.Injective fun i => (b i, degree i))
    (hlower : ∀ (i : Fin N) (d : ℕ), d < degree i →
      ∃ j : Fin N, b j = b i ∧ degree j = d)
    (k : o) :
    {i : Fin N // b i = k} ≃
      Fin (Fintype.card {i : Fin N // b i = k}) := by
  let f : {i : Fin N // b i = k} →
      Fin (Fintype.card {i : Fin N // b i = k}) :=
    fun i => ⟨degree i.1,
      fiberDegree_lt_card_of_lowerClosed b degree hinj hlower k i⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  constructor
  · intro i j h
    apply Subtype.ext
    apply hinj
    apply Prod.ext
    · change b i.1 = b j.1
      rw [i.property, j.property]
    · exact Fin.ext_iff.mp h
  · simp

@[simp]
theorem lowerClosedFiberDegreeEquiv_apply_val
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (hinj : Function.Injective fun i => (b i, degree i))
    (hlower : ∀ (i : Fin N) (d : ℕ), d < degree i →
      ∃ j : Fin N, b j = b i ∧ degree j = d)
    (k : o) (i : {i : Fin N // b i = k}) :
    ((lowerClosedFiberDegreeEquiv b degree hinj hlower k i :
      Fin (Fintype.card {i : Fin N // b i = k})) : ℕ) = degree i.1 := by
  rfl

theorem degree_lowerClosedFiberDegreeEquiv_symm
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (hinj : Function.Injective fun i => (b i, degree i))
    (hlower : ∀ (i : Fin N) (d : ℕ), d < degree i →
      ∃ j : Fin N, b j = b i ∧ degree j = d)
    (k : o) (j : Fin (Fintype.card {i : Fin N // b i = k})) :
    degree ((lowerClosedFiberDegreeEquiv b degree hinj hlower k).symm j).1 =
      (j : ℕ) := by
  have h := lowerClosedFiberDegreeEquiv_apply_val b degree hinj hlower k
    ((lowerClosedFiberDegreeEquiv b degree hinj hlower k).symm j)
  simpa using h.symm

/-! ## Concrete lexicographic fiber data for the global prefix -/

theorem sortedMixedExponentBoxPrefix_fst_lt_succ (N : ℕ) (i : Fin N) :
    (sortedMixedExponentBoxPrefix N i).1 < N + 1 := by
  change ((finProdFinEquiv.symm
    (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)
      (Fin.castLE (le_mixedExponentBox_card N) i))).1 : ℕ) < N + 1
  exact (finProdFinEquiv.symm
    (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)
      (Fin.castLE (le_mixedExponentBox_card N) i))).1.isLt

theorem sortedMixedExponentBoxPrefix_snd_lt_succ (N : ℕ) (i : Fin N) :
    (sortedMixedExponentBoxPrefix N i).2 < N + 1 := by
  change ((finProdFinEquiv.symm
    (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)
      (Fin.castLE (le_mixedExponentBox_card N) i))).2 : ℕ) < N + 1
  exact (finProdFinEquiv.symm
    (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)
      (Fin.castLE (le_mixedExponentBox_card N) i))).2.isLt

theorem sortedMixedExponentBoxPrefix_injective (N : ℕ) :
    Function.Injective (sortedMixedExponentBoxPrefix N) := by
  intro i j h
  apply (sortedMixedExponentBoxPrefix_weight_strictMono N).injective
  exact congrArg mixedExponent h

/-- Downward closure in the second coordinate of the genuine global prefix. -/
theorem sortedMixedExponentBoxPrefix_lowerClosed_snd
    (N : ℕ) (i : Fin N) (d : ℕ)
    (hd : d < (sortedMixedExponentBoxPrefix N i).2) :
    ∃ j : Fin N, sortedMixedExponentBoxPrefix N j =
      ((sortedMixedExponentBoxPrefix N i).1, d) := by
  by_contra h
  push Not at h
  have hglobal := sortedMixedExponentBoxPrefix_weight_lt_of_not_mem N i
    ((sortedMixedExponentBoxPrefix N i).1, d) h
  have hlower :
      mixedExponent ((sortedMixedExponentBoxPrefix N i).1, d) <
        mixedExponent (sortedMixedExponentBoxPrefix N i) := by
    simpa only [Prod.eta] using
      (mixedExponent_lt_of_snd_lt (a := (sortedMixedExponentBoxPrefix N i).1) hd)
  exact lt_asymm hglobal hlower

/-- Downward closure in the first coordinate of the genuine global prefix. -/
theorem sortedMixedExponentBoxPrefix_lowerClosed_fst
    (N : ℕ) (i : Fin N) (d : ℕ)
    (hd : d < (sortedMixedExponentBoxPrefix N i).1) :
    ∃ j : Fin N, sortedMixedExponentBoxPrefix N j =
      (d, (sortedMixedExponentBoxPrefix N i).2) := by
  by_contra h
  push Not at h
  have hglobal := sortedMixedExponentBoxPrefix_weight_lt_of_not_mem N i
    (d, (sortedMixedExponentBoxPrefix N i).2) h
  have hlower :
      mixedExponent (d, (sortedMixedExponentBoxPrefix N i).2) <
        mixedExponent (sortedMixedExponentBoxPrefix N i) := by
    simpa only [Prod.eta] using
      (mixedExponent_lt_of_fst_lt (b := (sortedMixedExponentBoxPrefix N i).2) hd)
  exact lt_asymm hglobal hlower

/-- Base-`N+1` code that orders bounded exponent pairs lexicographically. -/
def mixedPrefixLexKey (N : ℕ) (i : Fin N) : ℕ :=
  (N + 1) * (sortedMixedExponentBoxPrefix N i).1 +
    (sortedMixedExponentBoxPrefix N i).2

theorem mixedPrefixLexKey_injective (N : ℕ) :
    Function.Injective (mixedPrefixLexKey N) := by
  intro i j h
  apply sortedMixedExponentBoxPrefix_injective N
  apply Prod.ext
  · have hdiv := congrArg (fun x : ℕ => x / (N + 1)) h
    simpa [mixedPrefixLexKey, Nat.mul_add_div (Nat.zero_lt_succ N),
      Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N i),
      Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N j)] using hdiv
  · have hmod := congrArg (fun x : ℕ => x % (N + 1)) h
    simpa [mixedPrefixLexKey, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N i),
      Nat.mod_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N j)] using hmod

/-- Prefix columns regrouped by first coordinate and, within each fiber, by second
coordinate. -/
def lexSortedMixedExponentBoxPrefix (N : ℕ) : Fin N → ℕ × ℕ :=
  sortedMixedExponentBoxPrefix N ∘ Tuple.sort (mixedPrefixLexKey N)

theorem lexSortedMixedExponentBoxPrefix_key_strictMono (N : ℕ) :
    StrictMono (mixedPrefixLexKey N ∘ Tuple.sort (mixedPrefixLexKey N)) := by
  exact (Tuple.monotone_sort (mixedPrefixLexKey N)).strictMono_of_injective
    ((mixedPrefixLexKey_injective N).comp (Tuple.sort (mixedPrefixLexKey N)).injective)

theorem lexSortedMixedExponentBoxPrefix_fst_monotone (N : ℕ) :
    Monotone fun i => (lexSortedMixedExponentBoxPrefix N i).1 := by
  intro i j hij
  have hkey := (lexSortedMixedExponentBoxPrefix_key_strictMono N).monotone hij
  have hdiv := Nat.div_le_div_right (c := N + 1) hkey
  simp only [Function.comp_apply, mixedPrefixLexKey] at hdiv
  rw [Nat.mul_add_div (Nat.zero_lt_succ N),
    Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N
      (Tuple.sort (mixedPrefixLexKey N) i)), add_zero,
    Nat.mul_add_div (Nat.zero_lt_succ N),
    Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_snd_lt_succ N
      (Tuple.sort (mixedPrefixLexKey N) j)), add_zero] at hdiv
  exact hdiv

theorem lexSortedMixedExponentBoxPrefix_injective (N : ℕ) :
    Function.Injective (lexSortedMixedExponentBoxPrefix N) :=
  (sortedMixedExponentBoxPrefix_injective N).comp
    (Tuple.sort (mixedPrefixLexKey N)).injective

theorem lexSortedMixedExponentBoxPrefix_lowerClosed_snd
    (N : ℕ) (i : Fin N) (d : ℕ)
    (hd : d < (lexSortedMixedExponentBoxPrefix N i).2) :
    ∃ j : Fin N,
      (lexSortedMixedExponentBoxPrefix N j).1 =
          (lexSortedMixedExponentBoxPrefix N i).1 ∧
        (lexSortedMixedExponentBoxPrefix N j).2 = d := by
  let rho := Tuple.sort (mixedPrefixLexKey N)
  obtain ⟨j₀, hj₀⟩ :=
    sortedMixedExponentBoxPrefix_lowerClosed_snd N (rho i) d hd
  refine ⟨rho.symm j₀, ?_⟩
  change
    (sortedMixedExponentBoxPrefix N (rho (rho.symm j₀))).1 =
        (sortedMixedExponentBoxPrefix N (rho i)).1 ∧
      (sortedMixedExponentBoxPrefix N (rho (rho.symm j₀))).2 = d
  rw [rho.apply_symm_apply, hj₀]
  simp

/-- First-coordinate block label for lexicographically regrouped prefix columns. -/
def lexMixedPrefixBlock (N : ℕ) (i : Fin N) : Fin (N + 1) :=
  ⟨(lexSortedMixedExponentBoxPrefix N i).1,
    sortedMixedExponentBoxPrefix_fst_lt_succ N
      (Tuple.sort (mixedPrefixLexKey N) i)⟩

/-- Local second-coordinate degree within a first-coordinate block. -/
def lexMixedPrefixDegree (N : ℕ) (i : Fin N) : ℕ :=
  (lexSortedMixedExponentBoxPrefix N i).2

theorem lexMixedPrefixBlock_monotone (N : ℕ) :
    Monotone (lexMixedPrefixBlock N) := by
  intro i j hij
  exact lexSortedMixedExponentBoxPrefix_fst_monotone N hij

theorem lexMixedPrefixBlock_degree_injective (N : ℕ) :
    Function.Injective fun i =>
      (lexMixedPrefixBlock N i, lexMixedPrefixDegree N i) := by
  intro i j h
  apply lexSortedMixedExponentBoxPrefix_injective N
  apply Prod.ext
  · exact congrArg (fun z => (z.1 : ℕ)) h
  · change lexMixedPrefixDegree N i = lexMixedPrefixDegree N j
    exact congrArg (fun z : Fin (N + 1) × ℕ => z.2) h

theorem lexMixedPrefixDegree_lowerClosed (N : ℕ) :
    ∀ (i : Fin N) (d : ℕ), d < lexMixedPrefixDegree N i →
      ∃ j : Fin N,
        lexMixedPrefixBlock N j = lexMixedPrefixBlock N i ∧
          lexMixedPrefixDegree N j = d := by
  intro i d hd
  obtain ⟨j, hfst, hsnd⟩ :=
    lexSortedMixedExponentBoxPrefix_lowerClosed_snd N i d hd
  refine ⟨j, ?_, hsnd⟩
  apply Fin.ext
  exact hfst

/-- Size of a fixed-first-coordinate fiber in the global mixed prefix. -/
def lexMixedPrefixFiberSize (N : ℕ) (k : Fin (N + 1)) : ℕ :=
  Fintype.card {i : Fin N // lexMixedPrefixBlock N i = k}

/-- Degree-preserving enumeration of a fixed-first-coordinate fiber. -/
noncomputable def lexMixedPrefixFiberEquiv (N : ℕ) (k : Fin (N + 1)) :
    {i : Fin N // lexMixedPrefixBlock N i = k} ≃
      Fin (lexMixedPrefixFiberSize N k) :=
  lowerClosedFiberDegreeEquiv
    (lexMixedPrefixBlock N) (lexMixedPrefixDegree N)
    (lexMixedPrefixBlock_degree_injective N)
    (lexMixedPrefixDegree_lowerClosed N) k

theorem lexMixedPrefixFiberEquiv_degree (N : ℕ) (k : Fin (N + 1))
    (j : Fin (lexMixedPrefixFiberSize N k)) :
    lexMixedPrefixDegree N ((lexMixedPrefixFiberEquiv N k).symm j).1 =
      (j : ℕ) :=
  degree_lowerClosedFiberDegreeEquiv_symm
    (lexMixedPrefixBlock N) (lexMixedPrefixDegree N)
    (lexMixedPrefixBlock_degree_injective N)
    (lexMixedPrefixDegree_lowerClosed N) k j

/-- **Concrete dyadic bridge for the genuine global prefix.** No column permutation,
fiber-size function, or degree certificate remains as a hypothesis. -/
theorem two_pow_globalMixedPrefix_minCost_add_unit_dvd_det
    {N : ℕ} {depth : Fin N → ℕ}
    (M : ℤ) (q : Fin N → ℤ)
    (z : Fin N → ℕ) (hq : ∀ row, q row = 2 * (z row : ℤ) + 1)
    (hdepth : StrictAnti depth) :
    (2 : ℤ) ^
        (rankOneAssignmentCost depth
            ((fun k : Fin (N + 1) => (k : ℕ)) ∘ lexMixedPrefixBlock N)
            (Equiv.refl _) +
          rowBlockOrderingExponent (lexMixedPrefixFiberSize N)
            twoUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix
        (fun row => (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q
        (sortedMixedExponentBoxPrefix N)).det := by
  apply two_pow_minCost_add_rowBlockOrderingExponent_dvd_det_mixedIntegerPowerMatrix
    M q (sortedMixedExponentBoxPrefix N)
    (Tuple.sort (mixedPrefixLexKey N))
    (lexMixedPrefixBlock N)
    (value := fun k : Fin (N + 1) => (k : ℕ))
    (lexMixedPrefixFiberSize N) (lexMixedPrefixFiberEquiv N)
    (lexMixedPrefixDegree N) (z := z)
  · intro col
    apply Prod.ext <;> rfl
  · exact lexMixedPrefixFiberEquiv_degree N
  · exact hq
  · exact hdepth
  · exact lexMixedPrefixBlock_monotone N
  · intro i j hij
    exact hij

/-! ## Symmetric second-coordinate fibers -/

/-- Base-`N+1` code that orders bounded exponent pairs first by their second
coordinate and then by their first. -/
def mixedPrefixColexKey (N : ℕ) (i : Fin N) : ℕ :=
  (N + 1) * (sortedMixedExponentBoxPrefix N i).2 +
    (sortedMixedExponentBoxPrefix N i).1

theorem mixedPrefixColexKey_injective (N : ℕ) :
    Function.Injective (mixedPrefixColexKey N) := by
  intro i j h
  apply sortedMixedExponentBoxPrefix_injective N
  apply Prod.ext
  · have hmod := congrArg (fun x : ℕ => x % (N + 1)) h
    simpa [mixedPrefixColexKey, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N i),
      Nat.mod_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N j)] using hmod
  · have hdiv := congrArg (fun x : ℕ => x / (N + 1)) h
    simpa [mixedPrefixColexKey, Nat.mul_add_div (Nat.zero_lt_succ N),
      Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N i),
      Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N j)] using hdiv

/-- Prefix columns regrouped by second coordinate and, within each fiber, by first
coordinate. -/
def colexSortedMixedExponentBoxPrefix (N : ℕ) : Fin N → ℕ × ℕ :=
  sortedMixedExponentBoxPrefix N ∘ Tuple.sort (mixedPrefixColexKey N)

theorem colexSortedMixedExponentBoxPrefix_key_strictMono (N : ℕ) :
    StrictMono (mixedPrefixColexKey N ∘ Tuple.sort (mixedPrefixColexKey N)) := by
  exact (Tuple.monotone_sort (mixedPrefixColexKey N)).strictMono_of_injective
    ((mixedPrefixColexKey_injective N).comp
      (Tuple.sort (mixedPrefixColexKey N)).injective)

theorem colexSortedMixedExponentBoxPrefix_snd_monotone (N : ℕ) :
    Monotone fun i => (colexSortedMixedExponentBoxPrefix N i).2 := by
  intro i j hij
  have hkey := (colexSortedMixedExponentBoxPrefix_key_strictMono N).monotone hij
  have hdiv := Nat.div_le_div_right (c := N + 1) hkey
  simp only [Function.comp_apply, mixedPrefixColexKey] at hdiv
  rw [Nat.mul_add_div (Nat.zero_lt_succ N),
    Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N
      (Tuple.sort (mixedPrefixColexKey N) i)), add_zero,
    Nat.mul_add_div (Nat.zero_lt_succ N),
    Nat.div_eq_of_lt (sortedMixedExponentBoxPrefix_fst_lt_succ N
      (Tuple.sort (mixedPrefixColexKey N) j)), add_zero] at hdiv
  exact hdiv

theorem colexSortedMixedExponentBoxPrefix_injective (N : ℕ) :
    Function.Injective (colexSortedMixedExponentBoxPrefix N) :=
  (sortedMixedExponentBoxPrefix_injective N).comp
    (Tuple.sort (mixedPrefixColexKey N)).injective

theorem colexSortedMixedExponentBoxPrefix_lowerClosed_fst
    (N : ℕ) (i : Fin N) (d : ℕ)
    (hd : d < (colexSortedMixedExponentBoxPrefix N i).1) :
    ∃ j : Fin N,
      (colexSortedMixedExponentBoxPrefix N j).1 = d ∧
        (colexSortedMixedExponentBoxPrefix N j).2 =
          (colexSortedMixedExponentBoxPrefix N i).2 := by
  let rho := Tuple.sort (mixedPrefixColexKey N)
  obtain ⟨j₀, hj₀⟩ :=
    sortedMixedExponentBoxPrefix_lowerClosed_fst N (rho i) d hd
  refine ⟨rho.symm j₀, ?_⟩
  change
    (sortedMixedExponentBoxPrefix N (rho (rho.symm j₀))).1 = d ∧
      (sortedMixedExponentBoxPrefix N (rho (rho.symm j₀))).2 =
        (sortedMixedExponentBoxPrefix N (rho i)).2
  rw [rho.apply_symm_apply, hj₀]
  simp

/-- Second-coordinate block label for the colexicographically regrouped prefix. -/
def colexMixedPrefixBlock (N : ℕ) (i : Fin N) : Fin (N + 1) :=
  ⟨(colexSortedMixedExponentBoxPrefix N i).2,
    sortedMixedExponentBoxPrefix_snd_lt_succ N
      (Tuple.sort (mixedPrefixColexKey N) i)⟩

/-- Local first-coordinate degree within a second-coordinate block. -/
def colexMixedPrefixDegree (N : ℕ) (i : Fin N) : ℕ :=
  (colexSortedMixedExponentBoxPrefix N i).1

theorem colexMixedPrefixBlock_monotone (N : ℕ) :
    Monotone (colexMixedPrefixBlock N) := by
  intro i j hij
  exact colexSortedMixedExponentBoxPrefix_snd_monotone N hij

theorem colexMixedPrefixBlock_degree_injective (N : ℕ) :
    Function.Injective fun i =>
      (colexMixedPrefixBlock N i, colexMixedPrefixDegree N i) := by
  intro i j h
  apply colexSortedMixedExponentBoxPrefix_injective N
  apply Prod.ext
  · change colexMixedPrefixDegree N i = colexMixedPrefixDegree N j
    exact congrArg (fun z : Fin (N + 1) × ℕ => z.2) h
  · exact congrArg (fun z => (z.1 : ℕ)) h

theorem colexMixedPrefixDegree_lowerClosed (N : ℕ) :
    ∀ (i : Fin N) (d : ℕ), d < colexMixedPrefixDegree N i →
      ∃ j : Fin N,
        colexMixedPrefixBlock N j = colexMixedPrefixBlock N i ∧
          colexMixedPrefixDegree N j = d := by
  intro i d hd
  obtain ⟨j, hfst, hsnd⟩ :=
    colexSortedMixedExponentBoxPrefix_lowerClosed_fst N i d hd
  refine ⟨j, ?_, hfst⟩
  apply Fin.ext
  exact hsnd

def colexMixedPrefixFiberSize (N : ℕ) (k : Fin (N + 1)) : ℕ :=
  Fintype.card {i : Fin N // colexMixedPrefixBlock N i = k}

noncomputable def colexMixedPrefixFiberEquiv (N : ℕ) (k : Fin (N + 1)) :
    {i : Fin N // colexMixedPrefixBlock N i = k} ≃
      Fin (colexMixedPrefixFiberSize N k) :=
  lowerClosedFiberDegreeEquiv
    (colexMixedPrefixBlock N) (colexMixedPrefixDegree N)
    (colexMixedPrefixBlock_degree_injective N)
    (colexMixedPrefixDegree_lowerClosed N) k

theorem colexMixedPrefixFiberEquiv_degree (N : ℕ) (k : Fin (N + 1))
    (j : Fin (colexMixedPrefixFiberSize N k)) :
    colexMixedPrefixDegree N ((colexMixedPrefixFiberEquiv N k).symm j).1 =
      (j : ℕ) :=
  degree_lowerClosedFiberDegreeEquiv_symm
    (colexMixedPrefixBlock N) (colexMixedPrefixDegree N)
    (colexMixedPrefixBlock_degree_injective N)
    (colexMixedPrefixDegree_lowerClosed N) k j

/-- **Concrete triadic bridge for the genuine global prefix.** This is the exact
second-coordinate counterpart of the dyadic theorem above. -/
theorem three_pow_globalMixedPrefix_minCost_add_unit_dvd_det
    {N : ℕ} {depth : Fin N → ℕ}
    (A : ℤ) (r : Fin N → ℤ)
    (z : Fin N → ℕ) (residue : Fin N → Fin 2)
    (hr : ∀ row,
      r row = 3 * (z row : ℤ) + ((residue row : ℕ) : ℤ) + 1)
    (hdepth : StrictAnti depth) :
    (3 : ℤ) ^
        (rankOneAssignmentCost depth
            ((fun k : Fin (N + 1) => (k : ℕ)) ∘ colexMixedPrefixBlock N)
            (Equiv.refl _) +
          rowBlockOrderingExponent (colexMixedPrefixFiberSize N)
            threeUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix r
        (fun row => (3 : ℤ) ^ depth row * A ^ (row : ℕ))
        (sortedMixedExponentBoxPrefix N)).det := by
  apply three_pow_minCost_add_rowBlockOrderingExponent_dvd_det_mixedIntegerPowerMatrix
    A r (sortedMixedExponentBoxPrefix N)
    (Tuple.sort (mixedPrefixColexKey N))
    (colexMixedPrefixBlock N)
    (value := fun k : Fin (N + 1) => (k : ℕ))
    (colexMixedPrefixFiberSize N) (colexMixedPrefixFiberEquiv N)
    (colexMixedPrefixDegree N) (z := z) (residue := residue)
  · intro col
    apply Prod.ext <;> rfl
  · exact colexMixedPrefixFiberEquiv_degree N
  · exact hr
  · exact hdepth
  · exact colexMixedPrefixBlock_monotone N
  · intro i j hij
    exact hij

/-! ## Exact all-layer specialization to the global prefix -/

/-- The unit matrix left after the dyadic structural powers are removed and
the genuine global prefix is grouped by its first exponent coordinate. -/
def dyadicGlobalMixedPrefixUnitMatrix
    {N : ℕ} (M : ℤ) (q : Fin N → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  fiberScaledConsecutivePowerMatrix
    (lexMixedPrefixBlock N) (lexMixedPrefixDegree N)
    (fun k row => M ^ ((row : ℕ) * (k : ℕ)))
    (fun _ row => q row)

/-- **Concrete all-layer dyadic cascade for the genuine first `N` mixed
exponents.**  The only sign is the explicit column-regrouping sign.  There
are no remaining global-enumeration or fiber-certificate hypotheses. -/
theorem sign_mul_det_globalMixedPrefix_two_eq_minPow_mul_sum_assignmentExcess
    {N : ℕ} {depth : Fin N → ℕ}
    (M : ℤ) (q : Fin N → ℤ) (hdepth : StrictAnti depth) :
    ((Equiv.Perm.sign (Tuple.sort (mixedPrefixLexKey N)) : ℤ) : ℤ) *
        (mixedIntegerPowerMatrix
          (fun row => (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q
          (sortedMixedExponentBoxPrefix N)).det =
      (2 : ℤ) ^ rankOneAssignmentCost depth
          ((fun k : Fin (N + 1) => (k : ℕ)) ∘ lexMixedPrefixBlock N)
          (Equiv.refl _) *
        ∑ a : RowBlockAssignment (lexMixedPrefixBlock N),
          (2 : ℤ) ^ rowBlockAssignmentExcess depth
              (fun k : Fin (N + 1) => (k : ℕ))
              (lexMixedPrefixBlock N) a *
            rowBlockMinorProduct (lexMixedPrefixBlock N)
              (dyadicGlobalMixedPrefixUnitMatrix M q) a := by
  let B := mixedIntegerPowerMatrix
    (fun row => (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q
    (sortedMixedExponentBoxPrefix N)
  let rho := Tuple.sort (mixedPrefixLexKey N)
  have hmatrix :
      B.submatrix id rho =
        rankOnePowerMatrix 2 depth (lexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (dyadicGlobalMixedPrefixUnitMatrix M q) := by
    exact submatrix_mixedIntegerPowerMatrix_eq_two_rankOnePowerMatrix
      depth M q (sortedMixedExponentBoxPrefix N) rho
      (lexMixedPrefixBlock N) (fun k : Fin (N + 1) => (k : ℕ))
      (lexMixedPrefixDegree N) (by
        intro col
        apply Prod.ext <;> rfl)
  calc
    ((Equiv.Perm.sign rho : ℤ) : ℤ) * B.det =
        (B.submatrix id rho).det := (Matrix.det_permute' rho B).symm
    _ = (rankOnePowerMatrix 2 depth (lexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (dyadicGlobalMixedPrefixUnitMatrix M q)).det := by rw [hmatrix]
    _ = _ := det_rankOnePowerMatrix_eq_minPow_mul_sum_assignmentExcess
      2 (dyadicGlobalMixedPrefixUnitMatrix M q) hdepth
      (lexMixedPrefixBlock_monotone N) (fun _ _ h => h)

/-- Exact finite-depth form of the preceding concrete dyadic cascade. -/
theorem sign_mul_det_globalMixedPrefix_two_eq_minPow_mul_truncatedAssignmentSum
    {N : ℕ} {depth : Fin N → ℕ}
    (M : ℤ) (q : Fin N → ℤ) (hdepth : StrictAnti depth) (K : ℕ) :
    ((Equiv.Perm.sign (Tuple.sort (mixedPrefixLexKey N)) : ℤ) : ℤ) *
        (mixedIntegerPowerMatrix
          (fun row => (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q
          (sortedMixedExponentBoxPrefix N)).det =
      (2 : ℤ) ^ rankOneAssignmentCost depth
          ((fun k : Fin (N + 1) => (k : ℕ)) ∘ lexMixedPrefixBlock N)
          (Equiv.refl _) *
        ((∑ a ∈ (Finset.univ.filter fun a :
              RowBlockAssignment (lexMixedPrefixBlock N) =>
              rowBlockAssignmentExcess depth
                (fun k : Fin (N + 1) => (k : ℕ))
                (lexMixedPrefixBlock N) a < K),
            (2 : ℤ) ^ rowBlockAssignmentExcess depth
                (fun k : Fin (N + 1) => (k : ℕ))
                (lexMixedPrefixBlock N) a *
              rowBlockMinorProduct (lexMixedPrefixBlock N)
                (dyadicGlobalMixedPrefixUnitMatrix M q) a) +
          (2 : ℤ) ^ K *
            ∑ a ∈ (Finset.univ.filter fun a :
                RowBlockAssignment (lexMixedPrefixBlock N) =>
                K ≤ rowBlockAssignmentExcess depth
                  (fun k : Fin (N + 1) => (k : ℕ))
                  (lexMixedPrefixBlock N) a),
              (2 : ℤ) ^ (rowBlockAssignmentExcess depth
                    (fun k : Fin (N + 1) => (k : ℕ))
                    (lexMixedPrefixBlock N) a - K) *
                rowBlockMinorProduct (lexMixedPrefixBlock N)
                  (dyadicGlobalMixedPrefixUnitMatrix M q) a) := by
  let B := mixedIntegerPowerMatrix
    (fun row => (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q
    (sortedMixedExponentBoxPrefix N)
  let rho := Tuple.sort (mixedPrefixLexKey N)
  have hmatrix :
      B.submatrix id rho =
        rankOnePowerMatrix 2 depth (lexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (dyadicGlobalMixedPrefixUnitMatrix M q) := by
    exact submatrix_mixedIntegerPowerMatrix_eq_two_rankOnePowerMatrix
      depth M q (sortedMixedExponentBoxPrefix N) rho
      (lexMixedPrefixBlock N) (fun k : Fin (N + 1) => (k : ℕ))
      (lexMixedPrefixDegree N) (by
        intro col
        apply Prod.ext <;> rfl)
  calc
    ((Equiv.Perm.sign rho : ℤ) : ℤ) * B.det =
        (B.submatrix id rho).det := (Matrix.det_permute' rho B).symm
    _ = (rankOnePowerMatrix 2 depth (lexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (dyadicGlobalMixedPrefixUnitMatrix M q)).det := by rw [hmatrix]
    _ = _ := det_rankOnePowerMatrix_eq_minPow_mul_truncatedAssignmentSum
      2 (dyadicGlobalMixedPrefixUnitMatrix M q) hdepth
      (lexMixedPrefixBlock_monotone N) (fun _ _ h => h) K

/-- The unit matrix left after the triadic structural powers are removed and
the global prefix is grouped by its second exponent coordinate. -/
def triadicGlobalMixedPrefixUnitMatrix
    {N : ℕ} (A : ℤ) (r : Fin N → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  fiberScaledConsecutivePowerMatrix
    (colexMixedPrefixBlock N) (colexMixedPrefixDegree N)
    (fun k row => A ^ ((row : ℕ) * (k : ℕ)))
    (fun _ row => r row)

/-- Concrete all-layer triadic cascade for the genuine first `N` mixed
exponents, symmetric to the dyadic theorem. -/
theorem sign_mul_det_globalMixedPrefix_three_eq_minPow_mul_sum_assignmentExcess
    {N : ℕ} {depth : Fin N → ℕ}
    (A : ℤ) (r : Fin N → ℤ) (hdepth : StrictAnti depth) :
    ((Equiv.Perm.sign (Tuple.sort (mixedPrefixColexKey N)) : ℤ) : ℤ) *
        (mixedIntegerPowerMatrix r
          (fun row => (3 : ℤ) ^ depth row * A ^ (row : ℕ))
          (sortedMixedExponentBoxPrefix N)).det =
      (3 : ℤ) ^ rankOneAssignmentCost depth
          ((fun k : Fin (N + 1) => (k : ℕ)) ∘ colexMixedPrefixBlock N)
          (Equiv.refl _) *
        ∑ a : RowBlockAssignment (colexMixedPrefixBlock N),
          (3 : ℤ) ^ rowBlockAssignmentExcess depth
              (fun k : Fin (N + 1) => (k : ℕ))
              (colexMixedPrefixBlock N) a *
            rowBlockMinorProduct (colexMixedPrefixBlock N)
              (triadicGlobalMixedPrefixUnitMatrix A r) a := by
  let B := mixedIntegerPowerMatrix r
    (fun row => (3 : ℤ) ^ depth row * A ^ (row : ℕ))
    (sortedMixedExponentBoxPrefix N)
  let rho := Tuple.sort (mixedPrefixColexKey N)
  have hmatrix :
      B.submatrix id rho =
        rankOnePowerMatrix 3 depth (colexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (triadicGlobalMixedPrefixUnitMatrix A r) := by
    exact submatrix_mixedIntegerPowerMatrix_eq_three_rankOnePowerMatrix
      depth A r (sortedMixedExponentBoxPrefix N) rho
      (colexMixedPrefixBlock N) (fun k : Fin (N + 1) => (k : ℕ))
      (colexMixedPrefixDegree N) (by
        intro col
        apply Prod.ext <;> rfl)
  calc
    ((Equiv.Perm.sign rho : ℤ) : ℤ) * B.det =
        (B.submatrix id rho).det := (Matrix.det_permute' rho B).symm
    _ = (rankOnePowerMatrix 3 depth (colexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (triadicGlobalMixedPrefixUnitMatrix A r)).det := by rw [hmatrix]
    _ = _ := det_rankOnePowerMatrix_eq_minPow_mul_sum_assignmentExcess
      3 (triadicGlobalMixedPrefixUnitMatrix A r) hdepth
      (colexMixedPrefixBlock_monotone N) (fun _ _ h => h)

/-- Exact finite-depth form of the concrete triadic cascade. -/
theorem sign_mul_det_globalMixedPrefix_three_eq_minPow_mul_truncatedAssignmentSum
    {N : ℕ} {depth : Fin N → ℕ}
    (A : ℤ) (r : Fin N → ℤ) (hdepth : StrictAnti depth) (K : ℕ) :
    ((Equiv.Perm.sign (Tuple.sort (mixedPrefixColexKey N)) : ℤ) : ℤ) *
        (mixedIntegerPowerMatrix r
          (fun row => (3 : ℤ) ^ depth row * A ^ (row : ℕ))
          (sortedMixedExponentBoxPrefix N)).det =
      (3 : ℤ) ^ rankOneAssignmentCost depth
          ((fun k : Fin (N + 1) => (k : ℕ)) ∘ colexMixedPrefixBlock N)
          (Equiv.refl _) *
        ((∑ a ∈ (Finset.univ.filter fun a :
              RowBlockAssignment (colexMixedPrefixBlock N) =>
              rowBlockAssignmentExcess depth
                (fun k : Fin (N + 1) => (k : ℕ))
                (colexMixedPrefixBlock N) a < K),
            (3 : ℤ) ^ rowBlockAssignmentExcess depth
                (fun k : Fin (N + 1) => (k : ℕ))
                (colexMixedPrefixBlock N) a *
              rowBlockMinorProduct (colexMixedPrefixBlock N)
                (triadicGlobalMixedPrefixUnitMatrix A r) a) +
          (3 : ℤ) ^ K *
            ∑ a ∈ (Finset.univ.filter fun a :
                RowBlockAssignment (colexMixedPrefixBlock N) =>
                K ≤ rowBlockAssignmentExcess depth
                  (fun k : Fin (N + 1) => (k : ℕ))
                  (colexMixedPrefixBlock N) a),
              (3 : ℤ) ^ (rowBlockAssignmentExcess depth
                    (fun k : Fin (N + 1) => (k : ℕ))
                    (colexMixedPrefixBlock N) a - K) *
                rowBlockMinorProduct (colexMixedPrefixBlock N)
                  (triadicGlobalMixedPrefixUnitMatrix A r) a) := by
  let B := mixedIntegerPowerMatrix r
    (fun row => (3 : ℤ) ^ depth row * A ^ (row : ℕ))
    (sortedMixedExponentBoxPrefix N)
  let rho := Tuple.sort (mixedPrefixColexKey N)
  have hmatrix :
      B.submatrix id rho =
        rankOnePowerMatrix 3 depth (colexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (triadicGlobalMixedPrefixUnitMatrix A r) := by
    exact submatrix_mixedIntegerPowerMatrix_eq_three_rankOnePowerMatrix
      depth A r (sortedMixedExponentBoxPrefix N) rho
      (colexMixedPrefixBlock N) (fun k : Fin (N + 1) => (k : ℕ))
      (colexMixedPrefixDegree N) (by
        intro col
        apply Prod.ext <;> rfl)
  calc
    ((Equiv.Perm.sign rho : ℤ) : ℤ) * B.det =
        (B.submatrix id rho).det := (Matrix.det_permute' rho B).symm
    _ = (rankOnePowerMatrix 3 depth (colexMixedPrefixBlock N)
          (fun k : Fin (N + 1) => (k : ℕ))
          (triadicGlobalMixedPrefixUnitMatrix A r)).det := by rw [hmatrix]
    _ = _ := det_rankOnePowerMatrix_eq_minPow_mul_truncatedAssignmentSum
      3 (triadicGlobalMixedPrefixUnitMatrix A r) hdepth
      (colexMixedPrefixBlock_monotone N) (fun _ _ h => h) K

/-! ## Direct structural-output specializations -/

theorem exists_three_mul_add_fin_two_of_not_dvd
    (n : ℕ) (hunit : ¬ 3 ∣ n) :
    ∃ z : ℕ, ∃ residue : Fin 2,
      n = 3 * z + (residue : ℕ) + 1 := by
  have hmod_ne : n % 3 ≠ 0 := by
    intro hzero
    exact hunit (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hmod_lt : n % 3 < 3 := Nat.mod_lt n (by omega)
  have hdiv := Nat.mod_add_div n 3
  let residue : Fin 2 := ⟨n % 3 - 1, by omega⟩
  refine ⟨n / 3, residue, ?_⟩
  dsimp [residue]
  omega

/-- Dyadic divisor for the concrete pair of mixed output rows
`2^depth M^row` and `3^depth A^row`, on the genuine first `N` mixed
exponents.  Oddness of `A` supplies every unit-node certificate. -/
theorem two_pow_globalMixedPrefix_structuralOutput_dvd_det
    {N : ℕ} {depth : Fin N → ℕ}
    (M A : ℕ) (hA : Odd A) (hdepth : StrictAnti depth) :
    (2 : ℤ) ^
        (rankOneAssignmentCost depth
            ((fun k : Fin (N + 1) => (k : ℕ)) ∘ lexMixedPrefixBlock N)
            (Equiv.refl _) +
          rowBlockOrderingExponent (lexMixedPrefixFiberSize N)
            twoUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix
        (fun row => (2 : ℤ) ^ depth row * (M : ℤ) ^ (row : ℕ))
        (fun row => (3 : ℤ) ^ depth row * (A : ℤ) ^ (row : ℕ))
        (sortedMixedExponentBoxPrefix N)).det := by
  let qNat : Fin N → ℕ :=
    fun row => 3 ^ depth row * A ^ (row : ℕ)
  have hqOdd : ∀ row, Odd (qNat row) := by
    intro row
    exact (show Odd (3 : ℕ) from ⟨1, by norm_num⟩).pow.mul
      (hA.pow)
  choose z hz using hqOdd
  have hdiv := two_pow_globalMixedPrefix_minCost_add_unit_dvd_det
    (N := N) (depth := depth) (M : ℤ)
    (fun row => (qNat row : ℤ)) z (by
      intro row
      exact_mod_cast hz row) hdepth
  simpa [qNat, Nat.cast_mul, Nat.cast_pow] using hdiv

/-- Triadic counterpart for the concrete mixed output rows.  The only local
hypothesis needed is that `M` is a unit modulo three. -/
theorem three_pow_globalMixedPrefix_structuralOutput_dvd_det
    {N : ℕ} {depth : Fin N → ℕ}
    (M A : ℕ) (hM : ¬ 3 ∣ M) (hdepth : StrictAnti depth) :
    (3 : ℤ) ^
        (rankOneAssignmentCost depth
            ((fun k : Fin (N + 1) => (k : ℕ)) ∘ colexMixedPrefixBlock N)
            (Equiv.refl _) +
          rowBlockOrderingExponent (colexMixedPrefixFiberSize N)
            threeUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix
        (fun row => (2 : ℤ) ^ depth row * (M : ℤ) ^ (row : ℕ))
        (fun row => (3 : ℤ) ^ depth row * (A : ℤ) ^ (row : ℕ))
        (sortedMixedExponentBoxPrefix N)).det := by
  let rNat : Fin N → ℕ :=
    fun row => 2 ^ depth row * M ^ (row : ℕ)
  have hrUnit : ∀ row, ¬ 3 ∣ rNat row := by
    intro row hdvd
    rcases Nat.prime_three.dvd_mul.mp hdvd with htwo | hMpow
    · exact (by norm_num : ¬ 3 ∣ 2)
        (Nat.prime_three.dvd_of_dvd_pow htwo)
    · exact hM (Nat.prime_three.dvd_of_dvd_pow hMpow)
  have hdecomp : ∀ row, ∃ z : ℕ, ∃ residue : Fin 2,
      rNat row = 3 * z + (residue : ℕ) + 1 := by
    intro row
    exact exists_three_mul_add_fin_two_of_not_dvd (rNat row) (hrUnit row)
  choose z residue hr using hdecomp
  have hdiv := three_pow_globalMixedPrefix_minCost_add_unit_dvd_det
    (N := N) (depth := depth) (A : ℤ)
    (fun row => (rNat row : ℤ)) z residue (by
      intro row
      exact_mod_cast hr row) hdepth
  simpa [rNat, Nat.cast_mul, Nat.cast_pow] using hdiv

end

end LeanProofs.TwoBaseIntegerExponent
