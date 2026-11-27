import New.Congruences.Lifting.LongGap
import New.Congruences.Lifting.SafeMoves

/-!
# Exponent bounds by cuts for paired sides of a Kummer chart: sparse thick letters, two sizes

This file concerns two paired sides `S`, `S'` over a Kummer chart, whose distinguished element is
written `E`. Letters `i : k.Letter` are permuted by Frobenius `k.letterFrob`. The jumps
`S.jumpSet i`, `S'.jumpSet i` lie in `[-η, η] ∪ ∓ε i • [β i, β i + V]` (`New.Lift.FitsWindows`),
with opposite far windows, and `V + 4η ≤ W`. A cut a bounded number of letters back from each
letter then gives the bound for the exponent in `New.Lift.Pairing.IsScaledCupCoboundary`; two
choices of cuts treat the cases of two sizes of far windows: one where the thick letters, those
with the larger size, are sparse, and one where they form any pattern.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.killsCokernel_of_isKillingCut`: at a cut `i`, `p ^ κ * E ^ s i`
  kills the cokernel.
* `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_hasSignBefore`,
  `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_isLongGap`: the stop of the walk at a
  plain cut and at a cut with a long gap.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_cut_windows`: the scheme.
  It derives the bound from a cut 1 to `2J + 1` letters back from each letter.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_sparse_thick`,
  `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_any_pattern`: two choices of
  cuts and constants.

Notions from other files:
* `New.Lift.KummerChart`: a ring `k.S` = Λ⟦z⟧ in A_inf, where Λ = `WittFq k.f` = W(𝔽_{p^f}), and a
  subgroup Γ' of Γ of index prime to p that fixes Λ. It is unramified (`IsUnramified`) if E = z + p
  and the ramification index `k.e` is 1. The number `k.differentBound` is 0 if `k.e = 1` and
  v_p(e) + 1 otherwise.
* `New.Lift.KummerChart.Coeffs`: a ring of coefficients O, a finite free Z_p-algebra with an element
  ζ such that ζ^{p^f−1} = 1; ζ cuts out the letters.
* `New.Lift.KummerChart.Letter`: the letters of a Kummer chart, that is, the multiplicative group of
  the field with p^f elements in the tilt of the ring of integers of C_p; `i.stepBack a` is the
  letter `a` Frobenius steps back.
* `New.Lift.KummerChart.PairingSide`, `New.Lift.KummerChart.PairingSide.KillsCokernel`: one side
  of a pairing: lattices Y and C (`paramLattice`), an O-linear map `cocycleMap` from C to the
  crystalline cocycles Z_f(Y), and for each letter a finite set of integers that contains 0, the
  jumps. The extension `extensionLattice` of C by Y maps by `projTrivial` to `trivialLattice`, the
  lattice C with trivial action. `KillsCokernel`: `p ^ κ * E ^ s` multiplies the part of A_inf ⊗ C
  at a letter into the image of the standard module of level 0 of the extension.
* `New.Lift.KummerChart.PairingSide.pointsOver`: `S.pointsOver c i e o d` is the set of the vectors
  `x` of the Kisin module of the extension, with all φ^a E inverted, that lie over `p ^ e c` at `i`,
  have the orders `o` and have the depth `d`: every `g • x - x` with `g` in Γ' has exponents `d`.
* `New.Lift.raisedOrdersAtZero`: the orders `raisedOrdersAtZero t` are `-u` on the jump `u`, raised
  by `t` at E. The vectors with orders `raisedOrdersAtZero (-s)` have a pole of order at most `s` at
  E.
* `New.Lift.Pairing.IsSafeMoveFst`, `New.Lift.Pairing.IsSafeMoveSnd`: one side moves by a vector
  while the other rests at a point `x`. The move is safe for `κ` if, for all `g` in Γ', `p ^ κ`
  times the pairing of `g • x - x` with the move (for the second side, with `g` times the move) lies
  in the image of W(𝔪^♭).

## Relation to the literature

Take crystalline lattices with weights in short windows near 0 and near large weights, in the cases
of no small negative weight, two sizes, or sparse large weights. For these, an explicit power of p,
independent of the rank, makes crystalline classes cup to zero with those of congruent dual
lattices. This bounds the loss at the places above p in the Selmer bound. The case of small weights
and a rank-free factorial torsion bound by Sen operators are known in the literature. Related work:
Gao–Liu, Integral filtered Sen theory and applications, 2024; Iovita–Marmora, Continuity of the
finite Bloch–Kato cohomology, 2015; Y. Min, Congruences of first syntomic cohomology groups, 2026.
-/

namespace New.Lift.KummerChart

section SparseThickLetters

open Period Finset

variable {p : ℕ} [j : ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ}

/-- The letter `i.stepBack l` is the nearest cut before `i`. -/
structure Letter.IsNearestCut (i : k.Letter) (cut : k.Letter → Prop) (l : ℕ) : Prop where
  /-- The cut is at least one step back. -/
  pos : 0 < l
  /-- The letter `l` steps back is a cut. -/
  cut_stepBack : cut (i.stepBack l)
  /-- No letter strictly between it and `i` is a cut. -/
  not_cut : ∀ a ∈ Set.Ioo 0 l, ¬cut (i.stepBack a)

/-- Each of the `l` letters `i.stepBack a` with `a < l` has the sign `ρ`, or its far window
`[β, β + V]` ends at or below `η`. -/
def Letter.HasSignBefore (i : k.Letter) (ε : k.Letter → ℤˣ) (β : k.Letter → ℕ) (η V l : ℕ)
    (ρ : ℤˣ) : Prop :=
  ∀ a < l, ε (i.stepBack a) = ρ ∨ β (i.stepBack a) + V ≤ η

/-- A long gap at the pivot `i.stepBack t`, one of the `l` letters after `i.stepBack l` up to `i`:
the far window of the pivot starts far out, and the other letters have the opposite sign or small
far windows. The number `ω` bounds the low window and the far windows before the pivot. -/
structure Letter.IsLongGap (i : k.Letter) (ε : k.Letter → ℤˣ) (s β : k.Letter → ℕ)
    (η V J s₀ ω l t : ℕ) : Prop where
  /-- The chart is unramified. -/
  isUnramified : k.IsUnramified
  /-- The prime is at least `5`. -/
  five_le : 5 ≤ p
  /-- The letter `l` steps back has shift `0`. -/
  shift_eq_zero : s (i.stepBack l) = 0
  /-- The pivot is `J + 1` letters after `i.stepBack l`. -/
  pivot_add : t + (J + 1) = l
  /-- The far window of the pivot starts beyond `s₀ + ω (1 + p + ⋯ + p ^ J)`. -/
  lt_far_pivot : s₀ + ω * ∑ a ∈ range (J + 1), p ^ a < β (i.stepBack t)
  /-- The other letters have the opposite sign, or a far window that ends at or below `η`. -/
  sign_ne_or_far_le : ∀ a < l, a ≠ t → ε (i.stepBack a) ≠ ε (i.stepBack t) ∨ β (i.stepBack a) + V ≤
    η
  /-- The low window ends at or below `ω`. -/
  low_le : η ≤ ω
  /-- The far windows of the letters before the pivot end at or below `ω`. -/
  far_le : ∀ a < l, t < a → β (i.stepBack a) + V ≤ ω

/-- None of the `J` letters after `i` satisfies `T`. -/
def Letter.HasThinSuccessors (i : k.Letter) (T : k.Letter → Prop) (J : ℕ) : Prop :=
  ∀ t ≥ 1, t ≤ J → ¬T ((k.letterFrob ^ t) i)

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
If `i.stepBack r` satisfies `T` and does not have thin successors, that is, one of the `J` letters
after it satisfies `T` too, then `i.stepBack (r + (J + 1))` has thin successors: none of the `J`
letters before `i.stepBack r` satisfies `T`. -/
lemma Letter.hasThinSuccessors_stepBack_add {T : k.Letter → Prop} {J : ℕ}
    (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (i : k.Letter) (r : ℕ) (h_after : ¬(i.stepBack r).HasThinSuccessors T J)
    (h_thick : T (i.stepBack r)) :
    (i.stepBack (r + (J + 1))).HasThinSuccessors T J := by
  refine fun n hn_pos hn h_before ↦ h_after fun t ht_pos ht ↦ ?_
  set j : k.Letter := (k.letterFrob ^ n) (i.stepBack (r + (J + 1))) with hj
  have h_letters : (k.letterFrob ^ (J + 1 - n)) j = i.stepBack r := by
    simp [hj, pow_add, pow_sub _ (hn.trans J.le_succ)]
  have h_not : ¬T ((k.letterFrob ^ (J + 1 - n + t)) j) :=
    h_sparse j _ (by grind) t (mem_Icc.2 ⟨ht_pos, ht⟩) h_before (by rwa [h_letters])
  rwa [add_comm, pow_add, Equiv.Perm.mul_apply, h_letters] at h_not

/-- The two kinds of letters `i` at which `p ^ κ * E ^ s i` is shown to kill the cokernel. -/
inductive Letter.IsKillingCut (i : k.Letter) (s β : k.Letter → ℕ) (W J G s₀ κ : ℕ) : Prop
  /-- The shift is `0` and the next `J` letters have `β + W ≤ G`. -/
  | of_thin (shift_eq_zero : s i = 0)
      (next_le : ∀ t ∈ Icc 1 J, β ((k.letterFrob ^ t) i) + W ≤ G)
  /-- The chart is unramified, `p ≥ 5`, and the shift lies in `[s₀ - κ, β i)`. -/
  | of_isUnramified (shift_lt : s i < β i) (isUnramified : k.IsUnramified) (five_le : 5 ≤ p)
      (le_add_shift : s₀ ≤ κ + s i)

/-- The size conditions of the scheme of cuts, for shifts `s i`, far windows that start at `β i`
and a width `W`. The shifted far windows end at or below `2 b`, and `G` bounds `β + W` at the `J`
letters after a thin cut (`Letter.IsKillingCut.of_thin`). The number `n` bounds `G / (p - 1)`, and
`s₀` bounds `(β i + W) / (p - 3)` if `p ≥ 5`. The number `X` is the cost of one letter or level,
`δ` the cost of the depth `2 b`, and `p ^ κ` is the killer at a cut. Here `k.differentBound` is `0`
if the ramification index `k.e` is `1`, and `v_p(k.e) + 1` otherwise. -/
structure CutSizes (k : KummerChart Γ) (s β : k.Letter → ℕ) (W X δ κ b n J s₀ G : ℕ) : Prop where
  /-- The unit of cost `X` is large against `n`, `log_p (2 b)`, `W` and `G`. -/
  le_cost : n + p.log (2 * b) + (J + 1 + k.differentBound) * W + k.differentBound * G ≤ X
  /-- The exponent `κ` exceeds `12 ((J + 1) X + δ)`. -/
  cost_lt : 12 * ((J + 1) * X + δ) < κ
  /-- The depth `2 b` times the ramification index is at most `p ^ (J + 1) δ`. -/
  ramification_mul_le : k.e * (2 * b) ≤ p ^ (J + 1) * δ
  /-- The ramification index is at most `p ^ (J + 1) / 8`. -/
  ramification_le : 8 * k.e ≤ p ^ (J + 1)
  /-- The shifted far windows end at or below `2 b`. -/
  far_le : ∀ i : k.Letter, β i + s i + W ≤ 2 * b
  /-- The bound `G` is at most `(p - 1) n`. -/
  thin_le : G ≤ (p - 1) * n
  /-- For `p ≥ 5` the far windows end at or below `(p - 3) s₀`. -/
  far_le_of_five_le : 5 ≤ p → ∀ i : k.Letter, β i + W ≤ (p - 3) * s₀

/-- If `i` satisfies `i.IsKillingCut s β W J G s₀ κ`, then either the shift `s i` is `0`, or
`s i < β i` and `k.differentBound = 0`. -/
lemma Letter.IsKillingCut.shift_eq_zero_or_lt {i : k.Letter} {s β : k.Letter → ℕ} {W J G s₀ κ : ℕ}
    (h_cut : i.IsKillingCut s β W J G s₀ κ) : s i = 0 ∨ s i < β i ∧ k.differentBound = 0 := by
  obtain h_zero | ⟨h_lt, ⟨-, -, h_diff⟩⟩ := h_cut
  exacts [.inl h_zero, .inr ⟨h_lt, h_diff⟩]

/-- The exponents of the standard point at a cut with shift `s`, where the cut before is `l` steps
back. The point has the exponents `raisedOrdersAtZero (-s)` (`-u`, lowered by `s` at the level `0`)
and the depth `standardDepth s η (l + 1)` (`-u`, raised by `s` at the level `0` and by `η` at the
levels up to `l`). This depth improves the exponents: they become the depth where they were
positive, and the minimum of the depth and `0` elsewhere (`JumpLattice.improvedOrders`). -/
def cutOrders (s η l : ℕ) : ℕ → ℤ → ℤ :=
  JumpLattice.improvedOrders (raisedOrdersAtZero (-s)) (PairingSide.standardDepth s η (l + 1))

/-- The depth of the point at which a side rests when the walk meets a cut with a long gap: `r` at
the level `t` of the pivot, `1` at the other levels below `l`, and `-u` beyond. -/
def longGapDepth (l t r a : ℕ) (u : ℤ) : ℤ :=
  if a = t then r else if a < l then 1 else -u

/-- The steps that may be needed to deepen a point at `i` of a side whose far windows have the
signs `σ`: two windows, around `0` and `∓ β`, at each of the first `2 J + 2` levels. -/
noncomputable def Letter.windowSteps (i : k.Letter) (σ : k.Letter → ℤˣ) (s β : k.Letter → ℕ)
    (W J : ℕ) : Finset (Σ _ : ℕ, ℤ) :=
  (range (2 * J + 2)).sigma fun a ↦ twoWindows ((if a = 0 then s i else 0) + W)
    ((if σ (i.stepBack a) = 1 then -1 else 1) * β (i.stepBack a))

/-- The steps `i.windowSteps σ s β W J` are the pairs `(a, m)` of a level `a < 2 J + 2` and an
integer `m` near `0` or near `-σ j • β j`, where `j = i.stepBack a` and `σ j` is any sign; near
means within `s i + W` at the level `0` and within `W` at the others. The step `(a, m)` costs
`k.cost a m = v_p(m) + d + 3 a`, with `v_p(0) = 0` and `d = k.differentBound`, which is `0` if the
ramification index `k.e` is `1` and `v_p(k.e) + 1` otherwise. Assume the size conditions `CutSizes`:
they make the cost `X` of a level large against `n`, `log_p (2 b)`, `W` and `G`, make `κ` exceed
`12 ((J + 1) X + δ)`, and bound every `β j + s j + W` by `2 b`. With `W ≥ 4` and `s i + W ≤ p n`,
and if `s i` or `d` is `0`, the steps then cost at most `24 κ - 4 δ` together. -/
lemma CutSizes.sum_cost_windowSteps_le {σ : k.Letter → ℤˣ} {s β : k.Letter → ℕ}
    {W X δ κ b n J s₀ G : ℕ} (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) (hW : 4 ≤ W)
    {i : k.Letter} (h_shift : s i + W ≤ p * n) (h_zero : s i = 0 ∨ k.differentBound = 0) :
    κ + 4 * δ + ∑ q ∈ i.windowSteps σ s β W J, k.cost q.1 q.2 ≤ 25 * κ := by
  -- By `sum_twoWindows_le` each of the `2 J + 2` levels costs at most `30 X`.
  have h_level (a : ℕ) (ha : a ∈ range (2 * J + 2)) :
      ∑ m ∈ twoWindows ((if a = 0 then s i else 0) + W)
        ((if σ (i.stepBack a) = 1 then -1 else 1) * β (i.stepBack a)), k.cost a m ≤ 30 * X := by
    set centre : ℤ := (if σ (i.stepBack a) = 1 then -1 else 1) * β (i.stepBack a) with h_centre
    -- The shift `r` occurs only at the level `0`, where it is `0` or the steps cost only `v_p(m)`.
    obtain ⟨r, hr, hr_le, hr_zero⟩ : ∃ r : ℕ, (if a = 0 then s i else 0) = r ∧
        r ≤ min (s i) (s (i.stepBack a)) ∧ (r = 0 ∨ k.differentBound + 3 * a = 0) := by
      obtain rfl | ha_pos := a.eq_zero_or_pos
      · exact ⟨s i, rfl, (min_self (s i)).ge, h_zero⟩
      · exact ⟨0, ite_eq_right ha_pos.ne', Nat.zero_le _, .inl rfl⟩
    have h_far : β (i.stepBack a) + s (i.stepBack a) + W ≤ 2 * b := h_sizes.far_le _
    have h_abs : |centre| = β (i.stepBack a) := by simp [h_centre, apply_ite]
    have h_rest : (4 * (r + W) + 2) * (k.differentBound + 3 * a) ≤
        5 * W * (6 * (J + 1 + k.differentBound)) := by
      rw [mem_range] at ha
      obtain rfl | h_free := hr_zero
      · exact Nat.mul_le_mul (by omega) (by omega)
      · simp [h_free]
    have h_width : r + W ≤ p * n := by omega
    have h_range : |centre| + (r + W : ℕ) ≤ (2 * b : ℕ) := by omega
    rw [hr]
    calc _ ≤ 8 * n + 2 * p.log (2 * b) + (4 * (r + W) + 2) * (k.differentBound + 3 * a) :=
          sum_twoWindows_le (Fact.out : p.Prime) n (2 * b) h_width h_range
      _ ≤ 30 * X := by linarith [h_sizes.le_cost, Nat.zero_le (k.differentBound * G)]
  have h_sum : ∑ q ∈ i.windowSteps σ s β W J, k.cost q.1 q.2 ≤ (2 * J + 2) * (30 * X) := by
    simpa [Letter.windowSteps, sum_sigma] using sum_le_card_nsmul _ _ _ h_level
  linarith [h_sizes.cost_lt]

/-- A set that lies in the union of the low window `[-η, η]` and a far window `± [b, b + V]` is
bounded above by `b + W` if `V + η ≤ W`. -/
lemma _root_.New.Lift.FitsWindows.le_add {η b V W : ℕ} {ρ : ℤˣ} {U : Finset ℤ}
    (hU : FitsWindows η ρ b V U) (hW : V + η ≤ W) {u : ℤ} (hu : u ∈ U) : u ≤ b + W := by
  obtain h_low | h_pos | h_neg := hU u hu <;> omega

namespace PairingSide

variable {O : k.Coeffs} {S S' : PairingSide O}

/-- Let `S` be a side whose jumps at each letter `i` are at most `β i + W`. Let the size conditions
`CutSizes` hold: `β + s + W ≤ 2 b` for the shifts `s`, the cost `X` is large against `n`, `W` and
`G`, with `G ≤ (p - 1) n`, the depth `2 b` costs `δ` over `J + 1` letters, and
`κ > 12 ((J + 1) X + δ)` (`s₀` plays no part). If `β + W ≤ G` at the `J` letters after `i`, then
`p ^ κ` kills the cokernel at `i`: it multiplies `A_inf ⊗ C`, for the lattice
`C = S.paramLattice`, into the image of the extension of level `0`. -/
lemma killsCokernel_zero_of_next_le {s β : k.Letter → ℕ} {W X δ κ b n J s₀ G : ℕ}
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G)
    (h_jump : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ≤ β i + W) {i : k.Letter}
    (h_next : ∀ t ∈ Icc 1 J, β ((k.letterFrob ^ t) i) + W ≤ G) : S.KillsCokernel i κ 0 := by
  -- All jumps are at most `2 b` and those at the `J` letters after `i` are at most `G`. The size
  -- conditions bound the three terms of the cokernel bound with weights by multiples of `X`, `δ`.
  have h_jump_all (i' : k.Letter) (u : ℤ) (hu : u ∈ S.jumpSet i') : u ≤ (2 * b : ℕ) := by
    have h_far : β i' + s i' + W ≤ 2 * b := h_sizes.far_le i'
    have h_le : u ≤ β i' + W := h_jump i' u hu
    omega
  have h_jump_next : ∀ t ∈ Icc 1 J, ∀ u ∈ S.jumpSet ((k.letterFrob ^ t) i), u ≤ G :=
    fun t ht u hu ↦ (h_jump _ u hu).trans (mod_cast h_next t ht)
  refine killsCokernel_zero_of_jumps_le h_jump_all h_jump_next h_sizes.ramification_le ?_
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h_step : k.differentBound * G + n ≤ X := by
    linarith [h_sizes.le_cost, Nat.zero_le ((J + 1 + k.differentBound) * W)]
  have h_different : (k.differentBound * G : ℝ) ≤ X := mod_cast le_of_add_le_left h_step
  have h_thin : (G : ℝ) / (p - 1) ≤ X := by
    have h_nat : G ≤ (p - 1) * X :=
      h_sizes.thin_le.trans (Nat.mul_le_mul_left _ (le_of_add_le_right h_step))
    rw [div_le_iff₀' (sub_pos.2 (mod_cast hp)), ← Nat.cast_pred (by omega)]
    exact_mod_cast h_nat
  have h_depth : (k.e * (2 * b : ℕ) : ℝ) / p ^ (J + 1) ≤ δ :=
    (div_le_iff₀' (by positivity)).2 (mod_cast h_sizes.ramification_mul_le)
  have h_total : 2 * J * X + (2 * J + 4) * X + 8 * δ ≤ κ := by
    linarith [h_sizes.cost_lt, Nat.zero_le (J * X)]
  calc _ = (2 * J * (k.differentBound * G) : ℝ) + (2 * J + 4) * (G / (p - 1)) +
          8 * (k.e * (2 * b : ℕ) / p ^ (J + 1)) := by ring
    _ ≤ 2 * J * X + (2 * J + 4) * X + 8 * δ := by gcongr
    _ ≤ κ := mod_cast h_total

/-- The cokernel at a cut of the side `S`. Let its jumps at each letter `i` be at most `β i + W`,
for shifts `s i`, and let the size conditions `CutSizes` hold. Then `p ^ κ * E ^ s i`, with `E` the
distinguished element, kills the cokernel of the extension over `S.paramLattice` at every letter `i`
with `IsKillingCut`: `s i = 0` and the next `J` letters have `β + W ≤ G`, or the chart is
unramified, `p ≥ 5` and `s₀ - κ ≤ s i < β i`. -/
lemma killsCokernel_of_isKillingCut {s β : k.Letter → ℕ} {W X δ κ b n J s₀ G : ℕ}
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G)
    (h_jump : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ≤ β i + W) {i : k.Letter}
    (h_cut : i.IsKillingCut s β W J G s₀ κ) : S.KillsCokernel i κ (s i) := by
  cases h_cut with
  | of_thin hs_zero h_next =>
    simpa only [hs_zero] using killsCokernel_zero_of_next_le h_sizes h_jump h_next
  | of_isUnramified _ hk hp hs₀ =>
    have h_bound (i' : k.Letter) : β i' + W ≤ (p - 3) * (κ + s i) :=
      (h_sizes.far_le_of_five_le hp i').trans (Nat.mul_le_mul_left (p - 3) hs₀)
    exact killsCokernel_of_isUnramified κ (s i)
      (fun i' u hu ↦ (h_jump i' u hu).trans (mod_cast h_bound i')) hk hp

/-- The points `S.pointsOver c i e o₁ o₀` are the vectors of the extension of `C = S.paramLattice`
at the letter `i` over `p ^ e c` that have the orders `o₁` (divisibility by `t ^ (o₁ a u)` at
`φ^a E` on the jump `u`) and the depth `o₀` (the orders of all `g • x - x`, `g` in `Γ'`). Let `x` be
one. Let `steps` contain every pair `(a, m)` with `o₀ a u ≤ m < o a u` for a jump `u` at
`i.stepBack a`, the letter `a` steps before `i`, and let `e'` be at least `e` plus the costs
`k.cost a m = v_p(m) + k.differentBound + 3 a` of the steps. Then there is a point over `p ^ e' c`
of depth `o` with any orders `o'` that are at most `o` where `o₁` is positive and at most `min o 0`
elsewhere. -/
lemma pointsOver_nonempty_of_sum_cost_le {c : S.paramLattice} {i : k.Letter} {e e' : ℕ}
    {o₁ o₀ o o' : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient} (hx : x ∈ S.pointsOver c i e o₁ o₀)
    (steps : Finset (Σ _ : ℕ, ℤ)) (h_cost : e + ∑ q ∈ steps, k.cost q.1 q.2 ≤ e')
    (h_steps : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ m : ℤ, o₀ a u ≤ m → m < o a u →
      ⟨a, m⟩ ∈ steps)
    (h_exponent : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a),
      o' a u ≤ JumpLattice.improvedOrders o₁ o a u) :
    (S.pointsOver c i e' o' o).Nonempty := by
  exact (pointsOver_nonempty_of_costs hx steps h_steps h_cost).mono fun y hy ↦
    mem_pointsOver_of_le hy h_exponent fun _ _ _ ↦ le_rfl

/-- The standard point of a side `S` at a cut `i`. Let the jumps of `S` lie in `[-η, η]` and in the
far windows `σ j • [β j, β j + V]` of signs `σ j`. Let `η ≥ 1`, `V + 4 η ≤ W`, let the shifts `s`
have `s i + W ≤ p n`, let the size conditions `CutSizes` hold, let the cut be of a kind at which the
cokernel is killed, and let `l ≤ 2 J + 1` be its distance to the cut before. Then for `c` in
`S.paramLattice` the extension has a point at `i` over `p ^ (25 κ) c` with the orders
`cutOrders (s i) η l` and with depth `standardDepth (s i) η (l + 1)`: `-u`, raised by `s i` at the
level `0` and by `η` at the levels up to `l`. -/
lemma pointsOver_cutOrders_nonempty {s β : k.Letter → ℕ} {η V W X δ κ b n J s₀ G : ℕ}
    {σ : k.Letter → ℤˣ} (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hU : ∀ i : k.Letter, FitsWindows η (σ i) (β i) V (S.jumpSet i))
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) {i : k.Letter} (h_shift : s i + W ≤ p * n)
    (h_cut : i.IsKillingCut s β W J G s₀ κ) {l : ℕ} (hl : l ≤ 2 * J + 1) (c : S.paramLattice) :
    (S.pointsOver c i (25 * κ) (cutOrders (s i) η l)
      (standardDepth (s i) η (l + 1))).Nonempty := by
  obtain ⟨x, hx⟩ : (S.pointsOver c i κ (raisedOrdersAtZero (-s i))
    (raisedOrdersAtZero (-s i))).Nonempty :=
    pointsOver_nonempty_of_killsCokernel
      (killsCokernel_of_isKillingCut h_sizes (fun j u ↦ (hU j).le_add (by omega)) h_cut) c
  have h_cost : κ + 4 * δ + ∑ q ∈ i.windowSteps σ s β W J, cost q.1 q.2 ≤ 25 * κ :=
    h_sizes.sum_cost_windowSteps_le (by omega) h_shift
      (h_cut.shift_eq_zero_or_lt.imp_right And.right)
  refine pointsOver_nonempty_of_costs hx (i.windowSteps σ s β W J) (fun a u hu m hm_ge hm_lt ↦ ?_)
    (by omega)
  -- The steps lie at the levels up to `l`, within `s i + η` or `η` of `-u`.
  simp only [Letter.windowSteps, mem_sigma, mem_range, mem_union, mem_Icc, ← Units.val_eq_one]
  grind [raisedOrdersAtZero, standardDepth, hU (i.stepBack a) u hu]

/-- Let the jumps of the side `S` at the letter `i` lie in `[-η, η]` and in the far window
`σ • [β i, β i + V]`, and let `i` be a cut of a kind at which the cokernel is killed, with shift
`s i`. Let `x` be a standard point at `i` over `p ^ e c`: the depth (the orders of all `g • x - x`)
is `standardDepth (s i) η (l + 1)`, that is `-u` raised by `s i` at the level `0` and by `η` at the
levels up to `l`, and the orders `cutOrders (s i) η l` are `-u - s i` at the level `0` and `-u`
above, improved by this depth. As no jump lies in `[-s i, -η)`, the point `x` has the orders
`raisedOrdersAtZero (-η)`, a pole of order at most `η` at the distinguished element `E`, and it has
the depth `plainDepth (s i) η l η` that a cut without long gap asks. -/
lemma mem_pointsOver_plainDepth_of_cutOrders {s β : k.Letter → ℕ} {η V W κ J s₀ G e : ℕ}
    {σ : ℤˣ} {i : k.Letter} {l : ℕ} {c : S.paramLattice} {x : S.extensionLattice.Ambient}
    (hU : FitsWindows η σ (β i) V (S.jumpSet i)) (h_cut : i.IsKillingCut s β W J G s₀ κ)
    (hx : x ∈ S.pointsOver c i e (cutOrders (s i) η l) (standardDepth (s i) η (l + 1))) :
    x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) (plainDepth (s i) η l η) := by
  have h_shift : s i = 0 ∨ s i < β i := h_cut.shift_eq_zero_or_lt.imp_right And.left
  have h_gap : ∀ u ∈ S.jumpSet i, -(s i : ℤ) ≤ u → -(η : ℤ) ≤ u := by
    intro u hu hu_ge
    obtain h_low | h_pos | h_neg := low_or_far_of_fitsWindows hU hu <;> omega
  have h_pole : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) (standardDepth (s i) η (l + 1)) :=
    mem_pointsOver_raisedOrdersAtZero_of_gap hx (Int.natCast_nonneg η) h_gap
      (fun a u _ ↦ by grind [cutOrders, raisedOrdersAtZero, standardDepth])
      fun a u _ ↦ by grind [raisedOrdersAtZero, standardDepth]
  refine mem_pointsOver_of_le h_pole (fun a u _ ↦ le_rfl) fun a u _ ↦ ?_
  simp only [plainDepth, standardDepth]
  omega

/-- The stop at `i` when the nearest cut before it, `i.stepBack l` (`l` letters back), is followed
by a long gap. Let `S` have its jumps in `[-η, η]` and in far windows of width `V` at `β` with signs
`σ`. The long gap at the pivot `i.stepBack t`, `J + 1` letters after the cut, means that its far
window starts beyond `s₀ + ω (1 + ⋯ + p ^ J)`, where `ω` bounds the windows before it; its signs
`ε` are not tied to `σ`. Let `σ` be `-1` at the pivot, and let the jumps at the other letters after
the cut be at least `-η`. Let the size conditions hold: `2 b` bounds the shifted far windows
`β + s + W`, `G` the windows of the `J` letters after a thin cut, `n` bounds `G / (p - 1)`, and
`κ` is large against the costs. Let `η ≥ 1`, `V + 4 η ≤ W`, `s i + W ≤ p n`, `l ≤ 2 J + 1`, and let
the cut be of a kind at which the cokernel is killed. Then `S` has a point over `p ^ (25 κ) c` at
which it can rest (a stop): its orders `stopOrders η l` are `max 0 (-u - η)` below the level `l` and
`-u` from `l` on, and its depth `longGapDepth l t (2 b)` is `2 b` at the level `t`, `1` at the
others below `l` and `-u` from `l` on. -/
lemma pointsOver_longGapDepth_nonempty {ε : k.Letter → ℤˣ} {s β : k.Letter → ℕ}
    {η V W X δ κ b n J s₀ G ω : ℕ} {σ : k.Letter → ℤˣ} (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hU : ∀ i : k.Letter, FitsWindows η (σ i) (β i) V (S.jumpSet i))
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) {i : k.Letter} (h_shift : s i + W ≤ p * n)
    {l t : ℕ} (hl : l ≤ 2 * J + 1) (h_cut : (i.stepBack l).IsKillingCut s β W J G s₀ κ)
    (h_gap : i.IsLongGap ε s β η V J s₀ ω l t) (h_pivot : σ (i.stepBack t) = -1)
    (h_up : ∀ a : ℕ, a < l → a ≠ t → ∀ u ∈ S.jumpSet (i.stepBack a), -η ≤ u) (c : S.paramLattice) :
    (S.pointsOver c i (25 * κ) (stopOrders η l) (longGapDepth l t (2 * b))).Nonempty := by
  -- The long gap gives a point over `p ^ (κ + 4 δ)` of depth `2 b` at the pivot. Carry it to `i` by
  -- `φ ^ t`, and raise its depth from `0` to `1` at the levels between `t` and `l`.
  obtain ⟨hk, hp, hs_cut, rfl, h_long, -, h_low, h_thin⟩ := h_gap
  obtain ⟨he_one, h_free⟩ := hk.right
  have h_jump (j : k.Letter) (u : ℤ) (hu : u ∈ S.jumpSet j) : u ≤ β j + W :=
    (hU j).le_add (by omega) hu
  have h_back (a : ℕ) : (i.stepBack t).stepBack a = i.stepBack (t + a) := by simp [pow_add]
  have h_kill_cut : S.KillsCokernel ((i.stepBack t).stepBack (J + 1)) κ 0 := by
    simpa only [h_back, hs_cut] using killsCokernel_of_isKillingCut h_sizes h_jump h_cut
  have h_kill_pivot : S.KillsCokernel (i.stepBack t) 0 s₀ :=
    killsCokernel_of_isUnramified 0 s₀ (fun j u hu ↦ (h_jump j u hu).trans
      (by simpa using mod_cast h_sizes.far_le_of_five_le hp j)) hk hp
  have h_small (a : ℕ) (ha : a < J + 1) : ∀ u ∈ S.jumpSet ((i.stepBack t).stepBack a), u ≤ ω := by
    intro u hu
    obtain rfl | ha_pos := a.eq_zero_or_pos
    · exact (jump_le_of_fitsWindows (hU _) (.inl h_pivot) u hu).trans (mod_cast h_low)
    · rw [h_back] at hu
      have h_far_le : β (i.stepBack (t + a)) + V ≤ ω := h_thin (t + a) (by omega) (by omega)
      obtain h_low_jump | h_pos | h_neg := low_or_far_of_fitsWindows (hU _) hu <;> omega
  have h_far_pivot : β (i.stepBack t) + s (i.stepBack t) + W ≤ 2 * b := h_sizes.far_le _
  have h_three : 3 ≤ p ^ (J + 1) := (by omega : 3 ≤ p).trans (Nat.le_self_pow J.succ_ne_zero p)
  have h_depth : 2 * b ≤ p ^ (J + 1) * δ := by simpa [he_one] using h_sizes.ramification_mul_le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, s₀ + ω * ∑ a ∈ range (J + 1), p ^ a = N := ⟨_, rfl⟩
  rw [hN] at h_long
  obtain ⟨x, hx⟩ : Set.Nonempty (S.pointsOver c (i.stepBack t) (κ + 4 * δ)
      (JumpLattice.shiftedStdOrders (J + 1) fun u ↦ if u < -N then (2 * b : ℕ) else 0)
      (JumpLattice.shiftedStdOrders (J + 1) fun _ ↦ (2 * b : ℕ))) :=
    pointsOver_nonempty_of_long_gap hk h_three h_depth h_kill_cut h_kill_pivot h_small hN
      (by omega) c
  have h_cost : κ + 4 * δ + ∑ q ∈ i.windowSteps σ s β W J, cost q.1 q.2 ≤ 25 * κ :=
    h_sizes.sum_cost_windowSteps_le (by omega) h_shift (.inr h_free)
  -- The point `φ ^ t • x` at `i` has the exponents and depth of `x`, shifted up by `t` levels.
  refine pointsOver_nonempty_of_sum_cost_le (phi_pow_smul_mem_pointsOver (l := t) hx)
    (i.windowSteps σ s β W J) h_cost (fun a u _ m hm_ge hm_lt ↦ ?_) fun a u hu ↦ ?_
  · -- The only steps are `(a, 0)` with `t < a < l`.
    simp only [Letter.windowSteps, JumpLattice.shiftedOrders, JumpLattice.shiftedStdOrders,
      stdOrders,
      longGapDepth, mem_sigma, mem_range, mem_union, mem_Icc] at hm_ge hm_lt ⊢
    omega
  · -- At the pivot no jump lies in `[-N, -η)`; at the other levels below `l` the side is up.
    have h_window : a = t → -η ≤ u ∨ β (i.stepBack t) ≤ -u ∧ -u ≤ β (i.stepBack t) + V := by
      rintro rfl
      obtain h_low | h_pos | h_neg := low_or_far_of_fitsWindows (hU _) hu <;> omega
    have h_up_level : a < t + (J + 1) → a ≠ t → -η ≤ u := fun ha hat ↦ h_up a ha hat u hu
    simp only [stopOrders, JumpLattice.improvedOrders, JumpLattice.shiftedOrders,
      JumpLattice.shiftedStdOrders, stdOrders, longGapDepth]
    omega

/-- The inequality that makes a move safe at a cut with a long gap. The move has the minimum of the
exponents `cutOrders s η l` and of `cutOrders 0 η l₀` shifted up by `l` levels (`0` below `l`).
The side at rest has the depth `longGapDepth l t r`, where `t < l` and `0 < r`. At the level `a` let
`u ≤ η` if `t ≠ a < l` and `u < η + r` if `a = t`. Then for every `v` the exponent at `u` and the
depth at `v` add up to at least `ruleBound l 0 a (u + v)`, which is `1` for `a < l` and `-(u + v)`
for `a ≥ l`. -/
lemma ruleBound_le_inf_add_longGapDepth {η l l₀ t r s a : ℕ} {u : ℤ} (ht : t < l) (hr : 0 < r)
    (h_down : a < l → a ≠ t → u ≤ η) (h_pivot : a = t → u < η + r) (v : ℤ) :
    ruleBound l 0 a (u + v) ≤
      (cutOrders s η l ⊓ JumpLattice.shiftedOrders l 0 (cutOrders 0 η l₀)) a u +
        longGapDepth l t r a v := by
  simp only [Pi.inf_apply, ruleBound, cutOrders, JumpLattice.improvedOrders,
    JumpLattice.shiftedOrders, raisedOrdersAtZero, standardDepth, longGapDepth]
  omega

/-- Let the side `R`, which moves first to a stop and rests there, have jumps in `[-η, η]` and in
far windows `σ j • [β j, β j + V]`, and let the other side `R'` have those of signs `-σ`. Let
`η ≥ 1`, `V + 4 η ≤ W`, `s i + W ≤ p n`, let the size conditions hold, and let the letter
`l ≤ 2 J + 1` steps before `i` be a cut at which the cokernel is killed, followed by a long gap with
pivot `i.stepBack t` where `σ` is `-1`. Let the far windows at the levels `a ≠ t` below `l` be small
or of the sign opposite to that at the pivot. Then `R` has a point `q` over `p ^ (25 κ) c` with
orders `stopOrders η l` and depth `longGapDepth l t (2 b)` that has this property: `R'` moves from
`φ ^ l` of its standard point at that cut, whose own cut before is any `l₀` letters back, to its
standard point at `i`, so the move has the minimum of the two systems `cutOrders`; at each jump `u`
of `R'` this order and the depth at any `v` add up to at least `ruleBound l 0`. -/
lemma exists_mem_pointsOver_ruleBound_le_of_isLongGap {ε : k.Letter → ℤˣ} {s β : k.Letter → ℕ}
    {η V W X δ κ b n J s₀ G ω : ℕ} {R R' : PairingSide O} {σ : k.Letter → ℤˣ} (hη : 1 ≤ η)
    (hW : V + 4 * η ≤ W) (hR : ∀ i : k.Letter, FitsWindows η (σ i) (β i) V (R.jumpSet i))
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) {i : k.Letter} (h_shift : s i + W ≤ p * n)
    {l l₀ t : ℕ} (hl : l ≤ 2 * J + 1) (h_cut : (i.stepBack l).IsKillingCut s β W J G s₀ κ)
    (h_gap : i.IsLongGap ε s β η V J s₀ ω l t) (h_pivot : σ (i.stepBack t) = -1)
    (hR' : ∀ i : k.Letter, FitsWindows η (-σ i) (β i) V (R'.jumpSet i))
    (h_sign : ∀ a < l, a ≠ t →
      σ (i.stepBack a) ≠ σ (i.stepBack t) ∨ β (i.stepBack a) + V ≤ η) (c : R.paramLattice) :
    ∃ q ∈ R.pointsOver c i (25 * κ) (stopOrders η l) (longGapDepth l t (2 * b)),
      ∀ a : ℕ, ∀ u ∈ R'.jumpSet (i.stepBack a), ∀ v : ℤ, ruleBound l 0 a (u + v) ≤
        (cutOrders (s i) η l ⊓ JumpLattice.shiftedOrders l 0 (cutOrders 0 η l₀)) a u +
          longGapDepth l t (2 * b) a v := by
  have ht : t < l := by grind [h_gap.pivot_add]
  have h_far : β (i.stepBack t) + s (i.stepBack t) + W ≤ 2 * b := h_sizes.far_le _
  have h_opposite (a : ℕ) (ha : a < l) (hat : a ≠ t) :
      σ (i.stepBack a) = 1 ∨ β (i.stepBack a) + V ≤ η := by
    simpa only [h_pivot, Int.units_ne_iff_eq_neg, neg_neg] using h_sign a ha hat
  obtain ⟨q, hq⟩ := pointsOver_longGapDepth_nonempty hη hW hR h_sizes h_shift hl h_cut h_gap h_pivot
    (fun a ha hat ↦ neg_le_jump_of_fitsWindows (hR _) (h_opposite a ha hat)) c
  refine ⟨q, hq, fun a u hu v ↦ ruleBound_le_inf_add_longGapDepth ht (by omega) (fun ha hat ↦ ?_) ?_
    v⟩
  · exact jump_le_of_fitsWindows (hR' _) ((h_opposite a ha hat).imp_left neg_inj.2) u hu
  · -- The jumps at the pivot are less than `η + 2 b`.
    rintro rfl
    grind [low_or_far_of_fitsWindows (hR' _) hu]

/-- Let the sides `S`, `S'`, paired by `h`, have jumps in `[-η, η]` and in opposite far windows
`∓ε j • [β j, β j + V]`. Let the cut `i.stepBack l` have shift `0` and be followed up to `i` by a
long gap: the far window at the pivot `i.stepBack t` starts far out and the others have the opposite
sign or are small. Let `x`, `x'` at `i` and `x₀`, `x₀'` at `i.stepBack l` be points of the two sides
over `p ^ (25 κ) c`, `p ^ (25 κ) c'` with the orders `cutOrders` of standard points at these cuts
and any depths `d`, `d₀`. Let `h_cut` say that the cut is of a kind at which the cokernels of `S`
and `S'` are killed, and `h_kill` that `p ^ κ` kills that of the Tate dual side, with lattice
`Hom(Y ⊗ Y', O(1))`, there. Let the size conditions `CutSizes` hold with `η ≥ 1`, `V + 4 η ≤ W`,
`s i + W ≤ p n` and `l ≤ 2 J + 1`. Then one side has a stop, at which it rests while the other side
moves from `φ ^ l` of its point at `i.stepBack l` to its point at `i`, and this move is safe:
`p ^ κ` times its pairing with all `g • q - q` (`q` the stop) lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.exists_stop_of_isLongGap {ε : k.Letter → ℤˣ} {s β : k.Letter → ℕ}
    {η V W X δ κ b n J s₀ G ω : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (β i) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (β i) V (S'.jumpSet i))
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) {i : k.Letter} (h_shift : s i + W ≤ p * n)
    {l l₀ t : ℕ} (hl : l ≤ 2 * J + 1) (h_cut : (i.stepBack l).IsKillingCut s β W J G s₀ κ)
    (h_kill : h.tateDualSide.KillsCokernel (i.stepBack l) κ 0)
    (h_gap : i.IsLongGap ε s β η V J s₀ ω l t) {c : S.paramLattice} {c' : S'.paramLattice}
    {d d₀ : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient} {x₀' x' : S'.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i (25 * κ) (cutOrders (s i) η l) d)
    (hx' : x' ∈ S'.pointsOver c' i (25 * κ) (cutOrders (s i) η l) d)
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) (25 * κ) (cutOrders 0 η l₀) d₀)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) (25 * κ) (cutOrders 0 η l₀) d₀) :
    (∃ q ∈ S.stopPoints c i (25 * κ) η l, h.IsSafeMoveSnd κ q (FrobGroup.φ ^ l • x₀' - x')) ∨
      ∃ q' ∈ S'.stopPoints c' i (25 * κ) η l,
        h.IsSafeMoveFst κ (FrobGroup.φ ^ l • x₀ - x) q' := by
  -- The side with the negative far window at the pivot leads; by symmetry one lemma serves both.
  obtain hε | hε := Int.units_eq_one_or (ε (i.stepBack t))
  · have h_sign : ∀ a < l, a ≠ t →
        -ε (i.stepBack a) ≠ -ε (i.stepBack t) ∨ β (i.stepBack a) + V ≤ η := by
      simpa only [ne_eq, neg_inj] using h_gap.sign_ne_or_far_le
    obtain ⟨q, hq, h_rule⟩ := exists_mem_pointsOver_ruleBound_le_of_isLongGap (R' := S') (l₀ := l₀)
      hη hW hU
      h_sizes h_shift hl h_cut h_gap (neg_inj.2 hε) (by simpa only [neg_neg] using hU') h_sign c
    exact .inl ⟨q, mem_stopPoints_of_mem_pointsOver hq, h.isSafeMoveSnd_of_killsCokernel h_kill
      (sub_mem_kerWithOrders_of_pointsOver hx' (phi_pow_smul_mem_pointsOver hx₀')) hq
      fun a u hu v _ ↦ h_rule a u hu v⟩
  · obtain ⟨q', hq', h_rule⟩ := exists_mem_pointsOver_ruleBound_le_of_isLongGap (R' := S) (l₀ := l₀)
      hη hW hU'
      h_sizes h_shift hl h_cut h_gap hε hU h_gap.sign_ne_or_far_le c'
    exact .inr ⟨q', mem_stopPoints_of_mem_pointsOver hq', h.isSafeMoveFst_of_killsCokernel h_kill
      (sub_mem_kerWithOrders_of_pointsOver hx (phi_pow_smul_mem_pointsOver hx₀)) hq'
      fun a u hu v _ ↦ h_rule a u hu v⟩

/-- Let the paired sides have their jumps at each letter `j` in `[-η, η]` and in opposite far
windows `∓ε j • [β j, β j + V]`. Let `i` be a plain cut: `0 < l`, and the `l` letters after
`i.stepBack l` share the sign `ρ`, up to far windows that end at or below `η`. Let `x`, `x'` at `i`
and `x₀`, `x₀'` at `i.stepBack l` be points of the two sides over `p ^ e c`, `p ^ e c'` with orders
`-u` on each jump `u`, lowered by `η` at the distinguished element `E` (level `0`). Let `x`, `x'`
have the depth `plainDepth s η l η`: `-u`, raised by `s` at the level `0` and by `η` at the levels
up to `l`. Let `p ^ κ * E ^ s` kill the cokernel at `i` of the Tate dual side, with lattice
`Hom(Y ⊗ Y', O(1))`. Then one side has a stop, at which it rests while the other side moves from
`φ ^ l` of its point at `i.stepBack l` to its point at `i`, safely: `p ^ κ` times the pairing of
this move with all `g • q - q` (`q` the stop) lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.exists_stop_of_hasSignBefore {ε : k.Letter → ℤˣ} {β : k.Letter → ℕ}
    {η V κ e : ℕ} (h : S.SidePairing S')
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (β i) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (β i) V (S'.jumpSet i)) {i : k.Letter} {l s : ℕ}
    {ρ : ℤˣ} (hl : 0 < l) (h_kill : h.tateDualSide.KillsCokernel i κ s)
    (h_plain : i.HasSignBefore ε β η V l ρ) {c : S.paramLattice} {c' : S'.paramLattice}
    {d₀ : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient} {x₀' x' : S'.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) (plainDepth s η l η))
    (hx' : x' ∈ S'.pointsOver c' i e (raisedOrdersAtZero (-η)) (plainDepth s η l η))
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) e (raisedOrdersAtZero (-η)) d₀)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) e (raisedOrdersAtZero (-η)) d₀) :
    (∃ q ∈ S.stopPoints c i e η l, h.IsSafeMoveSnd κ q (FrobGroup.φ ^ l • x₀' - x')) ∨
      ∃ q' ∈ S'.stopPoints c' i e η l, h.IsSafeMoveFst κ (FrobGroup.φ ^ l • x₀ - x) q' := by
  obtain rfl | rfl := Int.units_eq_one_or ρ
  · have h_down (a : ℕ) (ha : a < l) : ∀ u ∈ S.jumpSet (i.stepBack a), u ≤ η :=
      jump_le_of_fitsWindows (hU _) ((h_plain a ha).imp_left neg_inj.2)
    have h_up (a : ℕ) (ha : a < l) : ∀ u ∈ S'.jumpSet (i.stepBack a), -η ≤ u :=
      neg_le_jump_of_fitsWindows (hU' _) (h_plain a ha)
    exact .inl (h.exists_mem_stopPoints_isSafeMoveSnd hl h_kill h_down h_up hx hx' hx₀')
  · have h_down (a : ℕ) (ha : a < l) : ∀ u ∈ S'.jumpSet (i.stepBack a), u ≤ η :=
      jump_le_of_fitsWindows (hU' _) (h_plain a ha)
    have h_up (a : ℕ) (ha : a < l) : ∀ u ∈ S.jumpSet (i.stepBack a), -η ≤ u :=
      neg_le_jump_of_fitsWindows (hU _) ((h_plain a ha).imp_left neg_eq_iff_eq_neg.2)
    exact .inr (h.exists_mem_stopPoints_isSafeMoveFst hl h_kill h_down h_up hx' hx hx₀)

/-- Upper bounds on the jumps of three sides: two paired sides `S`, `S'` and the Tate dual side of
the pairing, with lattice `Hom(Y ⊗ Y', O(1))`, whose jumps are `0` and the `-(u + u') - 1` for jumps
`u` of `S` and `u'` of `S'`. If at the letter `i` the jumps of the paired sides lie in the low
window `[-η, η]` and in opposite far windows `∓ε i • [β i, β i + V]`, and `V + 4 η ≤ W`, then the
jumps of all three sides at `i` are at most `β i + W`. -/
lemma SidePairing.jumps_le_of_fitsWindows {ε : k.Letter → ℤˣ} {β : k.Letter → ℕ} {η V W : ℕ}
    (h : S.SidePairing S') (hW : V + 4 * η ≤ W)
    {i : k.Letter} (h_left : FitsWindows η (-ε i) (β i) V (S.jumpSet i))
    (h_right : FitsWindows η (ε i) (β i) V (S'.jumpSet i)) :
    (∀ w ∈ h.tateDualSide.jumpSet i, w ≤ β i + W) ∧
      (∀ u ∈ S.jumpSet i, u ≤ β i + W) ∧ ∀ u' ∈ S'.jumpSet i, u' ≤ β i + W := by
  refine ⟨fun w hw ↦ ?_, fun u ↦ h_left.le_add (by omega), fun u' ↦ h_right.le_add (by omega)⟩
  -- The jumps of the Tate dual side are `0` and the `-(u + u') - 1`.
  obtain rfl | ⟨u, hu, u', hu', rfl⟩ :
      w = 0 ∨ ∃ u ∈ S.jumpSet i, ∃ u' ∈ S'.jumpSet i, -(u + u') - 1 = w := by
    simpa only [mem_insert, mem_image, mem_image₂, exists_exists_and_exists_and_eq_and] using hw
  · positivity
  -- As the far windows have opposite signs, `u` and `u'` are not both below `-η`, and neither is
  -- below `-(β i + V + η)`.
  have h_sign : ((-ε i : ℤˣ) : ℤ) = -(ε i : ℤ) := Units.val_neg (ε i)
  rcases h_left u hu, h_right u' hu' with ⟨h_low | h_pos | h_neg, h_low' | h_pos' | h_neg'⟩
  all_goals omega

/-- The scheme of cuts, a chosen set of letters. Let paired sides have their jumps in the low window
`[-η, η]` and in opposite far windows `∓ε i • [β i, β i + V]`. Suppose that `η ≥ 1`, `V + 4 η ≤ W`,
that the shifts have `s i + W ≤ p n`, and that the size conditions `CutSizes` hold: `2 b` bounds all
`β i + s i + W`, `n` bounds `G / (p - 1)`, `s₀` bounds `(β i + W) / (p - 3)` for `p ≥ 5`, and `κ` is
large against the cost `X` of one of `J + 1` levels and the cost `δ` of the depth `2 b`. Let each
cut `i` be of a kind at which the cokernel is killed (`IsKillingCut`): `s i = 0` and `β + W ≤ G` at
the next `J` letters, or the chart is unramified, `p ≥ 5` and `s₀ - κ ≤ s i < β i`. Let every letter
have a cut at most `2 J + 1` steps back. Suppose also that the letters after the nearest cut share
the sign of some `i.stepBack t`, up to small far windows, or have a long gap with pivot
`i.stepBack t`. Then, for every `e ≥ 51 κ` and `c`, `c'` in the lattices `paramLattice` of the
sides, the cup product of the cocycles of `c` and `p ^ e c'` is a coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_cut_windows {cut : k.Letter → Prop} {ε : k.Letter → ℤˣ}
    {s β : k.Letter → ℕ} {η V W X δ κ b n J s₀ G ω e : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η)
    (hW : V + 4 * η ≤ W) (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (β i) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (β i) V (S'.jumpSet i))
    (h_sizes : k.CutSizes s β W X δ κ b n J s₀ G) (h_shift : ∀ i : k.Letter, s i + W ≤ p * n)
    (h_killing : ∀ i : k.Letter, cut i → i.IsKillingCut s β W J G s₀ κ)
    (h_cut_before : ∀ i : k.Letter, ∃ l ∈ Set.Ioc 0 (2 * J + 1), cut (i.stepBack l))
    (h_gap : ∀ (i : k.Letter) (l : ℕ), i.IsNearestCut cut l → ∃ t : ℕ,
      i.HasSignBefore ε β η V l (ε (i.stepBack t)) ∨ i.IsLongGap ε s β η V J s₀ ω l t)
    (he : 51 * κ ≤ e) (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary e c c' := by
  -- Apply the walk. At each cut both sides get a standard point over `p ^ (25 κ)`. The side whose
  -- far window at the pivot is negative leads; its stop is its own point at a plain cut, and comes
  -- from the long gap at the other cuts.
  -- The letter `i.stepBack (l i)` is the nearest cut before `i`.
  have h_nearest (i : k.Letter) : ∃ l : ℕ, l ≤ 2 * J + 1 ∧ i.IsNearestCut cut l := by
    classical
    obtain ⟨⟨h_pos, h_le⟩, h_cut⟩ := Nat.find_spec (h_cut_before i)
    exact ⟨Nat.find (h_cut_before i), h_le, h_pos, h_cut, fun a ⟨ha_pos, ha_lt⟩ ha_cut ↦
      Nat.find_min (h_cut_before i) ha_lt ⟨⟨ha_pos, ha_lt.le.trans h_le⟩, ha_cut⟩⟩
  choose l hl_le hl_nearest using h_nearest
  have hl_least (i : k.Letter) : IsLeast {a : ℕ | 0 < a ∧ cut (i.stepBack a)} (l i) :=
    ⟨⟨(hl_nearest i).pos, (hl_nearest i).cut_stepBack⟩, fun a ⟨ha_pos, ha_cut⟩ ↦
      le_of_not_gt fun ha_lt ↦ (hl_nearest i).not_cut a ⟨ha_pos, ha_lt⟩ ha_cut⟩
  have h_kill (i : k.Letter) (hi : cut i) : h.tateDualSide.KillsCokernel i κ (s i) :=
    killsCokernel_of_isKillingCut h_sizes
      (fun j ↦ (h.jumps_le_of_fitsWindows hW (hU j) (hU' j)).left) (h_killing i hi)
  -- The standard points of a side `R`; they also have the depth that a plain cut asks.
  have h_points {R : PairingSide O} {σ : k.Letter → ℤˣ}
      (hR : ∀ i : k.Letter, FitsWindows η (σ i) (β i) V (R.jumpSet i)) (d : R.paramLattice) :
      ∃ x : k.Letter → R.extensionLattice.Ambient,
        (∀ i, cut i → x i ∈ R.pointsOver d i (25 * κ) (cutOrders (s i) η (l i))
          (standardDepth (s i) η (l i + 1))) ∧
        ∀ i, cut i →
          x i ∈ R.pointsOver d i (25 * κ) (raisedOrdersAtZero (-η))
            (plainDepth (s i) η (l i) η) := by
    choose! x hx using fun i hi ↦
      pointsOver_cutOrders_nonempty hη hW hR h_sizes (h_shift i) (h_killing i hi) (hl_le i) d
    exact ⟨x, hx, fun i hi ↦
      mem_pointsOver_plainDepth_of_cutOrders (hR i) (h_killing i hi) (hx i hi)⟩
  obtain ⟨x, hx, hx_plain⟩ := h_points hU c
  obtain ⟨x', hx', hx'_plain⟩ := h_points hU' c'
  refine h.isScaledCupCoboundary_of_stops cut l s x x' hl_least h_kill
    (fun i hi ↦ mem_standardPoints_of_plainDepth (hx_plain i hi))
    (fun i hi ↦ mem_standardPoints_of_plainDepth (hx'_plain i hi)) (fun i hi ↦ ?_) (by omega)
  have h_before : cut (i.stepBack (l i)) := (hl_nearest i).cut_stepBack
  obtain ⟨t, h_plain | h_long⟩ := h_gap i (l i) (hl_nearest i)
  · exact h.exists_stop_of_hasSignBefore hU hU' (hl_nearest i).pos (h_kill i hi) h_plain
      (hx_plain i hi) (hx'_plain i hi) (hx_plain _ h_before) (hx'_plain _ h_before)
  · -- The cut before a long gap has shift `0`.
    have h_kill_before := h_kill _ h_before
    have hx_before := hx _ h_before
    have hx'_before := hx' _ h_before
    rw [h_long.shift_eq_zero] at h_kill_before hx_before hx'_before
    exact h.exists_stop_of_isLongGap hη hW hU hU' h_sizes (h_shift i) (hl_le i)
      (h_killing _ h_before) h_kill_before h_long (hx i hi) (hx' i hi) hx_before hx'_before

/-- The size conditions `CutSizes` of the scheme of cuts (letters at which the exponent bound is
anchored) with all shifts `0`, for far windows of the jumps that start at `β i ≤ max b W` at each
letter `i`. They ask that the cost `X` of a level dominate `n`, `log_p (2 b)`, `W` and `G`, that
`κ` exceed `12 ((J + 1) X + δ)`, that `β i + W ≤ 2 b`, and that `G`, `β i + W` and `2 e b` be at
most `(p - 1) n`, `(p - 3) s₀` (if `p ≥ 5`) and `p ^ (J + 1) δ`. Let `8 e ≤ p ^ (J + 1)`,
`2 e (b + W) ≤ p ^ (J + 1) δ` and
`4 (J + 1 + d) W + ⌊log_p (2 (b + W))⌋ ≤ X`, where `e = k.e` is the ramification index and
`d = k.differentBound` is `0` if `e = 1` and `v_p(e) + 1` otherwise. Then the conditions hold with
`κ = 12 ((J + 1) X + δ) + 1`, with `b + W` in place of `b`, with `n = G = 2 W` and with
`s₀ = ⌊(b + 2 W) / (p - 3)⌋ + 1`. -/
lemma _root_.New.Lift.KummerChart.cutSizes_zero_shift {β : k.Letter → ℕ} {W X δ b J : ℕ}
    (hβ_le : ∀ i : k.Letter, β i ≤ max b W)
    (h_ram : 8 * k.e ≤ p ^ (J + 1)) (h_depth : k.e * (2 * (b + W)) ≤ p ^ (J + 1) * δ)
    (hX : 4 * (J + 1 + k.differentBound) * W + p.log (2 * (b + W)) ≤ X) :
    k.CutSizes (fun _ : k.Letter ↦ 0) β W X δ (12 * ((J + 1) * X + δ) + 1) (b + W) (2 * W) J
      ((b + 2 * W) / (p - 3) + 1) (2 * W) where
  le_cost := by lia
  cost_lt := Nat.lt_succ_self _
  ramification_mul_le := h_depth
  ramification_le := h_ram
  far_le i :=
    calc β i + 0 + W ≤ max b W + 0 + W := by grw [hβ_le i]
      _ ≤ 2 * (b + W) := by omega
  thin_le := Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  far_le_of_five_le hp i :=
    calc β i + W ≤ max b W + W := Nat.add_le_add_right (hβ_le i) W
      _ ≤ b + 2 * W := by omega
      _ ≤ (p - 3) * ((b + 2 * W) / (p - 3) + 1) := (Nat.lt_mul_div_succ _ (by omega)).le

/-- On an unramified chart the ramification index `k.e` is `1`, so `8 e ≤ p ^ 2` if `p ≥ 3`. -/
lemma _root_.New.Lift.KummerChart.IsUnramified.eight_mul_e_le_sq (hk : k.IsUnramified)
    (hp : 3 ≤ p) : 8 * k.e ≤ p ^ 2 := by
  calc 8 * k.e ≤ 3 ^ 2 := by simp [hk.right.1]
    _ ≤ p ^ 2 := pow_le_pow_left' hp 2

/-- Let the far windows `± [β i, β i + V]` start at `b` at the b-letters, or thick letters (those
with `T`), and at `G` at the others, the thin ones, where `η ≥ 1` and `G + V ≤ η`. Among the letters
`i.stepBack r` with `r < l`, let only those with `r = 0` or `r + (J + 1) = l` be possibly thick. Let
the chart be unramified with `p ≥ 7` and `10 p ^ J η ≤ b`, or let the sign `ε` be constant. Then for
some pivot `i.stepBack t` these `l` letters have the sign of the pivot or a far window that ends at
or below `η` (`HasSignBefore`), or there is a long gap among them: the pivot is `J + 1` steps after
`i.stepBack l`, its window starts beyond `s₀ + ω (1 + ⋯ + p ^ J)` and the others have the opposite
sign or small windows (`IsLongGap` with all shifts `0`, `s₀ = ⌊(b + 10 η) / (p - 3)⌋ + 1` and
`ω = η`). -/
lemma _root_.New.Lift.KummerChart.Letter.hasSignBefore_or_isLongGap {T : k.Letter → Prop}
    {ε : k.Letter → ℤˣ} {β : k.Letter → ℕ} {η V b J G : ℕ} {i : k.Letter} {l : ℕ} (hη : 1 ≤ η)
    (hβ_thick : ∀ i : k.Letter, T i → β i = b) (hβ_thin : ∀ i : k.Letter, ¬T i → β i = G)
    (hG : G + V ≤ η)
    (h_unramified_or_constSign :
      k.IsUnramified ∧ 7 ≤ p ∧ 10 * p ^ J * η ≤ b ∨ ∀ i i' : k.Letter, ε i = ε i')
    (h_thick_positions : ∀ r : ℕ, r < l → T (i.stepBack r) → r = 0 ∨ r + (J + 1) = l) :
    ∃ t : ℕ, i.HasSignBefore ε β η V l (ε (i.stepBack t)) ∨
      i.IsLongGap ε (fun _ : k.Letter ↦ 0) β η V J ((b + 10 * η) / (p - 3) + 1) η l t := by
  by_cases h_sign : i.HasSignBefore ε β η V l (ε (i.stepBack 0))
  · exact ⟨0, .inl h_sign⟩
  -- The pivot `i.stepBack t` is a b-letter and its sign is not that of `i`; so `t + (J + 1) = l`.
  obtain ⟨t, ht_lt, ht_sign, ht_far⟩ :
      ∃ t < l, ε (i.stepBack t) ≠ ε (i.stepBack 0) ∧ η < β (i.stepBack t) + V := by
    simpa only [Letter.HasSignBefore, not_forall, not_or, not_le, exists_prop] using h_sign
  obtain ⟨hk, hp, hb⟩ :=
    h_unramified_or_constSign.resolve_right fun h_const ↦ ht_sign (h_const _ _)
  have ht_thick : T (i.stepBack t) := by grind
  have h_pivot : t + (J + 1) = l :=
    (h_thick_positions t ht_lt ht_thick).resolve_left fun ht_zero ↦ ht_sign (by rw [ht_zero])
  -- The letters other than `i` and the pivot are thin, so their far windows are small.
  have h_small (a : ℕ) (ha : a < l) (ha_ne : a ≠ t) (ha_pos : a ≠ 0) :
      β (i.stepBack a) + V ≤ η := by
    rwa [hβ_thin _ fun h_thick ↦ (h_thick_positions a ha h_thick).elim ha_pos (by omega)]
  -- The geometric sum is at most `2 p ^ J`, and `(b + 10 η) / 4 + 1 + 2 p ^ J η < b`.
  have h_lt_pivot : (b + 10 * η) / (p - 3) + 1 + η * ∑ a ∈ range (J + 1), p ^ a < b := by
    have h_sum : ∑ a ∈ range (J + 1), p ^ a ≤ 2 * p ^ J := by
      rw [sum_range_succ, two_mul, add_le_add_iff_right]
      exact (Nat.geomSum_lt (by omega) (by simp)).le
    have h_div : (b + 10 * η) / (p - 3) ≤ (b + 10 * η) / 4 :=
      Nat.div_le_div_left (by omega) four_pos
    have hη_le : η ≤ p ^ J * η := Nat.le_mul_of_pos_left η (by positivity)
    calc _ ≤ (b + 10 * η) / 4 + 1 + η * (2 * p ^ J) := by gcongr
      _ < b := by lia
  refine ⟨t, .inr
    { isUnramified := hk
      five_le := by omega
      shift_eq_zero := rfl
      pivot_add := h_pivot
      lt_far_pivot := h_lt_pivot.trans_eq (hβ_thick _ ht_thick).symm
      sign_ne_or_far_le := fun a ha ha_ne ↦ ?_
      low_le := le_rfl
      far_le := fun a ha ha_gt ↦ h_small a ha ha_gt.ne' (by omega) }⟩
  obtain rfl | ha_pos := eq_or_ne a 0
  · exact .inl ht_sign.symm
  · exact .inr (h_small a ha ha_ne ha_pos)

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
Then one of the `2 J + 1` letters before `i` is followed by `J` letters without `T`. -/
lemma _root_.New.Lift.KummerChart.Letter.exists_hasThinSuccessors_stepBack {T : k.Letter → Prop}
    {J : ℕ} (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i)) (i : k.Letter) :
    ∃ l ∈ Set.Ioc 0 (2 * J + 1), (i.stepBack l).HasThinSuccessors T J := by
  -- If the letter `J + 1` steps back fails, then a letter `r` steps back has `T`, with `1 ≤ r ≤ J`.
  -- That letter or the one `J + 1` steps before it has the property.
  by_cases h_first : (i.stepBack (J + 1)).HasThinSuccessors T J
  · exact ⟨J + 1, ⟨J.succ_pos, by omega⟩, h_first⟩
  obtain ⟨n, hn_pos, hn_le, h_next⟩ :
      ∃ n : ℕ, n ≥ 1 ∧ n ≤ J ∧ T ((k.letterFrob ^ n) (i.stepBack (J + 1))) := by
    simpa only [Letter.HasThinSuccessors, not_forall, not_not, exists_prop] using h_first
  have h_thick : T (i.stepBack (J + 1 - n)) := by simpa [pow_sub _ hn_le.step] using h_next
  by_cases h_second : (i.stepBack (J + 1 - n)).HasThinSuccessors T J
  · exact ⟨J + 1 - n, by grind, h_second⟩
  · exact ⟨J + 1 - n + (J + 1), by grind,
      Letter.hasThinSuccessors_stepBack_add h_sparse i _ h_second h_thick⟩

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
Let `i.stepBack l` be the nearest letter before `i` that is followed by `J` letters without `T`.
Then a letter `i.stepBack r` with `T` and `r < l` is `i` itself or lies `J + 1` steps after
`i.stepBack l`. -/
lemma _root_.New.Lift.KummerChart.Letter.IsNearestCut.eq_zero_or_add_eq_of_hasThinSuccessors
    {T : k.Letter → Prop} {J l r : ℕ} {i : k.Letter}
    (h_nearest : i.IsNearestCut (fun i' : k.Letter ↦ i'.HasThinSuccessors T J) l)
    (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (hr : r < l) (h_thick : T (i.stepBack r)) : r = 0 ∨ r + (J + 1) = l := by
  refine r.eq_zero_or_pos.imp_right fun hr_pos ↦ le_antisymm ?_ ?_
  · -- The letter with `T` is not among the `J` letters after `i.stepBack l`.
    by_contra h_near
    have h_after : T ((k.letterFrob ^ (l - r)) (i.stepBack l)) := by
      simpa [← pow_mul_pow_sub _ hr.le] using h_thick
    exact h_nearest.cut_stepBack (l - r) (by omega) (by omega) h_after
  · -- Otherwise the letter `r + (J + 1)` steps back would be a nearer cut.
    by_contra h_far
    have h_cut : (i.stepBack (r + (J + 1))).HasThinSuccessors T J :=
      Letter.hasThinSuccessors_stepBack_add h_sparse i r (h_nearest.not_cut r ⟨hr_pos, hr⟩) h_thick
    exact h_nearest.not_cut (r + (J + 1)) (by grind) h_cut

/-- Sparse b-letters. Let the sides `S`, `S'` of a Kummer chart be paired by `h`; each side has
lattices Y and `C = paramLattice`, a map `cocycleMap` from C to the crystalline cocycles of Y, and a
finite set of jumps at each letter. The b-letters, or thick letters, are those with `T i`. At each
b-letter `i`, let each jump of `S` lie in `[-η, η]` or in the far window `-ε i [b, b + V]`, and each
jump of `S'` in `[-η, η]` or in `ε i [b, b + V]`. At the other letters `G` replaces `b`. Here
`η ≥ 1` and `G + V ≤ η`. Suppose that no three b-letters follow one another under Frobenius with
both gaps between `1` and `J ≥ 1`. Suppose also that the chart is unramified with `p ≥ 7` and
`10 p ^ J η ≤ b`, or that the sign `ε` is constant and `8 e ≤ p ^ (J + 1)`. Let
`2 e (b + 5 η) ≤ p ^ (J + 1) δ` and `20 (J + 1 + d) η + ⌊log_p (2 (b + 5 η))⌋ ≤ X`. Here `e = k.e`
is the ramification index, and `d = k.differentBound` is `0` if `e = 1` and `v_p(e) + 1` otherwise.
Then for `c` in `S.paramLattice` and `c'` in `S'.paramLattice`, the cup product of the cocycles
`S.cocycleMap c` and `p ^ (10³ (δ + (J + 1) X)) • S'.cocycleMap c'` is a coboundary
(`IsScaledCupCoboundary`). -/
lemma SidePairing.isScaledCupCoboundary_sparse_thick {T : k.Letter → Prop} [DecidablePred T]
    {ε : k.Letter → ℤˣ} {η V X δ b J G : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (if T i then b else G) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (if T i then b else G) V (S'.jumpSet i))
    (hG : G + V ≤ η) (hJ : 1 ≤ J) (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (h_unramified_or_constSign : k.IsUnramified ∧ 7 ≤ p ∧ 10 * p ^ J * η ≤ b ∨
      (∀ i i' : k.Letter, ε i = ε i') ∧ 8 * k.e ≤ p ^ (J + 1))
    (h_depth : k.e * (2 * (b + 5 * η)) ≤ p ^ (J + 1) * δ)
    (hX : 20 * (J + 1 + k.differentBound) * η + p.log (2 * (b + 5 * η)) ≤ X)
    (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary (10 ^ 3 * (δ + (J + 1) * X)) c c' := by
  -- Apply `isScaledCupCoboundary_of_cut_windows` without shifts, cutting at the letters that are
  -- followed by `J` thin letters, with the width `W = 5 η` and the least `κ` it allows.
  let β (i : k.Letter) : ℕ := if T i then b else G
  let κ : ℕ := 12 * ((J + 1) * X + δ) + 1
  let s₀ : ℕ := (b + 10 * η) / (p - 3) + 1
  have hβ_thick (i : k.Letter) (hi : T i) : β i = b := ite_eq_left hi
  have hβ_thin (i : k.Letter) (hi : ¬T i) : β i = G := ite_eq_right hi
  have hβ_le (i : k.Letter) : β i ≤ max b (5 * η) := by grind
  have h_ram : 8 * k.e ≤ p ^ (J + 1) := by
    obtain ⟨hk, hp, -⟩ | ⟨-, h_ram⟩ := h_unramified_or_constSign
    · exact (hk.eight_mul_e_le_sq (by omega)).trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact h_ram
  have h_sizes :
      k.CutSizes (fun _ ↦ 0) β (5 * η) X δ κ (b + 5 * η) (2 * (5 * η)) J s₀ (2 * (5 * η)) := by
    simpa [s₀, κ, ← mul_assoc] using cutSizes_zero_shift hβ_le h_ram h_depth (by linarith)
  have hW : V + 4 * η ≤ 5 * η := by omega
  have h_width : 0 + 5 * η ≤ p * (2 * (5 * η)) := by nlinarith [(Fact.out : p.Prime).two_le]
  have h_killing (i : k.Letter) (hi : i.HasThinSuccessors T J) :
      i.IsKillingCut (fun _ ↦ 0) β (5 * η) J (2 * (5 * η)) s₀ κ := by
    refine .of_thin rfl fun t ht ↦ ?_
    obtain ⟨ht_pos, ht_le⟩ := mem_Icc.1 ht
    rw [hβ_thin _ (hi t ht_pos ht_le)]
    omega
  have h_gap (i : k.Letter) (l : ℕ) (h_nearest : i.IsNearestCut (·.HasThinSuccessors T J) l) :
      ∃ t : ℕ, i.HasSignBefore ε β η V l (ε (i.stepBack t)) ∨
        i.IsLongGap ε (fun _ ↦ 0) β η V J s₀ η l t :=
    Letter.hasSignBefore_or_isLongGap hη hβ_thick hβ_thin hG
      (h_unramified_or_constSign.imp_right And.left)
      fun _ ↦ h_nearest.eq_zero_or_add_eq_of_hasThinSuccessors h_sparse
  have h_exponent : 51 * κ ≤ 10 ^ 3 * (δ + (J + 1) * X) := by lia
  exact h.isScaledCupCoboundary_of_cut_windows hη hW hU hU' h_sizes (fun _ ↦ h_width) h_killing
    (Letter.exists_hasThinSuccessors_stepBack h_sparse) h_gap h_exponent c c'

/-- The size conditions `CutSizes` of the scheme of cuts with `J = 1`, on an unramified chart with
`p ≥ 7`. Here `β i` is the start of the far window of the jumps at the letter `i` and `s i` its
shift, the pole order at `E` allowed if `i` is a cut; let `β i ≤ b` and `s i ≤ ⌊b / p⌋ - 7 K`. Let
`b < K p ^ 2`, `2 G < K p` and `W ≤ K`. Then they hold with the costs
`X = 3 K + ⌊log_p (2 (b + W))⌋` and `δ = 4 K`, with `κ = 12 (2 X + δ) + 1`, `n = K` and
`s₀ = ⌊b / p⌋ + 12 K`, and with `b + W` and `G + W` in place of `b` and `G`. -/
lemma _root_.New.Lift.KummerChart.cutSizes_of_isUnramified {s β : k.Letter → ℕ} {W b G K : ℕ}
    (hk : k.IsUnramified) (hp : 7 ≤ p)
    (hβ_le : ∀ i : k.Letter, β i ≤ b) (hs_le : ∀ i : k.Letter, s i ≤ b / p - 7 * K)
    (hbK : b < K * p ^ 2) (hGK : 2 * G < K * p) (hWK : W ≤ K) :
    k.CutSizes s β W (3 * K + p.log (2 * (b + W))) (4 * K)
      (12 * (2 * (3 * K + p.log (2 * (b + W))) + 4 * K) + 1) (b + W) K 1 (b / p + 12 * K)
      (G + W) := by
  obtain ⟨he_one, h_different⟩ := hk.right
  have hK_pos : 0 < K := Nat.pos_of_mul_pos_right (Nat.zero_lt_of_lt hGK)
  have hK_seven : K * 7 ≤ K * p := mul_le_mul_right hp K
  exact
    { le_cost := by
        rw [h_different]
        omega
      cost_lt := by omega
      ramification_mul_le := by
        have hK_sq : K ≤ K * p ^ 2 := Nat.le_mul_of_pos_right K (by positivity)
        calc k.e * (2 * (b + W)) = 2 * (b + W) := by rw [he_one, one_mul]
          _ ≤ p ^ (1 + 1) * (4 * K) := by lia
      ramification_le := hk.eight_mul_e_le_sq (by omega)
      far_le i :=
        calc β i + s i + W ≤ b + (b / p - 7 * K) + W := by grw [hβ_le i, hs_le i]
          _ ≤ b + b + W := by grw [Nat.sub_le, Nat.div_le_self]
          _ ≤ 2 * (b + W) := by omega
      thin_le := by
        rw [Nat.sub_one_mul, mul_comm p K]
        omega
      far_le_of_five_le _ i := by
        -- `b - (p - 3) (b / p) < 3 (b / p) + p ≤ 4 p K`
        have h_lt_div : b < b / p * p + p := b.lt_div_mul_add (by omega)
        have h_div_lt : b / p < K * p := Nat.div_lt_of_lt_mul (by lia)
        have hpK : p ≤ K * p := Nat.le_mul_of_pos_left p hK_pos
        have h_expand : (p - 3) * (b / p + 12 * K) + 3 * (b / p + 12 * K) =
            b / p * p + 12 * (K * p) := by
          rw [← add_mul, Nat.sub_add_cancel (by omega)]
          ring
        grw [hβ_le i]
        omega }

/-- A long gap of length `2`, on an unramified chart with `p ≥ 7`. Let the far window of the jumps,
of width `V` beside the low window `[-η, η]`, start at `b` at `i`, and at `G` with
`G + 7 K ≤ ⌊b / p⌋` at the letter before `i`, which has the opposite sign; let `s`, the shift, be
`0` at the letter two steps back. If `b < K p ^ 2` and `V + 4 η ≤ W ≤ K`, then the gap is long with
`J = 1`, `s₀ = ⌊b / p⌋ + 12 K` and `ω = G + W`: the windows before `i` end at or below `ω`, and `b`
exceeds `s₀ + ω (1 + p)`. -/
lemma _root_.New.Lift.KummerChart.Letter.isLongGap_two_zero {ε : k.Letter → ℤˣ}
    {s β : k.Letter → ℕ} {η V W b G K : ℕ} (hk : k.IsUnramified) (hp : 7 ≤ p)
    {i : k.Letter} (hβ_pivot : β i = b) (hβ_prev : β (i.stepBack 1) = G)
    (h_shift : s (i.stepBack 2) = 0) (h_sign : ε (i.stepBack 1) ≠ ε (i.stepBack 0))
    (hG_le : G + 7 * K ≤ b / p) (hbK : b < K * p ^ 2) (hW : V + 4 * η ≤ W) (hWK : W ≤ K) :
    i.IsLongGap ε s β η V 1 (b / p + 12 * K) (G + W) 2 0 := by
  -- The left side is at most `(p + 2) (b / p) - (6 p - 6) K`, which is less than `b`.
  have h_lt_pivot : b / p + 12 * K + (G + W) * (1 + p) < b := by
    have hK_seven : K * 7 ≤ K * p := mul_le_mul_right hp K
    have h_div_le : b / p * p ≤ b := b.div_mul_le_self p
    have h_div_lt : b / p < K * p := Nat.div_lt_of_lt_mul (by lia)
    have h_mul : (G + W + 6 * K) * (1 + p) ≤ b / p * (1 + p) := Nat.mul_le_mul_right _ (by omega)
    lia
  have h_prev (a : ℕ) (ha : a < 2) (ha_ne : a ≠ 0) : a = 1 := by omega
  exact
    { isUnramified := hk
      five_le := by omega
      shift_eq_zero := h_shift
      pivot_add := rfl
      lt_far_pivot := by simpa [sum_range_succ, hβ_pivot] using h_lt_pivot
      sign_ne_or_far_le a ha ha_ne := .inl (by rwa [h_prev a ha ha_ne])
      low_le := by omega
      far_le a ha ha_pos := by grind [h_prev a ha ha_pos.ne'] }

/-- Frobenius sends the letter `a + 1` steps before `i` to the letter `a` steps before `i`. -/
lemma _root_.New.Lift.KummerChart.Letter.letterFrob_stepBack_succ (i : k.Letter) (a : ℕ) :
    k.letterFrob (i.stepBack (a + 1)) = i.stepBack a := by
  simp [pow_succ]

/-- Suppose `cut` holds at every letter `i` with `T i` and at every letter `i` with
`¬T (k.letterFrob i)`, where `k.letterFrob` sends a letter `x` to `x ^ p`. Then `cut (i.stepBack 1)`
or `cut (i.stepBack 2)` holds, that is, `cut` holds at one of the two letters before `i`. -/
lemma _root_.New.Lift.KummerChart.Letter.cut_stepBack_one_or_two {cut T : k.Letter → Prop}
    (h_cut_thick : ∀ i : k.Letter, T i → cut i)
    (h_cut_thin : ∀ i : k.Letter, ¬T (k.letterFrob i) → cut i) (i : k.Letter) :
    cut (i.stepBack 1) ∨ cut (i.stepBack 2) := by
  by_cases h_thick : T (i.stepBack 1)
  · exact .inl (h_cut_thick _ h_thick)
  · exact .inr (h_cut_thin _ (by rwa [i.letterFrob_stepBack_succ 1]))

/-- On an unramified chart with `p ≥ 7`, let the far windows start at `b` at the b-letters (those
with `T`) and at `G` at the others, the thin ones. Let the shifts be at most `⌊b / p⌋ - 7 K`, and
`0` at the letters with a thin successor, where `0 < G`, `b < K p ^ 2` and `V + 4 η ≤ W ≤ K`. The
cuts are the letters whose shift is less than the start of their far window; let the b-letters and
the letters with a thin successor be cuts. If `i.stepBack l` is the nearest cut before `i`, then
each of the `l` letters after it has the sign of `i` or a far window that ends at or below `η`
(`HasSignBefore`), or there is a long gap with pivot `i` (pivot index `0`): its window starts beyond
`s₀ + ω (1 + p)`, for `s₀ = ⌊b / p⌋ + 12 K` and `ω = G + W`, and the letter before has the opposite
sign. -/
lemma _root_.New.Lift.KummerChart.Letter.IsNearestCut.hasSignBefore_or_isLongGap_of_two_sizes
    {T : k.Letter → Prop} {ε : k.Letter → ℤˣ} {s β : k.Letter → ℕ} {η V W b G K : ℕ}
    {i : k.Letter} {l : ℕ} (h_nearest : i.IsNearestCut (fun i' : k.Letter ↦ s i' < β i') l)
    (hk : k.IsUnramified) (hp : 7 ≤ p) (hβ_thick : ∀ i : k.Letter, T i → β i = b)
    (hβ_thin : ∀ i : k.Letter, ¬T i → β i = G) (hs_le : ∀ i : k.Letter, s i ≤ b / p - 7 * K)
    (hs_thin_succ : ∀ i : k.Letter, ¬T (k.letterFrob i) → s i = 0)
    (h_cut_thick : ∀ i : k.Letter, T i → s i < β i)
    (h_cut_thin_succ : ∀ i : k.Letter, ¬T (k.letterFrob i) → s i < β i)
    (hG_pos : 0 < G) (hbK : b < K * p ^ 2) (hW : V + 4 * η ≤ W) (hWK : W ≤ K) :
    i.HasSignBefore ε β η V l (ε (i.stepBack 0)) ∨
      i.IsLongGap ε s β η V 1 (b / p + 12 * K) (G + W) l 0 := by
  have hl_le : l ≤ 2 := by
    by_contra hl_gt
    obtain h_one | h_two := i.cut_stepBack_one_or_two h_cut_thick h_cut_thin_succ
    · exact h_nearest.not_cut 1 (by grind) h_one
    · exact h_nearest.not_cut 2 (by grind) h_two
  by_cases h_opposite : l = 2 ∧ ε (i.stepBack 1) ≠ ε (i.stepBack 0)
  · -- The letter before `i` is not a cut, so it is not a b-letter and `i` is a b-letter.
    obtain ⟨rfl, h_sign⟩ := h_opposite
    have h_not_cut : ¬s (i.stepBack 1) < β (i.stepBack 1) := h_nearest.not_cut 1 (by simp)
    have h_prev_thin : ¬T (i.stepBack 1) := mt (h_cut_thick _) h_not_cut
    have h_thick : T i := by
      by_contra h_thin
      exact h_not_cut (h_cut_thin_succ _ (by rwa [i.letterFrob_stepBack_succ 0]))
    -- As that letter is not a cut, `0 < G ≤ s (i.stepBack 1) ≤ b / p - 7 K`.
    have hβ_prev : β (i.stepBack 1) = G := hβ_thin _ h_prev_thin
    have hG_le : G + 7 * K ≤ b / p := by grind [hs_le (i.stepBack 1)]
    have h_shift : s (i.stepBack 2) = 0 := hs_thin_succ _ (by rwa [i.letterFrob_stepBack_succ 1])
    exact .inr (Letter.isLongGap_two_zero hk hp (hβ_thick i h_thick) hβ_prev h_shift h_sign
      hG_le hbK hW hWK)
  · refine .inl fun r hr ↦ .inl ?_
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    · rfl
    · exact by_contra fun h_sign ↦ h_opposite ⟨by omega, h_sign⟩

/-- Let the Kummer chart `k` over `Γ` be unramified, and let the fixed prime `p` be at least `7`.
Let the sides `S`, `S'`, paired by `h`, have their jumps at each letter `i` in `[-η, η]` and in
opposite far windows of signs `∓ε i` and width `V`, which start at `b` at the b-letters (those with
`T i`) and at `G` at the others, where `0 < G ≤ b`, `η ≥ 1` and `V + 4 η ≤ W`. If `b < K p ^ 2`,
`2 G < K p` and `W ≤ K`, then the cup product of the cocycles `S.cocycleMap c` and `p ^ (10⁴
(K + ⌊log_p (2 (b + W))⌋)) • S'.cocycleMap c'` is a coboundary. -/
lemma SidePairing.isScaledCupCoboundary_any_pattern {T : k.Letter → Prop} [DecidablePred T]
    {ε : k.Letter → ℤˣ} {η V W b G K : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (if T i then b else G) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (if T i then b else G) V (S'.jumpSet i))
    (hk : k.IsUnramified) (hp : 7 ≤ p) (hG_pos : 0 < G) (hGb : G ≤ b) (hbK : b < K * p ^ 2)
    (hGK : 2 * G < K * p) (hWK : W ≤ K) (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary (10 ^ 4 * (K + p.log (2 * (b + W)))) c c' := by
  -- Apply `isScaledCupCoboundary_of_cut_windows` with `J = 1`. A letter whose successor is a
  -- b-letter has shift `b / p - 7 K`, the others have shift `0`; the cuts are the letters with
  -- `s i < β i`.
  let β (i : k.Letter) : ℕ := if T i then b else G
  let s (i : k.Letter) : ℕ := if T (k.letterFrob i) then b / p - 7 * K else 0
  let X : ℕ := 3 * K + p.log (2 * (b + W))
  let κ : ℕ := 12 * (2 * X + 4 * K) + 1
  let s₀ : ℕ := b / p + 12 * K
  have hβ_thick (i : k.Letter) (hi : T i) : β i = b := ite_eq_left hi
  have hβ_thin (i : k.Letter) (hi : ¬T i) : β i = G := ite_eq_right hi
  have hβ_le (i : k.Letter) : β i ≤ b := by grind
  have hs_thin_succ (i : k.Letter) (hi : ¬T (k.letterFrob i)) : s i = 0 := ite_eq_right hi
  have hs_le (i : k.Letter) : s i ≤ b / p - 7 * K := by grind
  have h_sizes : k.CutSizes s β W X (4 * K) κ (b + W) K 1 s₀ (G + W) :=
    cutSizes_of_isUnramified hk hp hβ_le hs_le hbK hGK hWK
  have h_shift (i : k.Letter) : s i + W ≤ p * K := by
    have hK_seven : 7 * K ≤ p * K := Nat.mul_le_mul_right K hp
    have h_div_lt : b / p < p * K := Nat.div_lt_of_lt_mul (by lia)
    calc s i + W ≤ b / p - 7 * K + K := Nat.add_le_add (hs_le i) hWK
      _ ≤ p * K := by omega
  -- A cut with a thin successor has shift `0`; one whose successor is a b-letter has
  -- `s₀ ≤ s i + 19 K`.
  have h_killing (i : k.Letter) (hi : s i < β i) : i.IsKillingCut s β W 1 (G + W) s₀ κ := by
    by_cases h_thick : T (k.letterFrob i)
    · refine .of_isUnramified hi hk (by omega) ?_
      simp only [s, ite_eq_left h_thick]
      omega
    · refine .of_thin (hs_thin_succ i h_thick) fun t ht ↦ ?_
      obtain rfl : t = 1 := by simpa using ht
      rw [pow_one, hβ_thin _ h_thick]
  -- Thick letters are cuts, and so are the letters with a thin successor.
  have h_cut_thick (i : k.Letter) (hi : T i) : s i < β i :=
    calc s i ≤ b / p := (hs_le i).trans (Nat.sub_le _ _)
      _ < b := Nat.div_lt_self (hG_pos.trans_le hGb) (by omega)
      _ = β i := (hβ_thick i hi).symm
  have h_cut_thin_succ (i : k.Letter) (hi : ¬T (k.letterFrob i)) : s i < β i :=
    calc s i < G := by rwa [hs_thin_succ i hi]
      _ ≤ β i := by grind
  have h_cut_before (i : k.Letter) :
      ∃ l ∈ Set.Ioc 0 (2 * 1 + 1), s (i.stepBack l) < β (i.stepBack l) :=
    (i.cut_stepBack_one_or_two h_cut_thick h_cut_thin_succ).elim (⟨1, by simp, ·⟩) (⟨2, by simp, ·⟩)
  have h_gap (i : k.Letter) (l : ℕ) (h_nearest : i.IsNearestCut (fun i' ↦ s i' < β i') l) :
      ∃ t : ℕ, i.HasSignBefore ε β η V l (ε (i.stepBack t)) ∨
        i.IsLongGap ε s β η V 1 s₀ (G + W) l t :=
    ⟨0, h_nearest.hasSignBefore_or_isLongGap_of_two_sizes hk hp hβ_thick hβ_thin hs_le hs_thin_succ
      h_cut_thick h_cut_thin_succ hG_pos hbK hW hWK⟩
  have h_exponent : 51 * κ ≤ 10 ^ 4 * (K + p.log (2 * (b + W))) := by lia
  exact h.isScaledCupCoboundary_of_cut_windows hη hW hU hU' h_sizes h_shift h_killing h_cut_before
    h_gap h_exponent c c'

end PairingSide

end SparseThickLetters

end New.Lift.KummerChart
