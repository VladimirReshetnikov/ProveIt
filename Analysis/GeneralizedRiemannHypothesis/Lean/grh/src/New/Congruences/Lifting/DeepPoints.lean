import New.Congruences.Lifting.SafeMoves

/-!
# Deep points and scaled cup coboundaries for a gap below zero or nonpositive jumps

A side `S` (`New.Lift.KummerChart.PairingSide`) has sets `S.jumpSet i` that hold the jumps at
each letter `i`. `S.pointsOver c i κ lo o` is the set of points over `p ^ κ c` at the letter `i`,
with orders `lo` and depth `o`. The steps from a depth `o` to a depth `o'` are the integers `y`
with `o l u ≤ y < o' l u`, each taken at its level `l`. The level `0` belongs to the prime `E` of
the chart `k`, and `d = k.differentBound`. This file raises the depth of points when all steps
occur at the level `0`, and bounds the cost of this with `New.Lift.KummerChart.cost`. It deduces
the cup conditions for paired sides in two cases: when no jump lies in `[-a, 0)`, and when the
chart is unramified and all jumps of the second side lie in `[-η, 0]`.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_noMultipleNear`: the depth can be raised
  at a cost of `p ^ ((8 n + 4) d)`. This needs every step to occur at `E` and within distance `n` of
  `0`, `b` or `-b`, and `p` to divide no nonzero integer within `n` of these.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_gap`,
  `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_jumps_nonpos`: the cup
  conditions when no jump lies in `[-a, 0)`, and when all jumps of `S'` lie in `[-η, 0]`.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_killsCokernel`: paired
  sides satisfy the cup conditions with exponent `H` when `3 (κ + (48 (a + η + W) + 4) d) ≤ H`. The
  hypotheses are these. The cokernels are killed. The jumps lie in opposite windows. At every `i`,
  `p` divides no nonzero integer within `6 (a + η + W)` of `0`, `b i` or `-b i`. Either no jump lies
  in `[-a, 0)`, or the chart is unramified and all jumps of `S'` lie in `[-η, 0]`.

Notions from other files:
* `New.Lift.KummerChart`: a Kummer chart `k` of the group `Γ` over `G_p`: a ring `Λ⟦z⟧` inside
  `A_inf` with a distinguished element `E` (`E = z + p` if the chart is unramified) and a subgroup
  `Γ'` of `Γ` of index prime to `p`. Its letters are the units of the residue field
  `𝔽_{p ^ k.f}`; a letter singles out embeddings of the coefficients, and `i.stepBack l` is the
  letter `l` steps of Frobenius before `i`.
* `New.Lift.KummerChart.PairingSide`: one side of a pairing: lattices `Y` and `paramLattice`, an
  `O`-linear map `cocycleMap` from `paramLattice` to the crystalline cocycles `Z_f(Y)`, and for each
  letter a finite set of integers that contains `0`. `S.extensionLattice` is the extension of the
  trivial lattice `paramLattice` by `Y` given by the cocycles of `S`, with the jump sets of `S`.
* Orders `o l u` prescribe, for every level `l` and jump `u` at `i.stepBack l`, a power of the
  uniformiser of `B_dR⁺` that divides the value of an element on the line `u` at the level `l`. An
  element has depth `o` if its differences with its translates by `Γ'` have orders `o`.
* `New.Lift.KummerChart.cost`: the cost `k.cost l n = v_p(n) + d + 3 l` of the step `n` at the level
  `l`, with `v_p(0) = 0`; here `d = 0` if the index `e` of the chart is `1`, and `d = v_p(e) + 1`
  otherwise.
* `New.Lift.KummerChart.PairingSide.KillsCokernel`: `p ^ κ * E ^ a` kills the cokernel at the letter
  `i`: it multiplies the letter-`i` part of `A_inf ⊗ C` into the image of the extension's module of
  standard exponents of level `0`.
* `New.Lift.FitsWindows`: `FitsWindows η ε b W U` says that `U` lies in the union of the low window
  `[-η, η]` and the far window `ε • [b, b + W]`.
* `New.Lift.Pairing.IsScaledCupCoboundary`: the cup conditions with exponent `H` for `c` and `c'`:
  the cup product of the cocycles `S.cocycleMap c` and `p ^ H • S'.cocycleMap c'` is a continuous
  coboundary.

## Relation to the literature

See `New.Congruences.Lifting.FewLowJumps` for related work.
-/

namespace New.Lift.KummerChart.PairingSide

open Finset JumpLattice Period Int

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
variable {k : KummerChart Γ} {O : Coeffs} {S S' : PairingSide O}

/-- Let `p` divide no nonzero integer within `n` of `0`, `b` or `-b`. For a Kummer chart `k`, the
cost of the step `y` at the level `0` is `k.cost 0 y = v_p(y) + k.differentBound`. These costs over
the integers within `n` of `0`, `b` or `-b` add up to at most `(8 n + 4) k.differentBound`. -/
lemma sum_cost_le_of_noMultipleNear {n : ℕ} {b : ℤ} (hb_gap : NoMultipleNear p n b) :
    ∑ y ∈ twoWindows n b ∪ twoWindows n (-b), k.cost 0 y ≤ (8 * n + 4) * k.differentBound := by
  -- The set is a union of four intervals of `2 n + 1` integers.
  have h_card : #(twoWindows n b ∪ twoWindows n (-b)) ≤ 8 * n + 4 := by
    grw [card_union_le, card_union_le, card_union_le]
    grind [card_Icc]
  -- By the gap condition each step is `0` or prime to `p`, so it costs `k.differentBound`.
  have h_step : ∀ y ∈ twoWindows n b ∪ twoWindows n (-b), k.cost 0 y ≤ k.differentBound := by
    intro y hy
    have h_zero : (p : ℤ) ∣ y → y = 0 := hb_gap.eq_zero_of_dvd hy
    have h_val : padicValInt p y = 0 := padicValInt.eq_zero_iff.2 (by tauto)
    simp [cost, h_val]
  grw [sum_le_card_nsmul _ _ _ h_step, h_card, smul_eq_mul]

/-- The integers within `n` of `0`, `b` or `-b`, described by inequalities. -/
lemma mem_twoWindows_union_iff {n : ℕ} {b y : ℤ} :
    y ∈ twoWindows n b ∪ twoWindows n (-b) ↔
      -n ≤ y ∧ y ≤ n ∨ b - n ≤ y ∧ y ≤ b + n ∨ -b - n ≤ y ∧ y ≤ -b + n := by
  grind

/-- Deepening at the level `0`. Let the side `S` have a point over `p ^ κ • c` at the letter `i`
with exponents `lo` and depth `o`. If all steps `y` from `o` to the depth `o'` are at the level `0`
and lie in a set `steps` of total cost at most `stepCost`, then `S` has a point over
`p ^ (κ + stepCost) • c` at `i` with depth `o'` and exponents `improvedOrders lo o'` (that is, `o'`
where `lo` is positive and `min o' 0` elsewhere). -/
lemma pointsOver_nonempty_of_steps_level_zero {κ stepCost : ℕ} {i : k.Letter} {c : S.paramLattice}
    {lo o o' : ℕ → ℤ → ℤ} {steps : Finset ℤ} (h_point : (S.pointsOver c i κ lo o).Nonempty)
    (h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, o l u ≤ y → y < o' l u →
      l = 0 ∧ y ∈ steps)
    (h_cost : ∑ y ∈ steps, k.cost 0 y ≤ stepCost) :
    (S.pointsOver c i (κ + stepCost) (improvedOrders lo o') o').Nonempty := by
  obtain ⟨x, hx⟩ := h_point
  exact pointsOver_nonempty_of_costs hx (({0} : Finset ℕ).sigma fun _ ↦ steps)
    (by simpa using h_steps) (by simpa [sum_sigma] using h_cost)

/-- Deepening under the gap condition. Let `p` divide no nonzero integer within `n` of `0`, `b` or
`-b`. A point of the side `S` over `p ^ κ • c` at the letter `i` is an element of the extension that
the cocycles of `S` define, mapping to `p ^ κ` times the letter-`i` part of `1 ⊗ c`. Its orders `lo`
and its depth `o` prescribe, at each level `l` and each jump `u ∈ S.jumpSet (i.stepBack l)`, the
orders of the values of the element, and of its differences with its translates by the group of the
chart. Given such a point, suppose that all steps `y` with `o l u ≤ y < o' l u` are at the level `0`
and within `n` of `0`, `b` or `-b`. Then there is a point over
`p ^ (κ + (8 n + 4) k.differentBound) • c` at `i` with depth `o'` and orders
`improvedOrders lo o'`. -/
lemma pointsOver_nonempty_of_noMultipleNear {κ : ℕ} {i : k.Letter} {c : S.paramLattice}
    {lo o : ℕ → ℤ → ℤ}
    {n : ℕ} {b : ℤ} (h_point : (S.pointsOver c i κ lo o).Nonempty) (hb_gap : NoMultipleNear p n b)
    (o' : ℕ → ℤ → ℤ)
    (h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, o l u ≤ y → y < o' l u →
      l = 0 ∧ y ∈ twoWindows n b ∪ twoWindows n (-b)) :
    Set.Nonempty
      (S.pointsOver c i (κ + (8 * n + 4) * k.differentBound) (improvedOrders lo o') o') :=
  pointsOver_nonempty_of_steps_level_zero h_point h_steps (sum_cost_le_of_noMultipleNear hb_gap)

/-- Deep points under a gap below `0`. Let `p ^ κ * E ^ a` kill the cokernel of the side `S` at the
letter `i`. Let no jump lie in `[-a, 0)`, and let the set `steps` contain `[-u - a, a + η - u)` for
every jump `u` at `i`, with sum of the costs `k.cost 0 y = v_p(y) + k.differentBound` at most
`stepCost`. Then `S` has a point over `p ^ (κ + stepCost) • c` at `i` without pole and of depth
`plainDepth a η 1 0`, which is `a + η - u` at the level `0` and `-u` at the levels above. -/
lemma pointsOver_nonempty_of_gap {a κ η stepCost : ℕ} {i : k.Letter}
    (h_kill : S.KillsCokernel i κ a)
    (h_gap : ∀ u ∈ S.jumpSet i, u ∉ Ico (-a : ℤ) 0) {steps : Finset ℤ}
    (h_steps : ∀ u ∈ S.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps)
    (h_cost : ∑ y ∈ steps, k.cost 0 y ≤ stepCost) (c : S.paramLattice.Carrier) :
    (S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero 0) (plainDepth a η 1 0)).Nonempty := by
  -- Deepen a point with a pole of order `a` along `steps`; by the gap the pole disappears.
  have h_cover : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, raisedOrdersAtZero (-a) l u ≤ y →
      y < plainDepth a η 1 0 l u → l = 0 ∧ y ∈ steps := by
    intro l u hu y hy_ge hy_lt
    obtain ⟨rfl, hy⟩ : l = 0 ∧ -u - a ≤ y ∧ y < a + η - u := by
      grind [raisedOrdersAtZero, plainDepth, standardDepth]
    exact ⟨rfl, h_steps u hu (mem_Ico.2 hy)⟩
  obtain ⟨x, hx⟩ : Set.Nonempty (S.pointsOver c i (κ + stepCost)
      (improvedOrders (raisedOrdersAtZero (-a)) (plainDepth a η 1 0)) (plainDepth a η 1 0)) :=
    pointsOver_nonempty_of_steps_level_zero (pointsOver_nonempty_of_killsCokernel h_kill c)
      h_cover h_cost
  have h_nonneg : ∀ u ∈ S.jumpSet i, -(a : ℤ) ≤ u → -0 ≤ u := fun u hu ↦ by grind [h_gap u hu]
  have h_no_pole :
      x ∈ S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero (-0)) (plainDepth a η 1 0) :=
    mem_pointsOver_raisedOrdersAtZero_of_gap hx le_rfl h_nonneg
      (fun l u _ ↦ by grind [raisedOrdersAtZero, plainDepth, standardDepth])
      fun l u _ ↦ by grind [raisedOrdersAtZero, plainDepth, standardDepth]
  exact ⟨x, by simpa only [neg_zero] using h_no_pole⟩

/-- The scaled cup coboundary under a gap below `0`. Let `P` be a pairing of the lattices of the
sides `S` and `S'`, and `P.tateDualSide` the side on the Tate dual of their tensor product that
carries the pairing. Here a side is a lattice with a family of crystalline cocycles and, at each
letter `i` of the chart `k` (a unit of its residue field), a finite set `jumpSet i` of integers. At
every letter let `p ^ κ * E ^ a`, with `E` the distinguished element of the chart, kill the
cokernels of `S`, `S'` and `P.tateDualSide`. Let the jumps of `S` lie in `[-η, η]` or in
`-ε i • [b i, b i + W]`, those of `S'` in `[-η, η]` or in `ε i • [b i, b i + W]` for a sign
`ε i = ±1`, none of them in `[-a, 0)`. Let `steps i` contain `[-u - a, a + η - u)` for every jump
`u` at `i`, with sum of the costs `k.cost 0 y = v_p(y) + k.differentBound` at most `stepCost`. Then
for `H ≥ 3 κ + 2 stepCost` the cup product of the cocycles that `S` and `S'` attach to `c` and
`p ^ H • c'` is a continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_gap (P : S.SidePairing S') {a κ η H W : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ} {stepCost : ℕ}
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (h_kill' : ∀ i : k.Letter, S'.KillsCokernel i κ a)
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_window' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (S'.jumpSet i))
    (h_gap : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ∉ Ico (-a : ℤ) 0)
    (h_gap' : ∀ i : k.Letter, ∀ u ∈ S'.jumpSet i, u ∉ Ico (-a : ℤ) 0) (steps : k.Letter → Finset ℤ)
    (h_steps : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps i)
    (h_steps' : ∀ i : k.Letter, ∀ u ∈ S'.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps i)
    (h_cost : ∀ i : k.Letter, ∑ y ∈ steps i, k.cost 0 y ≤ stepCost) (hH : 3 * κ + 2 * stepCost ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  -- Both sides have deep points without pole at every letter. At each letter the side whose far
  -- window is negative has jumps at most `η`; it provides a stop, a point at which it rests while
  -- the other side moves by Frobenius.
  have h_left (i : Letter) :
      ∃ x, x ∈ S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero 0) (plainDepth a η 1 0) :=
    pointsOver_nonempty_of_gap (h_kill i) (h_gap i) (h_steps i) (h_cost i) c
  have h_right (i : Letter) :
      ∃ x', x' ∈ S'.pointsOver c' i (κ + stepCost) (raisedOrdersAtZero 0) (plainDepth a η 1 0) :=
    pointsOver_nonempty_of_gap (h_kill' i) (h_gap' i) (h_steps' i) (h_cost i) c'
  choose x hx_no_pole using h_left
  choose x' hx'_no_pole using h_right
  have hx (i : Letter) : x i ∈ S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero (-η))
    (plainDepth a η 1 0) :=
    mem_pointsOver_of_exponent_le (hx_no_pole i) fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u
  have hx' (i : Letter) :
      x' i ∈ S'.pointsOver c' i (κ + stepCost) (raisedOrdersAtZero (-η)) (plainDepth a η 1 0) :=
    mem_pointsOver_of_exponent_le (hx'_no_pole i) fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u
  refine P.isScaledCupCoboundary_of_stops_at_all_letters x x' h_kill_tateDual
    (fun i ↦ mem_standardPoints_of_plainDepth (hx i))
    (fun i ↦ mem_standardPoints_of_plainDepth (hx' i)) (fun i ↦ ?_) (by omega)
  obtain Pε | Pε := units_eq_one_or (ε i)
  · have h_down : ∀ u ∈ S.jumpSet i, u ≤ η :=
      jump_le_of_fitsWindows (h_window i) (.inl (neg_inj.2 Pε))
    have h_up : ∀ u ∈ S'.jumpSet i, -η ≤ u := neg_le_jump_of_fitsWindows (h_window' i) (.inl Pε)
    exact .inl (P.exists_mem_stopPoints_isSafeMoveSnd one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx i) (hx' i) (hx'_no_pole (i.stepBack 1)))
  · have h_down : ∀ u ∈ S'.jumpSet i, u ≤ η := jump_le_of_fitsWindows (h_window' i) (.inl Pε)
    have h_up : ∀ u ∈ S.jumpSet i, -η ≤ u :=
      neg_le_jump_of_fitsWindows (h_window i) (.inl (neg_eq_iff_eq_neg.2 Pε))
    exact .inr (P.exists_mem_stopPoints_isSafeMoveFst one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx' i) (hx i) (hx_no_pole (i.stepBack 1)))

/-- Free steps. Let the Kummer chart be unramified, let `p` divide no nonzero integer within `n` of
`0`, `β` or `-β`, and let the side `S` have a point over `p ^ κ • c` at the letter `i` with orders
`lo` and depth `o`: an element of the extension over that constant whose values at each level `l`
and jump `u ∈ S.jumpSet (i.stepBack l)` have order at least `lo l u`, and whose differences with its
translates by the group of the chart have order at least `o l u`. If all steps `y` with
`o l u ≤ y < o' l u` are at the level `0` and within `n` of `0`, `β` or `-β`, then `S` has a point
over the same `p ^ κ • c` with depth `o'` and any orders `lo' ≤ improvedOrders lo o'`. -/
lemma pointsOver_nonempty_of_near_steps {κ : ℕ} {i : k.Letter} {c : S.paramLattice.Carrier}
    {lo lo' o o' : ℕ → ℤ → ℤ} {n : ℕ} {β : ℤ} (hk : k.IsUnramified)
    (hβ_gap : NoMultipleNear p n β) (h_point : (S.pointsOver c i κ lo o).Nonempty)
    (h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, o l u ≤ y → y < o' l u →
      l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β))
    (h_exponent : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), lo' l u ≤ improvedOrders lo o' l u) :
    (S.pointsOver c i κ lo' o').Nonempty := by
  obtain ⟨-, -, h_free : k.differentBound = 0⟩ := hk
  obtain ⟨y, hy⟩ := pointsOver_nonempty_of_noMultipleNear h_point hβ_gap o' h_steps
  rw [h_free, mul_zero, add_zero] at hy
  exact ⟨y, mem_pointsOver_of_exponent_le hy h_exponent⟩

/-- Let the chart be unramified (`E = z + p`), let `p ^ κ * E ^ a` kill the cokernel of the side
`S` at the letter `i` (it lifts each constant at `i` to the extension with standard orders), and let
the jumps, the elements of `S.jumpSet i`, lie in `[-η, η]` or in `σ • [β, β + W]`. Let `a ≤ t`, and
let `p` divide no nonzero integer within `n ≥ a + t + η + W` of `0` or `± β`. Then `S` has a point
over `p ^ κ • c` at `i` with a pole of order at most `t` (its orders `raisedOrdersAtZero (-t)` are
`-t - u` at the level `0` on the line of a jump `u`) and of depth `plainDepth a t 1 0`, which is
`a + t - u` at the level `0` and `-u` at the levels above. -/
lemma pointsOver_nonempty_of_fitsWindows {a κ η W t n β : ℕ} {σ : ℤˣ} {i : k.Letter}
    (hk : k.IsUnramified) (h_kill : S.KillsCokernel i κ a) (hβ_gap : NoMultipleNear p n β)
    (h_window : FitsWindows η σ β W (S.jumpSet i)) (hat : a ≤ t) (hn : a + t + η + W ≤ n)
    (c : S.paramLattice.Carrier) : (S.pointsOver c i κ (raisedOrdersAtZero (-t))
      (plainDepth a t 1 0)).Nonempty := by
  have h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, raisedOrdersAtZero (-a) l u ≤ y →
      y < plainDepth a t 1 0 l u → l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β) := by
    intro l u hu y hy_ge hy_lt
    obtain ⟨rfl, hy⟩ : l = 0 ∧ -u - a ≤ y ∧ y < a + t - u := by
      grind [raisedOrdersAtZero, plainDepth, standardDepth]
    have hu_window : -η ≤ u ∧ u ≤ η ∨ β ≤ u ∧ u ≤ β + W ∨ β ≤ -u ∧ -u ≤ β + W :=
      low_or_far_of_fitsWindows h_window hu
    grind
  have h_exponent (l : ℕ) (u : ℤ) :
      raisedOrdersAtZero (-t) l u ≤ improvedOrders (raisedOrdersAtZero (-a)) (plainDepth a t 1 0) l
        u := by
    grind [raisedOrdersAtZero, plainDepth, standardDepth]
  exact pointsOver_nonempty_of_near_steps hk hβ_gap
    (pointsOver_nonempty_of_killsCokernel h_kill c) h_steps fun l u _ ↦ h_exponent l u

/-- Let the chart be unramified, let all jumps of the side `S` lie in `[-η, 0]`, and let `p` divide
no nonzero integer within `n ≥ a + t + η` of `0` or `± β`. Then at every letter `i` the side `S` has
a point without pole over the constant `S.constantAt i c` of `c`: on the line of each jump `u` its
orders are `-u` at every level. Its depth, the orders of its differences with its translates by the
group of the chart, is `plainDepth a t 1 0`: this is `a + t - u` at the level `0` and `-u` at the
levels above. -/
lemma pointsOver_nonempty_of_jumps_nonpos {a η t n : ℕ} {β : ℤ} (hk : k.IsUnramified)
    (hβ_gap : NoMultipleNear p n β) (hn : a + t + η ≤ n)
    (h_nonpos : ∀ j : k.Letter, S.jumpSet j ⊆ Finset.Icc (-η : ℤ) 0) (c : S.paramLattice.Carrier)
      (i : k.Letter) :
    (S.pointsOver c i 0 (raisedOrdersAtZero 0) (plainDepth a t 1 0)).Nonempty := by
  -- As the jumps are at most `0`, the element `1 = p ^ 0 * E ^ 0` kills the cokernel.
  have h_kill : S.KillsCokernel i 0 0 := killsCokernel_zero_zero_of_small_jumps (ω := 0)
    (fun j u hu ↦ (mem_Icc.1 (h_nonpos j hu)).2) (Nat.zero_le _) i
  have h_point : (S.pointsOver c i 0 (raisedOrdersAtZero 0) (raisedOrdersAtZero 0)).Nonempty := by
    simpa only [Nat.cast_zero, neg_zero] using pointsOver_nonempty_of_killsCokernel h_kill c
  have h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, raisedOrdersAtZero 0 l u ≤ y →
      y < plainDepth a t 1 0 l u → l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β) :=
    fun l u hu ↦ by grind [h_nonpos _ hu, raisedOrdersAtZero, plainDepth, standardDepth]
  have h_exponent : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l),
      raisedOrdersAtZero 0 l u ≤ improvedOrders (raisedOrdersAtZero 0) (plainDepth a t 1 0) l u :=
    fun l u hu ↦ by grind [h_nonpos _ hu, raisedOrdersAtZero, plainDepth, standardDepth]
  exact pointsOver_nonempty_of_near_steps hk hβ_gap h_point h_steps h_exponent

/-- On an unramified chart let the jumps `u` of the side `S'` lie in `[-η, 0]`, and let `x₀'` be a
point over `c'` at the letter `i.stepBack 1` before `i`, without pole and of depth `a + t - u` at
the level `0`, where `η ≤ t`. Let `p` divide no nonzero integer within `n ≥ a + t + η` of `0` or
`± β`. Then `S'` has a point over `c'` at `i` that can serve as a stop, that is, rest while the
other side of a pairing moves by Frobenius: its orders `stopOrders t 1` are `max 0 (-u - t)` at the
level `0` and `-u` above, and its depth is `a + t - u`, `t - u` and `-u` at the level `0`, the level
`1` and above. -/
lemma pointsOver_stopOrders_nonempty {a η : ℕ} {i : k.Letter} {c' : S'.paramLattice.Carrier}
  {t n : ℕ}
    {β : ℤ} {x₀' : S'.extensionLattice.Ambient} (hk : k.IsUnramified)
      (hβ_gap : NoMultipleNear p n β)
    (hn : a + t + η ≤ n) (hηt : η ≤ t) (h_nonpos : ∀ j : k.Letter,
      S'.jumpSet j ⊆ Finset.Icc (-η : ℤ) 0)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack 1) 0 (raisedOrdersAtZero 0) (plainDepth a t 1 0)) :
    (S'.pointsOver c' i 0 (stopOrders t 1) (plainDepth a t 1 t)).Nonempty := by
  -- Frobenius shifts orders and depth by one level (`shiftedOrders`), which supplies the depth at
  -- the level `1`; the depth at the level `0` is then raised from `1`.
  have h_frob : FrobGroup.φ ^ 1 • x₀' ∈ S'.pointsOver c' i 0
      (shiftedOrders 1 0 (raisedOrdersAtZero 0)) (shiftedOrders 1 1 (plainDepth a t 1 0)) :=
    phi_pow_smul_mem_pointsOver hx₀'
  have h_steps : ∀ l : ℕ, ∀ u ∈ S'.jumpSet (i.stepBack l), ∀ y : ℤ,
      shiftedOrders 1 1 (plainDepth a t 1 0) l u ≤ y → y < plainDepth a t 1 t l u →
      l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β) :=
    fun l u hu ↦ by grind [h_nonpos _ hu, plainDepth, standardDepth]
  have h_exponent : ∀ l : ℕ, ∀ u ∈ S'.jumpSet (i.stepBack l), stopOrders t 1 l u ≤
      improvedOrders (shiftedOrders 1 0 (raisedOrdersAtZero 0)) (plainDepth a t 1 t) l u :=
    fun l u hu ↦ by
      grind [h_nonpos _ hu, stopOrders, stdOrders, raisedOrdersAtZero, plainDepth, standardDepth]
  exact pointsOver_nonempty_of_near_steps hk hβ_gap ⟨_, h_frob⟩ h_steps h_exponent

/-- Let the chart be unramified, let `P` be a pairing of the lattices of the sides `S` and `S'`, and
`P.tateDualSide` the side on the Tate dual of their tensor product that carries the pairing. At
every letter `i` let `p ^ κ * E ^ a`, with `E = z + p` the distinguished element of the chart, kill
the cokernels of `S` and of `P.tateDualSide`, and let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b i`. Let the jumps of `S` lie in `[-η, η]` or in
`-ε i • [b i, b i + W]` for a sign `ε i = ±1`, and let the jumps of `S'` lie in `[-η, 0]`. Then for
`H ≥ 2 κ` the cup product of the cocycles that `S` and `S'` attach to `c` and `p ^ H • c'` is a
continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_jumps_nonpos (P : S.SidePairing S') {a κ η H W : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ} (hk : k.IsUnramified)
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (hb_gap : ∀ i : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b i))
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_nonpos : ∀ i : k.Letter, S'.jumpSet i ⊆ Finset.Icc (-η : ℤ) 0) (hH : 2 * κ ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  -- Use the bound `t = a + η` for the poles and the low jumps. The jumps of `S'` lie in `[-t, t]`
  -- and its points have no pole. Where the far window of `S` is negative, `S` provides the stop
  -- (the point at rest while the other side moves by Frobenius); elsewhere `S'` does.
  set t : ℕ := a + η with ht
  have h_radius : a + t + η + W ≤ 6 * (t + W) := by omega
  have h_radius' : a + t + η ≤ 6 * (t + W) := by omega
  have h_left (i : Letter) : ∃ x : S.extensionLattice.Ambient,
      x ∈ S.pointsOver c i κ (raisedOrdersAtZero (-t)) (plainDepth a t 1 0) :=
    pointsOver_nonempty_of_fitsWindows hk (h_kill i) (hb_gap i) (h_window i) (by omega)
      h_radius c
  have h_right (i : Letter) : ∃ x' : S'.extensionLattice.Ambient,
      x' ∈ S'.pointsOver c' i 0 (raisedOrdersAtZero 0) (plainDepth a t 1 0) :=
    pointsOver_nonempty_of_jumps_nonpos hk (hb_gap i) h_radius' h_nonpos c' i
  choose x hx using h_left
  choose x' hx'_no_pole using h_right
  have hx' (i : Letter) : x' i ∈ S'.pointsOver c' i 0 (raisedOrdersAtZero (-t))
    (plainDepth a t 1 0) :=
    mem_pointsOver_of_exponent_le (hx'_no_pole i) fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u
  refine P.isScaledCupCoboundary_of_stops_at_all_letters x x' h_kill_tateDual
    (fun i ↦ mem_standardPoints_of_plainDepth (hx i))
    (fun i ↦ mem_standardPoints_of_plainDepth (hx' i)) (fun i ↦ ?_) (by omega)
  obtain Pε | Pε := units_eq_one_or (ε i)
  · have h_down : ∀ u ∈ S.jumpSet i, u ≤ t := by
      grind [jump_le_of_fitsWindows (h_window i) (.inl (neg_inj.2 Pε))]
    have h_up : ∀ u ∈ S'.jumpSet i, -t ≤ u := fun u hu ↦ by grind [h_nonpos i hu]
    exact .inl (P.exists_mem_stopPoints_isSafeMoveSnd one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx i) (hx' i) (hx'_no_pole (i.stepBack 1)))
  · have h_up : ∀ u ∈ S.jumpSet i, -t ≤ u := by
      grind [neg_le_jump_of_fitsWindows (h_window i) (.inl (neg_eq_iff_eq_neg.2 Pε))]
    obtain ⟨q', hq'⟩ : (S'.pointsOver c' i 0 (stopOrders t 1) (plainDepth a t 1 t)).Nonempty :=
      pointsOver_stopOrders_nonempty hk (hb_gap i) h_radius' (by omega) h_nonpos
        (hx'_no_pole (i.stepBack 1))
    have h_safe : P.IsSafeMoveFst κ (FrobGroup.φ ^ 1 • x (i.stepBack 1) - x i) q' :=
      P.isSafeMoveFst_of_neg_le_jumps one_pos (h_kill_tateDual i)
        (forall_mem_U_stepBack_of_lt_one h_up)
        (hx i)
        (hx (i.stepBack 1)) hq'
    exact .inr ⟨q', mem_stopPoints_of_mem_pointsOver hq', h_safe⟩

/-- Let `P` be a pairing of the lattices of the sides `S` and `S'`, and `P.tateDualSide` the side on
the Tate dual of their tensor product that carries the pairing. At every letter `i` let
`p ^ κ * E ^ a`, with `E` the distinguished element of the chart, kill the cokernels of `S`, `S'`
and `P.tateDualSide`, let `p` divide no nonzero integer within `n = 6 (a + η + W)` of `0` or
`± b i`, and let the jumps of `S` and `S'` lie in `[-η, η]` or in the opposite far windows
`∓ε i • [b i, b i + W]`, where `ε i = ±1`. Suppose that no jump lies in `[-a, 0)`, or that the chart
is unramified and the jumps of `S'` lie in `[-η, 0]`. Then for
`H ≥ 3 (κ + (8 n + 4) k.differentBound)` the cup product of the cocycles of `c` and `p ^ H • c'` is
a continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_killsCokernel (P : S.SidePairing S') {a κ η H W : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (h_kill' : ∀ i : k.Letter, S'.KillsCokernel i κ a)
    (hb_gap : ∀ i : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b i))
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_window' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (S'.jumpSet i))
    (h_gap_or_nonpos :
      -- no jump lies in `[-a, 0)`
      (∀ (i : k.Letter) (u : ℤ), u ∈ S.jumpSet i ∨ u ∈ S'.jumpSet i → u ∉ Ico (-a : ℤ) 0) ∨
      -- unramified chart, and the jumps of `S'` lie in `[-η, 0]`
      k.IsUnramified ∧ ∀ i : k.Letter, S'.jumpSet i ⊆ Finset.Icc (-η : ℤ) 0)
    (hH : 3 * (κ + (8 * (6 * (a + η + W)) + 4) * k.differentBound) ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  obtain h_gap | ⟨hk, h_nonpos⟩ := h_gap_or_nonpos
  · -- For jumps in a window the steps lie within `6 (a + η + W)` of `0` or `± b i`.
    have h_steps {σ : ℤˣ} {β : ℕ} {U : Finset ℤ} (hU_window : FitsWindows η σ β W U) :
        ∀ u ∈ U, Ico (-u - a) (a + η - u) ⊆
          twoWindows (6 * (a + η + W)) β ∪ twoWindows (6 * (a + η + W)) (-β) := by
      intro u hu y hy
      have hu_window : -η ≤ u ∧ u ≤ η ∨ β ≤ u ∧ u ≤ β + W ∨ β ≤ -u ∧ -u ≤ β + W :=
        low_or_far_of_fitsWindows hU_window hu
      grind
    exact P.isScaledCupCoboundary_of_gap h_kill_tateDual h_kill h_kill' h_window h_window'
      (fun i u hu ↦ h_gap i u (.inl hu)) (fun i u hu ↦ h_gap i u (.inr hu))
      (fun i ↦ twoWindows (6 * (a + η + W)) (b i) ∪ twoWindows (6 * (a + η + W)) (-b i))
      (fun i ↦ h_steps (h_window i)) (fun i ↦ h_steps (h_window' i))
      (fun i ↦ sum_cost_le_of_noMultipleNear (hb_gap i)) (by omega) c c'
  · exact P.isScaledCupCoboundary_of_jumps_nonpos hk h_kill_tateDual h_kill hb_gap h_window h_nonpos
      (by omega) c c'

end New.Lift.KummerChart.PairingSide
