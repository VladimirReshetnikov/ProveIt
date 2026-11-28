import New.Congruences.Lifting.CupProductBound

/-!
# Jump windows, the gap condition and points of the sides of a Kummer chart

This file defines windows of integers in which the jumps of lattices in a Kummer chart are required
to lie. It defines the gap condition that `p` divides no non-zero integer near 0, `b` or `-b`, and
it bounds sums of `p`-adic valuations over two windows. For one side it defines deep elements of
the extension, operators of a given cost and points of the extension over constants, and moves
points by Frobenius. It also defines pairings of sides and the standard points, stops and rule
bound used by the walk.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.pointsOver`: points of the extension over `p ^ e c`, with
  orders and a depth.
* `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_killsCokernel`,
  `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_costs`: points exist, and their depth can
  be raised at a cost in powers of `p`.

Notions from other files:
* `New.Lift.KummerChart.Letter`: the letters of a Kummer chart, that is, the multiplicative group of
  the field with p^f elements in O^♭.
* `New.Lift.KummerChart.PairingSide`: lattices Y and C with an O-linear map `cocycleMap` from C to
  the crystalline cocycles of Y, and for each letter a finite set of jumps that contains 0.
* `New.Lift.Pairing`: a pairing of Y and L modulo p^m, that is, an O-linear ψ: Y ⊗ L → O(1) with
  gψ − ψ = p^m c(g) for a crystalline cocycle c, and a Z_p-linear f: O → Z_p.
* `New.Lift.Pairing.IsSafe`: the pair (w, y) is safe for κ if p^κ times the pairing of the first
  components of w and y lies in the image of W(𝔪^♭).

## Relation to the literature

See `New.Congruences.Lifting.SafeMoves` for related work.
-/

noncomputable section

/-! ## Low and far windows of jumps, the gap condition, valuation sums -/

section Windows

open Finset Int

namespace New.Lift

/-- Every element of `U` lies in the low window `[-η, η]` or in the far window `ε [b, b + W]`, where
`ε` is a sign. -/
abbrev FitsWindows (η : ℕ) (ε : ℤˣ) (b W : ℕ) (U : Finset ℤ) : Prop :=
  ∀ u ∈ U,
    (-η ≤ u ∧ u ≤ η) ∨
    ((ε : ℤ) = 1 ∧ b ≤ u ∧ u ≤ b + W) ∨
    ((ε : ℤ) = -1 ∧ b ≤ -u ∧ -u ≤ b + W)

/-- The system of orders that is `-u` on the line `u` at every level `a`, raised by `t` at the
level `0`. -/
@[grind] def raisedOrdersAtZero (t : ℤ) (a : ℕ) (u : ℤ) : ℤ := (if a = 0 then t else 0) - u

/-- The integers within distance `n` of `0` or of `c`. -/
noncomputable abbrev twoWindows (n : ℕ) (c : ℤ) : Finset ℤ := Icc (-n : ℤ) n ∪ Icc (c - n) (c + n)

lemma mem_twoWindows {n : ℕ} {c y : ℤ} : y ∈ twoWindows n c ↔ |y| ≤ n ∨ |y - c| ≤ n := by
  grind

/-- The gap condition: `p` divides no nonzero integer within distance `n` of `0`, of `b` or
of `-b`. -/
def NoMultipleNear (p n : ℕ) (b : ℤ) : Prop :=
  ∀ y : ℤ, y ≠ 0 → |y| ≤ n ∨ |y - b| ≤ n ∨ |y + b| ≤ n → ¬(p : ℤ) ∣ y

/-- Under the gap condition, the only multiple of `p` in the windows of radius `n` around `0`,
`b` and `-b` is `0`. -/
lemma NoMultipleNear.eq_zero_of_dvd {p n : ℕ} {b y : ℤ} (h_gap : NoMultipleNear p n b)
    (hy : y ∈ twoWindows n b ∪ twoWindows n (-b)) (h_dvd : (p : ℤ) ∣ y) : y = 0 := by
  by_contra hy_ne
  exact h_gap y hy_ne (by grind) h_dvd

/-- Among the integers within `n` of `c` at most `2 n / q + 1` are multiples of `q`. -/
lemma card_filter_dvd_Icc_le (c : ℤ) (n : ℕ) {q : ℕ} (hq : 0 < q) :
    #{k ∈ Icc (c - n) (c + n) | (q : ℤ) ∣ k} ≤ 2 * n / q + 1 := by
  -- The map `k ↦ ⌊(k - (c - n)) / q⌋` is injective on the multiples, with values in `[0, 2 n / q]`.
  have hq_pos : (0 : ℤ) < q := natCast_pos.2 hq
  have h_card : #(Icc (0 : ℤ) (2 * n / q : ℕ)) = 2 * n / q + 1 := by
    rw [Int.card_Icc, sub_zero]
    norm_cast
  rw [← h_card]
  refine card_le_card_of_injOn (fun k ↦ (k - (c - n)) / q) ?_ ?_
  · intro k hk
    obtain ⟨h_lower, h_upper⟩ := mem_Icc.1 (mem_filter.1 hk).1
    refine mem_coe.2 (mem_Icc.2 ⟨ediv_nonneg (by omega) hq_pos.le, ?_⟩)
    exact_mod_cast Int.ediv_le_ediv hq_pos (by omega : k - (c - n) ≤ 2 * n)
  · intro k hk l hl h_eq
    obtain ⟨-, x, rfl⟩ := mem_filter.1 hk
    obtain ⟨-, y, rfl⟩ := mem_filter.1 hl
    simp only [sub_eq_neg_add _ (c - n), add_mul_ediv_left _ _ hq_pos.ne', add_right_inj] at h_eq
    rw [h_eq]

/-- Let `p` be prime, `n ≤ p m` and `|c| + n ≤ H`. The valuations `v_p(k)` of the integers `k`
within `n` of `c` add up to at most `4 m + ⌊log_p H⌋`, with `v_p(0) = 0`. -/
lemma sum_padicValInt_Icc_le {n p m H : ℕ} {c : ℤ} (hp : p.Prime) (hn : n ≤ p * m)
    (hH : |c| + n ≤ H) : ∑ k ∈ Icc (c - n) (c + n), padicValInt p k ≤ 4 * m + p.log H := by
  -- The valuation of `k` is at most the number of `i < log_p H` with `p ^ (i + 1) ∣ k`. For each
  -- `i`, count the multiples of `p ^ (i + 1)` in the interval.
  have : Fact p.Prime := ⟨hp⟩
  have h_val (k : ℤ) (hk : k ∈ Icc (c - n) (c + n)) :
      padicValInt p k ≤ #{i ∈ range (p.log H) | ((p ^ (i + 1) : ℕ) : ℤ) ∣ k} := by
    have hk_le : k.natAbs ≤ H := by grind
    have h_log : padicValInt p k ≤ p.log H :=
      (padicValNat_le_nat_log _).trans (Nat.log_mono_right hk_le)
    refine (card_range _).ge.trans (card_le_card fun i hi ↦ mem_filter.2 ⟨?_, ?_⟩)
    · exact mem_range.2 ((mem_range.1 hi).trans_le h_log)
    · exact_mod_cast (padicValInt_dvd_iff _ _).2 (.inr (mem_range.1 hi))
  have h_count (i : ℕ) :
      #{k ∈ Icc (c - n) (c + n) | ((p ^ (i + 1) : ℕ) : ℤ) ∣ k} ≤ 2 * m / p ^ i + 1 := by
    refine (card_filter_dvd_Icc_le c n (pow_pos hp.pos _)).trans (Nat.add_le_add_right ?_ 1)
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right (Nat.div_le_of_le_mul (by linarith))
  have h_geom : ∑ i ∈ range (p.log H), 2 * m / p ^ i ≤ 4 * m := by
    have hp_le : p ≤ 2 * (p - 1) := by grind [hp.two_le]
    refine (Nat.geom_sum_le hp.two_le _ _).trans (Nat.div_le_of_le_mul ?_)
    linarith [Nat.mul_le_mul_left (2 * m) hp_le]
  calc
    _ ≤ ∑ k ∈ Icc (c - n) (c + n), #{i ∈ range (p.log H) | ((p ^ (i + 1) : ℕ) : ℤ) ∣ k} :=
        sum_le_sum h_val
    _ = ∑ i ∈ range (p.log H), #{k ∈ Icc (c - n) (c + n) | ((p ^ (i + 1) : ℕ) : ℤ) ∣ k} := by
        simpa only [card_filter] using sum_comm
    _ ≤ ∑ i ∈ range (p.log H), (2 * m / p ^ i + 1) := sum_le_sum fun i _ ↦ h_count i
    _ ≤ 4 * m + p.log H := by simpa [sum_add_distrib] using h_geom

/-- Let `p` be prime, `n ≤ p m` and `|c| + n ≤ H`. The sum of `v_p(k) + d` over the integers `k`
within `n` of `0` or of `c` is at most `8 m + 2 ⌊log_p H⌋ + (4 n + 2) d`. -/
lemma sum_twoWindows_le {n p d : ℕ} {c : ℤ} (hp : p.Prime) (m H : ℕ) (hn : n ≤ p * m)
    (hH : |c| + n ≤ H) :
    ∑ k ∈ twoWindows n c, (padicValInt p k + d) ≤ 8 * m + 2 * p.log H + (4 * n + 2) * d := by
  have h_zero : ∑ k ∈ Icc (-n : ℤ) n, padicValInt p k ≤ 4 * m + p.log H := by
    simpa using sum_padicValInt_Icc_le (c := 0) hp hn (by grw [← hH, abs_zero, ← abs_nonneg c])
  have h_val : ∑ k ∈ twoWindows n c, padicValInt p k ≤ 8 * m + 2 * p.log H := by
    grw [le_of_add_le_left sum_union_inter.le, h_zero, sum_padicValInt_Icc_le hp hn hH]
    omega
  have h_card : #(twoWindows n c) ≤ 4 * n + 2 := by
    grw [card_union_le, card_Icc, card_Icc]
    omega
  grw [sum_add_distrib, sum_const, smul_eq_mul, h_val, h_card]

end New.Lift

end Windows

/-!
## Points of a side and safe-move criteria for pairings

A side `S` (`New.Lift.KummerChart.PairingSide`) is a lattice `Y` with crystalline cocycles indexed
by a lattice `C`. These cocycles define the extension `S.extensionLattice` of the trivial lattice
`S.trivialLattice` by `S.kerLattice` (that is, `Y`). All of these are taken over `W(C^♭)` and cut
into letters `i`.

`L.withOrders i o` holds the elements at the letter `i` with orders at least `o a u` (`a` stands for
the prime `φ ^ a E`, `u` is a jump), `i.stepBack a` is the letter `a` steps before `i`, `k.zTauUnit`
is `z τ`, and `k.galMonoid` is the group `Γ'` of the chart.

The invariant forms `L.forms` are the `Ainf`-linear maps `μ` from `W(C^♭) ⊗ L` to `BdR` that are
`Γ'`-equivariant on `1 ⊗ L`. Such a form has type `u` at a letter if it sends the part of `1 ⊗ L` at
that letter into `hodgeFil (-u)`, where `hodgeFil n` is `tⁿ B_dR⁺`.
-/

namespace New.Lift.KummerChart

open Period Submodule FrobGroup Module Finset JumpLattice Pairing Equiv Fintype LinearMap Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O : k.Coeffs}

/-- The lattice datum O(1), on which Γ acts through the cyclotomic character, with jump set {−1}
at every letter and at every embedding of O in ℂ_p (`embJumps`). The field `inClass` says that it is
crystalline over the group Γ' of the chart with jumps in these sets. -/
abbrev tateLattice (O : Coeffs) : JumpLattice O where
  Carrier := O
  ρ := actionRep O O χ
  jumpSet _ := {-1}
  embJumps := _
  inClass := InClass.of_cyclotomic_pow 1 (by simp)
  embJumps_subset := by simp

/-- A gap in the jumps is a gap in the pole orders. Let `L` be a lattice with a Galois action and
with a finite set `L.jumpSet i` of integers, its jumps, at each letter `i` of the chart `k`. Let `x`
in `W(C^♭) ⊗ L` have a pole of order at most `t` at `E`. Let `x` be fixed by `Γ'` modulo the vectors
without pole, which have orders `raisedOrdersAtZero 0`. If `0 ≤ h₀` and no jump at `i` lies in
`[-t, -h₀)`, then the pole of `x` has order at most `h₀`. -/
lemma JumpLattice.mem_withOrders_raisedOrdersAtZero_of_gap {L : k.JumpLattice O}
    {i : k.Letter} {x : L.Ambient} {t h₀ : ℤ} (h₀_nonneg : 0 ≤ h₀)
    (h_gap : ∀ u ∈ L.jumpSet i, -t ≤ u → -h₀ ≤ u)
      (hx : x ∈ L.withOrders i (raisedOrdersAtZero (-t)))
    (h_deep : x ∈ invariantsMod (L.withOrders i (raisedOrdersAtZero 0))) :
    x ∈ L.withOrders i (raisedOrdersAtZero (-h₀)) := by
  -- At `E` a line of jump `u < -t` has the positive order `-t - u`, which improves to `-u`; a line
  -- of jump `u ≥ -h₀` has the order `min (-u) 0`. Away from `E` all orders are `-u`.
  refine mem_withOrders_of_le (mem_withOrders_improvedOrders hx h_deep) fun a u hu ↦ ?_
  have h_out : a = 0 → u < -t ∨ -h₀ ≤ u := by
    rintro rfl
    exact (lt_or_ge u (-t)).imp_right (h_gap u hu)
  simp only [improvedOrders, raisedOrdersAtZero]
  omega

namespace PairingSide

section Definitions

lemma stepBack_zero (i : k.Letter) : i.stepBack 0 = i := rfl

/-! ### The extension, its kernel, and deep elements -/

/-- The inclusion of `Y` into the extension of `C` by `Y`, as an equivariant map of lattice data. -/
abbrev inclKer (S : PairingSide O) : S.Hom S.extensionLattice :=
  ⟨LinearMap.inl O.O S.Carrier S.paramLattice.Carrier, by aesop (add simp extensionRep)⟩

/-- The `ℤ_[p]`-linear map from the localized Kisin module `kisinLoc` of the extension of `C` by `Y`
to `W(C^♭) ⊗ C` induced by the projection onto `C`. -/
abbrev localizedProjTrivial (S : PairingSide O) :
    S.extensionLattice.kisinLoc →ₗ[ℤ_[p]] S.trivialLattice.Ambient :=
  S.projTrivial.wittMap.restrictScalars ℤ_[p] ∘ₗ S.extensionLattice.kisinLoc.subtype.restrictScalars
    ℤ_[p]

/-- The points of `S.extensionLattice.kisinLoc` that lie over a constant at the letter `i` (the
projection `S.constantAt i c` of some `1 ⊗ c` to `i`) and are deep for `o`, that is, fixed by
`k.galMonoid` modulo the vectors with orders `o`. For a point `x` at the letter `i` this means that
for each jump `u` at `i.stepBack a` and each form `μ` of type `u` there, the value
`valueAt a μ x = μ (φ^{-a} x)` lies in the fixed field of `Γ'` modulo
`hodgeFil (o a u) = t ^ (o a u) B_dR⁺` (`JumpLattice.mem_invariantsMod_withOrders_iff`). -/
def deepElements (S : PairingSide O) (i : k.Letter) (o : ℕ → ℤ → ℤ) :
    Submodule ℤ_[p] S.extensionLattice.kisinLoc :=
  (S.constantAt i).range.comap S.localizedProjTrivial ⊓
    (invariantsMod (S.extensionLattice.withOrders i o)).comap
      (S.extensionLattice.kisinLoc.subtype.restrictScalars ℤ_[p])

/-- The vectors of the extension that lie over `0` and have orders `o` at the letter `i`. -/
def kerWithOrders (S : PairingSide O) (i : k.Letter) (o : ℕ → ℤ → ℤ) :
    Submodule Ainf S.extensionLattice.Ambient :=
  S.extensionLattice.withOrders i o ⊓ (S.projTrivial.wittMap.restrictScalars Ainf).ker

/-! ### Operators of a cost, pairings of sides, and points -/

/-- The additive map `A` is an operator of cost `e`: for every letter `i`, all orders `o` and
every point `x` that lies over the projection of some `1 ⊗ c` to `i` and is deep for `o`, the
difference `A x - p ^ e • x` lies over `0` and has orders `o` at `i`. Here `locKisinPart Q` is the
set of the elements of `kisinLoc` that lie in `Q`. -/
def IsOperatorOfCost (S : PairingSide O) (e : ℕ)
    (A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc) : Prop :=
  ∀ ⦃i : k.Letter⦄ ⦃o : ℕ → ℤ → ℤ⦄ ⦃x : S.extensionLattice.kisinLoc⦄, x ∈ S.deepElements i o →
    A x - p ^ e • x ∈ locKisinPart (S.kerWithOrders i o)

/-- A pairing between the lattices of the sides S and S'. -/
abbrev SidePairing (S S' : PairingSide O) : Type := Pairing S.toGalLattice S'.toGalLattice

/-- The points of `S.extensionLattice.kisinLoc` over `p ^ e` times the constant of `c` at the letter
`i` (the projection `S.constantAt i c` of `1 ⊗ c` to `i`) that have orders `o` and are deep for
`o'`: for each jump `u` at `i.stepBack a` and each form `μ` of type `u` there, the value
`valueAt a μ x = μ (φ^{-a} x)` lies in the fixed field of `Γ'` modulo
`hodgeFil (o' a u) = t ^ (o' a u) B_dR⁺` (`JumpLattice.mem_invariantsMod_withOrders_iff`). -/
def pointsOver (S : PairingSide O) (c : S.paramLattice) (i : k.Letter) (e : ℕ)
    (o o' : ℕ → ℤ → ℤ) : Set S.extensionLattice.Ambient :=
  {x ∈ S.extensionLattice.kisinLoc | S.projTrivial.wittMap x = p ^ e • S.constantAt i c ∧
    x ∈ S.extensionLattice.withOrders i o ∧ x ∈ invariantsMod (S.extensionLattice.withOrders i o')}

/-- The depth that the walk asks of a standard point: on the lines of jump `u` it is `-u`, raised by
`t` at the level `0` and by `η` at the levels below `l`. -/
def standardDepth (t η l a : ℕ) (u : ℤ) : ℤ :=
  -u + (if a = 0 then (t : ℤ) else 0) + if a < l then (η : ℤ) else 0

/-- The depth that a point at rest needs at a plain cut: `standardDepth t η l`, and `h₀` more at the
level `l`. -/
def plainDepth (t η l h₀ a : ℕ) (u : ℤ) : ℤ :=
  standardDepth t η l a u + if a = l then (h₀ : ℤ) else 0

/-- The orders of a stop. In the walk one side moves first, to a point called the stop, and rests
there while the other side moves. The orders of a stop are at least those of the pullback by
`φ ^ l`, and at least `-u` lowered by `η` at the levels below `l`. -/
def stopOrders (η l a : ℕ) (u : ℤ) : ℤ :=
  max (stdOrders l a u) (-u - if a < l then (η : ℤ) else 0)

/-- The least sum of the orders of a move and the depth of the point at rest that the rule for `l`
allows, on lines whose jumps add up to `s`: it is `1` at the levels below `l`, `t - s` at the level
`l` and `-s` above. -/
def ruleBound (l t a : ℕ) (s : ℤ) : ℤ := if a < l then 1 else (if a = l then (t : ℤ) else 0) - s

/-- The standard points over `p ^ e c` at the letter `i`: their orders are `-u`, lowered by `η`
at the level `0`, and their depth is `standardDepth t η l`. -/
def standardPoints (S : PairingSide O) (c : S.paramLattice) (i : k.Letter) (e t η l : ℕ) :
    Set S.extensionLattice.Ambient :=
  S.pointsOver c i e (raisedOrdersAtZero (-η)) (standardDepth t η l)

/-- The points over `p ^ e c` at the letter `i` with the orders of a stop (the depth asked for is
the same). -/
def stopPoints (S : PairingSide O) (c : S.paramLattice) (i : k.Letter) (e η l : ℕ) :
    Set S.extensionLattice.Ambient :=
  S.pointsOver c i e (stopOrders η l) (stopOrders η l)

/-- The vector `x` lies at the letter `i`, over `p ^ e` times the constant of `c` at `i`. -/
structure LiesOver (S : PairingSide O) (c : S.paramLattice) (i : k.Letter) (e : ℕ)
    (x : S.extensionLattice.Ambient) : Prop where
  /-- The vector lies in the part at the letter `i`. -/
  mem_letterPart : x ∈ S.extensionLattice.letterPart i
  /-- Its image in the trivial lattice is `p ^ e` times the constant of `c` at `i`. -/
  projTrivial_eq : S.projTrivial.wittMap x = p ^ e • S.constantAt i c

end Definitions

variable {S S' : PairingSide O} {c : S.paramLattice} {i : k.Letter}

section Points

variable {c' : S'.paramLattice} {l κ s e e' : ℕ} {o o' o₁ o₂ o₃ : ℕ → ℤ → ℤ}
  {x w : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient} {P : S.SidePairing S'}

/-- Over `W(C^♭)`, the inclusion of `Y` into the extension is a section of the first projection
`S.wittFst`, and its image lies over `0`. -/
@[simp]
lemma wittFst_inclKer : ∀ y : S.Ambient,
    S.wittFst (S.inclKer.wittMap y) = y ∧ S.projTrivial.wittMap (S.inclKer.wittMap y) = 0 :=
  diagTensor_induction (by simp)

/-- The pairing `P`, read on the first components of vectors of the two extensions, is balanced for
the multiplication by the root of unity `ζ` of `O`. -/
lemma wittPairing_wittFst_mulZeta (x : S.extensionLattice.Ambient)
    (y : S'.extensionLattice.Ambient) :
    P.wittPairing (S.wittFst (S.extensionLattice.mulZeta.wittMap x)) (S'.wittFst y) =
      P.wittPairing (S.wittFst x) (S'.wittFst (S'.extensionLattice.mulZeta.wittMap y)) := by
  revert x y
  exact diagTensor_induction fun _ _ ↦ diagTensor_induction (by simp [mulZeta, modPairing])

/-- The Teichmüller lifts `k.letterTeich` of two distinct letters differ by a unit of the ring `k.S`
of the chart. -/
lemma isUnit_letterTeich_sub {i j : k.Letter} (h_ne : j ≠ i) :
    IsUnit (k.letterTeich j - k.letterTeich i) := by
  change IsUnit (algebraMap (WittFq k.f) k.S (WittVector.teichmuller p j.val) -
    algebraMap (WittFq k.f) k.S (WittVector.teichmuller p i.val))
  rw [← map_sub]
  exact (isUnit_teichmuller_sub (Units.ext.mt h_ne)).map _

/-- Vectors of the two extensions that lie at distinct letters are orthogonal under `P`. -/
lemma wittPairing_wittFst_eq_zero_of_ne {i j : k.Letter} (h_ne : j ≠ i)
    {x : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient}
    (hx : x ∈ S.extensionLattice.letterPart j) (hy : y ∈ S'.extensionLattice.letterPart i) :
      P.wittPairing (S.wittFst x) (S'.wittFst y) = 0 := by
  -- `ζ` acts at a letter by its Teichmüller lift, and the lifts of `j` and `i` differ by a unit.
  have h_eq : k.letterTeich j • P.wittPairing (S.wittFst x) (S'.wittFst y) =
      k.letterTeich i • P.wittPairing (S.wittFst x) (S'.wittFst y) := by
    simpa [mem_letterPart_iff_mulZeta.1 hx, mem_letterPart_iff_mulZeta.1 hy] using
      wittPairing_wittFst_mulZeta (P := P) x y
  rw [← (isUnit_letterTeich_sub h_ne).smul_eq_zero, sub_smul, h_eq, sub_self]

/-- Let `P` be a pairing modulo `p ^ m` of two sides `S`, `S'` of the chart `k`, with lattices `Y`,
`Y'`, and let `κ` be a natural number. For each letter `i` let `u i`, `v i` be vectors in the parts
at `i` (`letterPart i`) of `W(C^♭)` tensored with the two extension lattices `Y × C`, `Y' × C'`. If
each pair `u i`, `v i` is safe for `P` and `κ`, that is, `p ^ κ` times the pairing of their
components in `Y` and `Y'` lies in the image of the ideal `W(𝔪^♭)` of Witt vectors over the maximal
ideal, then the pair of their sums over all letters is safe. -/
lemma isSafe_sum {u : k.Letter → S.extensionLattice.Ambient}
    {v : k.Letter → S'.extensionLattice.Ambient}
    (h_letter : ∀ i : k.Letter, u i ∈ S.extensionLattice.letterPart i ∧ v i ∈
      S'.extensionLattice.letterPart i)
    (h_safe : ∀ i : k.Letter, P.IsSafe κ (u i) (v i)) :
    P.IsSafe κ (∑ i : k.Letter, u i) (∑ i : k.Letter, v i) := by
  obtain ⟨hu, hv⟩ := forall_and.1 h_letter
  -- the terms at distinct letters vanish
  have h_sum : P.wittPairing (S.wittFst (∑ i, u i)) (S'.wittFst (∑ i, v i)) =
      ∑ i, P.wittPairing (S.wittFst (u i)) (S'.wittFst (v i)) := by
    simp only [map_sum, LinearMap.sum_apply]
    exact sum_congr _ _ fun i ↦
      sum_eq_single i fun j h_ne ↦ wittPairing_wittFst_eq_zero_of_ne h_ne (hu j) (hv i)
  rw [IsSafe, h_sum, smul_sum]
  exact sum_mem fun i _ ↦ h_safe i

/-- Let `S` be a side of the chart `k`: a lattice `Y` (`S.Carrier`) and a lattice `C`
(`S.paramLattice`) that indexes crystalline cocycles `S.cocycleMap c` with values in `Y`. Let `μ` be
an invariant form on `Y`: an `Ainf`-linear map from `W(C^♭) ⊗ Y` to `BdR` that is equivariant on
`1 ⊗ Y` for the subgroup `k.subgroup` of the chart. If its values on `1 ⊗ Y` lie in the
`BdRPlus`-submodule `W`, then `μ` sends the cocycle of `c`, restricted to `k.subgroup`, to the
coboundary `g b - b` of an element `b` of `W`. -/
lemma exists_mem_form_cocycle_eq_coboundary (W : Submodule BdRPlus BdR) {μ : S.Functional}
    (hμ : μ ∈ S.forms) (hW : ∀ t : S.Carrier, μ (DiagTensor.mk 1 t) ∈ W) (c : S.paramLattice) :
    ∃ b ∈ W, ∀ g : k.subgroup,
      μ (DiagTensor.mk 1 ((S.cocycleMap c).val g)) = toGp (g : Γ.G) • b - b := by
  -- Extend `μ` to an equivariant `Bmax`-linear form `Λ`. The cocycle is the coboundary of a period
  -- `v`, and `Λ v` is congruent modulo `W` to a constant `a`. Take `Λ v - a`.
  let Λ : TensorProduct ℤ_[p] Bmax S.Carrier →ₗ[Bmax] BdR :=
    (μ.restrictScalars ℤ_[p] ∘ₗ DiagTensor.mk 1).liftBaseChange Bmax
  have Λ_equiv (g : k.subgroup) (y : TensorProduct ℤ_[p] Bmax S.Carrier) :
      Λ (tensorAction Bmax (toGp (g : Γ.G)) (S.ρ g) y) = toGp (g : Γ.G) • Λ y := by
    induction y with
    | tmul b t => simp [Λ, tensorAction, hμ t, smul_def']
    | add y y' hy hy' => simp only [map_add, smul_add, hy, hy']
  obtain ⟨v, hv⟩ : ∃ v : TensorProduct ℤ_[p] Bmax S.Carrier, ∀ g : Γ.G,
      1 ⊗ₜ (S.cocycleMap c).val g = tensorAction Bmax (toGp g) (S.ρ g) v - v :=
    (S.cocycleMap c).property
  have Λ_cob (g : k.subgroup) :
      μ (DiagTensor.mk 1 ((S.cocycleMap c).val g)) = toGp (g : Γ.G) • Λ v - Λ v := by
    simp [← Λ_equiv, ← map_sub, ← hv, Λ]
  have Λ_mem (g : k.subgroup) : toGp (g : Γ.G) • Λ v - Λ v ∈ W := by
    simpa only [← Λ_cob] using hW _
  obtain ⟨a, ha⟩ : ∃ a : localFieldOf k.subgroup, Λ v - Algebra.cast a ∈ W :=
    BdR.exists_sub_mem_of_smul_sub_mem k.subgroup W Λ_mem
  refine ⟨Λ v - Algebra.cast a, ha, fun g ↦ ?_⟩
  have a_fixed : toGp (g : Γ.G) • (Algebra.cast a : BdR) = Algebra.cast a :=
    (BdR.smul_algebraMap_padicAlgCl _ _).trans (congrArg _ (mem_localFieldOf.1 a.2 g))
  rw [Λ_cob, smul_sub, a_fixed, sub_sub_sub_cancel_right]

/-- Let `S` be a side of the chart `k`, with lattice `Y` and with cocycles `S.cocycleMap c` indexed
by the lattice `C = S.paramLattice`, and let `μ : W(C^♭) ⊗ Y → BdR` be an invariant form with values
in `W` on `1 ⊗ Y`. Then there is a linear map `f` from `C` to `W` such that `μ` sends the cocycle of
`c`, restricted to `k.subgroup`, to the coboundary `g ↦ g (f c) - f c`. -/
lemma exists_linearMap_form_cocycle_eq_coboundary (W : Submodule BdRPlus BdR) {μ : S.Functional}
    (hμ : μ ∈ S.forms) (hW : ∀ t : S.Carrier, μ (DiagTensor.mk 1 t) ∈ W) :
    ∃ f : S.paramLattice →ₗ[ℤ_[p]] BdR, (∀ c : S.paramLattice, f c ∈ W) ∧
      ∀ (c : S.paramLattice) (g : k.subgroup),
        μ (DiagTensor.mk 1 ((S.cocycleMap c).val g)) = toGp (g : Γ.G) • f c - f c := by
  choose b b_mem b_cob using exists_mem_form_cocycle_eq_coboundary W hμ hW
  let e : Basis (Fin (finrank ℤ_[p] S.paramLattice)) ℤ_[p] S.paramLattice :=
    finBasis ℤ_[p] S.paramLattice
  let f : S.paramLattice →ₗ[ℤ_[p]] BdR := e.constr ℕ fun j ↦ b (e j)
  -- both conditions hold on the basis `e` and are kept by linear combinations
  refine ⟨f, forall_and.1 fun c ↦ ?_⟩
  induction e.mem_span c using span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp [f, b_mem, b_cob]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, add_mem, add_sub_add_comm]
  | smul r x _ hx => simp [hx, smul_of_tower_mem, smul_sub, smul_comm (toGp _) r]

/-- Let `S` be a side of the chart: lattices `Y` and `C` with crystalline cocycles of `Y` indexed by
`C`, which define the extension `S.extensionLattice` of `C` by `Y`, with underlying module `Y × C`.
Let `μ` be an invariant form on `Y` whose values on `1 ⊗ Y` lie in `W`. Then some invariant form `ν`
on the extension restricts to `μ` along the inclusion `S.inclKer` of `Y` and has values in `W` on
`ainfLattice`, the `Ainf`-span of `1 ⊗ (Y × C)`. -/
lemma exists_extend_form (W : Submodule BdRPlus BdR) {μ : S.Functional} (hμ : μ ∈ S.forms)
    (hW : ∀ t : S.Carrier, μ (DiagTensor.mk 1 t) ∈ W) :
    ∃ ν ∈ S.extensionLattice.forms,
      S.extensionLattice.ainfLattice ≤ (W.restrictScalars Ainf).comap ν ∧ ν ∘ₗ S.inclKer.wittMap =
        μ := by
  -- Take `μ` on the first factor, and on the second a map `f` whose coboundary cancels the cocycle.
  obtain ⟨f, f_mem, f_cob⟩ := exists_linearMap_form_cocycle_eq_coboundary W hμ hW
  obtain ⟨μ', hμ'⟩ : ∃ μ' : S.trivialLattice.Functional, ∀ c : S.paramLattice,
    μ' (DiagTensor.mk 1 c) = f c :=
    S.trivialLattice.exists_functional_extend f
  let ν : S.extensionLattice.Functional := μ ∘ₗ ↑S.wittFst + μ' ∘ₗ S.projTrivial.wittMap
  have ν_apply (t : S.Carrier) (c : S.paramLattice) :
      ν (DiagTensor.mk 1 (t, c)) = μ (DiagTensor.mk 1 t) + f c := by simp [ν, hμ']
  refine ⟨ν, fun (t, c) g ↦ ?_, span_le.2 ?_, ext fun y ↦ by simp [ν]⟩
  · -- invariance: the cocycle term of the action cancels the coboundary of `f c`
    have h_act : S.extensionLattice.ρ g (t, c) = (S.ρ g t + (S.cocycleMap c).1 g, c) := rfl
    rw [h_act, ν_apply, ν_apply, map_add, map_add, hμ t g, f_cob, smul_add, add_assoc,
      sub_add_cancel]
  · rintro _ ⟨⟨t, c⟩, rfl⟩
    simpa [ν, hμ'] using add_mem (hW t) (f_mem c)

/-- Let `x` lie over a constant at the letter `i` and be deep for `o`. An operator of cost `e` sends
`x` into every submodule `M` that holds `x` and the points over `0` with orders `o`. -/
lemma IsOperatorOfCost.apply_mem_of_kerWithOrders_le
    {A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc}
    {M : Submodule ℤ_[p] S.extensionLattice.kisinLoc} {x : S.extensionLattice.kisinLoc}
    (hA : S.IsOperatorOfCost e A) (h_ker_le : locKisinPart (S.kerWithOrders i o) ≤ M)
    (hx_mem : x ∈ M) (hx_deep : x ∈ S.deepElements i o) : A x ∈ M := by
  exact (sub_mem_iff_left M (nsmul_mem hx_mem (p ^ e))).1 (h_ker_le (hA hx_deep))

/-- The points of the localized Kisin module of the extension that lie over `0` and have orders
`o` at the letter `i` are deep for `o` at `i`. -/
lemma locKisinPart_kerWithOrders_le_deepElements :
    locKisinPart (S.kerWithOrders i o) ≤ S.deepElements i o :=
  fun _ ⟨h_exp, h_over_zero⟩ ↦ ⟨ker_le_comap _ h_over_zero, smul_sub_mem_withOrders h_exp⟩

/-- An operator `A` of cost `e` keeps every depth: if `x` lies over a constant at the letter `i` and
is deep for `o`, then the same holds for `A x`. -/
lemma IsOperatorOfCost.mem_deepElements
    {A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc}
    {x : S.extensionLattice.kisinLoc} (hA : S.IsOperatorOfCost e A)
    (hx_deep : x ∈ S.deepElements i o) :
    A x ∈ S.deepElements i o :=
  hA.apply_mem_of_kerWithOrders_le locKisinPart_kerWithOrders_le_deepElements hx_deep hx_deep

/-- Costs add under composition: if `B` has cost `e'` and `A` has cost `e`, then `B ∘ A` has cost
`e' + e`. -/
lemma IsOperatorOfCost.comp {A B : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc}
    (hB : S.IsOperatorOfCost e' B) (hA : S.IsOperatorOfCost e A) :
      S.IsOperatorOfCost (e' + e) (B.comp A) := by
  intro i o x hx_deep
  have h_split : B.comp A x - p ^ (e' + e) • x =
      (B (A x) - p ^ e' • A x) + p ^ e' • (A x - p ^ e • x) := by
    simp [smul_sub, pow_add, mul_smul]
  rw [h_split]
  exact add_mem (hB (hA.mem_deepElements hx_deep)) (nsmul_mem (hA hx_deep) (p ^ e'))

/-! ### Strictness of the inclusion, and points of one side -/

/-- Let `S.inclKer` be the inclusion of the lattice `Y` of the side `S` into its extension by `C`,
and `S.inclKer.wittMap` that inclusion tensored with `W(C^♭)`. If the image of `y` under
`S.inclKer.wittMap` lies in `kisinLocAinf` of the extension, then `y` lies in `kisinLocAinf` of `Y`.
For a lattice `L`, this is the set of the vectors that some product of the elements `φ ^ a E` (`E`
the Eisenstein polynomial of the chart, `φ` the Frobenius) multiplies into `kisinAinf`. That module
consists of the `x` in `Ainf[1/τ] ⊗ L`, where `τ = [ε^{1/p}] - 1`, with `μ (φ ^ n x)` in `B_dR⁺` for
all `n ≥ 1` and all invariant forms `μ : W(C^♭) ⊗ L → BdR`. -/
lemma mem_kisinLocAinf_of_inclKer {y : S.Ambient}
    (hy : S.inclKer.wittMap y ∈ S.extensionLattice.kisinLocAinf) : y ∈ S.kisinLocAinf := by
  -- The condition on lattices passes to `y` by projecting to the first factor, the condition on
  -- invariant forms because such forms extend.
  obtain ⟨r, hr, ⟨t, ht, h_lattice⟩, h_values⟩ :
      ∃ r ∈ Submonoid.closure (Set.range fun a : ℕ ↦ (k.frobE a).1),
        (∃ t ∈ Submonoid.powers tau, t • r • S.inclKer.wittMap y ∈ S.extensionLattice.ainfLattice) ∧
        ∀ n : ℕ, ∀ ν ∈ S.extensionLattice.forms,
          ν (φ ^ (n + 1) • r • S.inclKer.wittMap y) ∈ hodgeFil 0 := hy
  refine ⟨r, hr, ⟨t, ht, ?_⟩, fun n μ hμ ↦ ?_⟩
  · simpa using wittMap_mem_ainfLattice (LinearMap.fst O S.Carrier S.paramLattice.Carrier) h_lattice
  · obtain ⟨ν, hν, -, rfl⟩ := exists_extend_form ⊤ hμ (by simp)
    simpa using h_values n ν hν

/-- A vector `y` of `S` whose image in the extension lies at the letter `i` lies at `i`. -/
lemma mem_letterPart_of_inclKer {y : S.Ambient}
    (hy : S.inclKer.wittMap y ∈ S.extensionLattice.letterPart i) : y ∈ S.letterPart i := by
  rw [mem_letterPart_iff_letterProj] at hy ⊢
  rw [← (wittFst_inclKer (S.letterProj i y)).1, Hom.wittMap_letterProj, hy, (wittFst_inclKer y).1]

/-- Let `S.inclKer` be the inclusion of the lattice `Y` of the side `S` into its extension by `C`.
If the image of a vector `y` of `W(C^♭) ⊗ Y` has orders `o` at the letter `i`, then so has `y`. Here
orders `o : ℕ → ℤ → ℤ` at `i` mean: `y` is in the part at `i` of `kisinLocAinf` and, for each
integer `u` among the jumps at the letter `i.stepBack a`, `a` steps before `i`, each invariant form
`μ` of type `u` there has `μ (φ^{-a} y)` in `t ^ (o a u) B_dR⁺`. -/
lemma mem_withOrders_of_inclKer {y : S.Ambient}
    (hy : S.inclKer.wittMap y ∈ S.extensionLattice.withOrders i o) : y ∈ S.withOrders i o := by
  obtain ⟨⟨h_span, h_letter⟩, h_exp⟩ := hy
  have y_letter : y ∈ S.letterPart i := mem_letterPart_of_inclKer h_letter
  refine ⟨⟨mem_kisinLocAinf_of_inclKer h_span, y_letter⟩, fun a u hu μ ⟨μ_form, μ_pole⟩ ↦ ?_⟩
  -- extend the letter part of `μ` to a form `ν`, keeping the order of its pole
  obtain ⟨ν, ν_form, ν_pole, ν_res⟩ : ∃ ν ∈ S.extensionLattice.forms,
      S.extensionLattice.ainfLattice ≤ ((hodgeFil (-u)).restrictScalars Ainf).comap ν ∧
      ν ∘ₗ S.inclKer.wittMap.restrictScalars Ainf =
        μ ∘ₗ (S.letterProj (i.stepBack a)).restrictScalars Ainf :=
    exists_extend_form _ (comp_letterProj_mem_forms μ_form) μ_pole
  have ν_type : ν ∈ S.extensionLattice.formsOfType (i.stepBack a) u :=
    ⟨ν_form, fun t ↦ ν_pole (letterProj_mk_mem_ainfLattice t)⟩
  -- `φ ^ (-a) • y` lies at the letter `i.stepBack a`, where `ν` restricts to `μ`
  have h_value : valueAt a ν (S.inclKer.wittMap y) = valueAt a μ y := by
    rw [← valueAt_comp_wittMap, ν_res]
    simp [JumpLattice.valueAt, mem_letterPart_iff_letterProj.1, ← phi_pow_smul_mem_letterPart_iff,
      y_letter, -Equiv.Perm.coe_inv]
  rw [← h_value]
  exact h_exp a u hu ν ν_type

/-- Let `y` be a vector of `W(C^♭) ⊗ Y`, for the lattice `Y` of the side `S`. If the image of `y` in
the extension of `C` by `Y` lies in `kisinLoc` of the extension, then `y` lies in `kisinLoc` of `Y`.
Here `kisinLoc` is the Kisin module with all `φ^a E` inverted: it consists of the vectors that some
product of the elements `φ^a E` multiplies into the Kisin module `kisinModule`. -/
lemma mem_kisinLoc_of_inclKer {y : S.Ambient}
    (hy : S.inclKer.wittMap y ∈ S.extensionLattice.kisinLoc) : y ∈ S.kisinLoc := by
  -- The retraction fixes `S.inclKer.wittMap y` and commutes with the inclusion, so it fixes `y`.
  let y' : S.kisinLocAinf := ⟨y, mem_kisinLocAinf_of_inclKer hy.1⟩
  have h_fixed : S.inclKer.wittMap (coordRetract y') = S.inclKer.wittMap y := by
    rw [S.inclKer.wittMap_coordRetract y' ⟨_, hy.1⟩ rfl, coordRetract_of_mem_kisinLoc hy]
  have y_fixed : (coordRetract y' : S.kisinLoc) = y := by simpa using congrArg S.wittFst h_fixed
  rw [← y_fixed]
  exact SetLike.coe_mem _

/-- Strictness: a vector `w` of the extension that lies over `0` and has orders `o` at the letter
`i` is the image of a vector `y` of `S` with orders `o` at `i`, and `y` lies in the localized
Kisin module `kisinLoc` if `w` does. -/
lemma exists_inclKer_eq_of_kerWithOrders (hw : w ∈ S.kerWithOrders i o) :
    ∃ y ∈ S.withOrders i o,
      S.inclKer.wittMap y = w ∧ (w ∈ S.extensionLattice.kisinLoc → y ∈ S.kisinLoc) := by
  obtain ⟨w_exp, w_over_zero⟩ := hw
  obtain ⟨y, rfl⟩ : w ∈ S.inclKer.wittMap.range :=
    (lTensor_exact _ .inl_snd snd_surjective _).1 w_over_zero
  exact ⟨y, mem_withOrders_of_inclKer w_exp, rfl, mem_kisinLoc_of_inclKer⟩

/-- Let `S` be a side of the chart, with lattices `Y` and `C = S.paramLattice`. Suppose that
`p ^ κ * E ^ s`, with `E` the Eisenstein polynomial of the chart, kills the cokernel at the letter
`i` (`KillsCokernel`): it multiplies the part at `i` of `A_inf ⊗ C` into the image of the vectors of
the extension with the standard orders `stdOrders 0`. Then, for `c` in `C`, `S.pointsOver` is
nonempty: some point of the extension lies over `p ^ κ • c` at `i`. Its orders and its depth are
both `raisedOrdersAtZero (-s)`. -/
lemma pointsOver_nonempty_of_killsCokernel (h_kill : S.KillsCokernel i κ s) (c : S.paramLattice) :
    (S.pointsOver c i κ (raisedOrdersAtZero (-s)) (raisedOrdersAtZero (-s))).Nonempty := by
  -- lift `p ^ κ * k.E ^ s` times the constant, then divide by `k.E ^ s`
  obtain ⟨t, lift⟩ := exists_lift_of_mem_liftIdeal h_kill
  obtain ⟨x, ⟨x_mem, x_exp⟩, pr_x⟩ := lift (S.constantAt i c) (constantAt_mem_stdOrdersPart c)
  have h_le (a : ℕ) (u : ℤ) :
      raisedOrdersAtZero (-s) a u ≤ stdOrders 0 a u + if 0 = a then (-s : ℤ) else 0 := by
    cases a <;> simp [raisedOrdersAtZero, stdOrders, sub_eq_neg_add]
  have exp : k.frobEUnit 0 ^ (-s : ℤ) • x ∈ S.extensionLattice.withOrders i
    (raisedOrdersAtZero (-s)) :=
    frobEUnit_zpow_smul_mem_withOrders 0 (-s) x_exp fun a u _ ↦ h_le a u
  refine ⟨k.frobEUnit 0 ^ (-s : ℤ) • x, frobEUnit_zpow_smul_mem_kisinLoc_iff.2 x_mem, ?_, exp,
    smul_sub_mem_withOrders exp⟩
  suffices h : ((p : Ainf) ^ κ * (k.E : Ainf) ^ s) • S.constantAt i c =
      (k.E : Ainf) ^ s • p ^ κ • S.constantAt i c by
    simpa [pr_x, inv_smul_eq_iff, frobEUnit_pow_smul, val_frobE] using h
  module

/-- The operator `x ↦ pr (υ (g x - x) / δ)` on `S.extensionLattice.kisinLoc`, for `g` in
`k.galMonoid` (the group `Γ'` of the chart) and `υ` in `Ainf`. Here `δ = k.zTau` is `z τ`, the
product of the coordinate `z` of the chart and `τ = [ε^{1/p}] - 1`. The element `(g x - x) / δ` lies
in the `Ainf`-span `S.extensionLattice.kisinLocAinf` of `S.extensionLattice.kisinLoc`, and the
retraction `pr = coordRetract` maps that span back to `S.extensionLattice.kisinLoc`. -/
def depthOperator (S : PairingSide O) (g : k.galMonoid) (υ : Ainf) :
    S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc :=
  AddMonoidHom.mk'
    (fun x ↦ S.extensionLattice.coordRetract
      (υ • ⟨k.zTauUnit⁻¹ • (g • x.1 - x.1), zTauUnit_inv_smul_sub_mem_kisinLocAinf g x.2⟩))
    (by simp [← map_add, add_sub_add_comm])

lemma depthOperator_apply (g : k.galMonoid) (υ : Ainf) (x : S.extensionLattice.kisinLoc) :
    S.depthOperator g υ x = S.extensionLattice.coordRetract
      (υ • ⟨k.zTauUnit⁻¹ • (g • x.1 - x.1), zTauUnit_inv_smul_sub_mem_kisinLocAinf g x.2⟩) :=
  rfl

/-- An operator turns depth into orders: if `g • x - x` has orders `o` at the letter `i`, then so
does `S.depthOperator g υ x`, the retraction of `υ (g x - x) / (z τ)` to the Kisin module of the
extension. -/
lemma depthOperator_mem_withOrders (g : k.galMonoid) (υ : Ainf) {x : S.extensionLattice.kisinLoc}
    (hx_deep : g • x.1 - x.1 ∈ S.extensionLattice.withOrders i o) :
    (S.depthOperator g υ x).1 ∈ S.extensionLattice.withOrders i o := by
  have h_quot : k.zTauUnit⁻¹ • (g • x.1 - x.1) ∈ S.extensionLattice.withOrders i o :=
    zTauUnit_inv_smul_sub_mem_withOrders x.2 hx_deep
  exact coordRetract_mem_withOrders _ (smul_mem _ υ h_quot)

/-- The operator `S.depthOperator g υ`, the retraction of `x ↦ υ (g x - x) / (z τ)`, sends a point
over a constant at the letter `i` to a vector over `0`. -/
lemma projTrivial_depthOperator_eq_zero (g : k.galMonoid) (υ : Ainf)
    {x : S.extensionLattice.kisinLoc} (hx_over : S.projTrivial.wittMap x.1 = S.constantAt i c) :
    S.projTrivial.wittMap (S.depthOperator g υ x).1 = 0 := by
  -- `g` fixes the constant below `x`, and the projection commutes with the retraction
  have h_quot : S.projTrivial.wittMap (υ • k.zTauUnit⁻¹ • (g • x.1 - x.1)) = 0 := by
    simp [hx_over, constantAt, gal_smul_letterProj, k.galMonoid.smul_def]
  rw [depthOperator_apply, S.projTrivial.wittMap_coordRetract _ 0 h_quot]
  simp

/-- The operator `S.depthOperator g υ` sends an element of `S.deepElements i o` into
`S.kerWithOrders i o`, the vectors over `0` with orders `o` at `i`. -/
lemma depthOperator_mem_kerWithOrders (g : k.galMonoid) (υ : Ainf) {x : S.extensionLattice.kisinLoc}
    (hx : x ∈ S.deepElements i o) :
    S.depthOperator g υ x ∈ locKisinPart (S.kerWithOrders i o) := by
  obtain ⟨⟨c, hx_over⟩, hx_deep⟩ := hx
  exact ⟨depthOperator_mem_withOrders g υ (hx_deep g),
    projTrivial_depthOperator_eq_zero g υ hx_over.symm⟩

/-- One step of depth at the level `a` (the place `φ ^ a E`) for a side `S` of the chart `k`. Some
additive map `B` of cost `cost a n = v_p(n) + k.differentBound + 3 a` has the property below. Cost
`e'` means: if a point `x` lies over a constant at a letter `i` and is fixed by `Γ' = k.galMonoid`
modulo the vectors with orders `o` there, then `B x - p ^ e' • x` lies over `0` and has orders `o`
at `i`. The property: for every invariant form `μ` on the extension, if
`valueAt a μ (g • x - x) = μ (φ^{-a} (g • x - x))` lies in `hodgeFil n = tⁿ B_dR⁺` for all `g` in
`Γ'`, then the same expression for `B x` lies in `hodgeFil (n + 1)`. -/
lemma exists_isOperatorOfCost_mem_hodgeFil_succ (S : PairingSide O) (a : ℕ) (n : ℤ) :
    ∃ B : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc,
      S.IsOperatorOfCost (cost a n) B ∧
      ∀ x : S.extensionLattice.kisinLoc, ∀ μ ∈ S.extensionLattice.forms,
        (∀ g : k.galMonoid, valueAt a μ (g • x.val - x.val) ∈ hodgeFil n) →
        ∀ g : k.galMonoid, valueAt a μ (g • (B x).val - (B x).val) ∈ hodgeFil (n + 1) := by
  -- Take `p ^ cost a n + υ ∑ (γ l - 1) / zTau` from `exists_valueAt_sub_mem_hodgeFil_succ` and
  -- bring its second term back into `kisinLoc` by the retraction `coordRetract`.
  obtain ⟨m, γ, υ, step⟩ := S.extensionLattice.exists_valueAt_sub_mem_hodgeFil_succ a n
  let B : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc :=
    p ^ cost a n • .id _ + ∑ l : Fin m, S.depthOperator (γ l) υ
  refine ⟨B, fun i o x hx_deep ↦ ?_, fun x μ hμ h_inv g ↦ ?_⟩
  · have h_sum : B x - p ^ cost a n • x = ∑ l, S.depthOperator (γ l) υ x := by simp [B]
    rw [h_sum]
    exact sum_mem fun l _ ↦ depthOperator_mem_kerWithOrders (γ l) υ hx_deep
  -- the value of `x` is invariant modulo `hodgeFil n`, hence a constant modulo `hodgeFil n`; so
  -- `step` gives a constant modulo `hodgeFil (n + 1)`, and the retraction keeps it
  have x_mem : x.val ∈ S.extensionLattice.kisinLocAinf := x.property.1
  obtain ⟨const, h_const⟩ : ∃ const : localFieldOf k.subgroup,
      valueAt a μ (S.extensionLattice.depthStepOperator (cost a n) υ γ x.val) -
        Algebra.cast const ∈ hodgeFil (n + 1) :=
    step x.val x.property μ hμ (exists_valueAt_sub_mem_hodgeFil x_mem hμ h_inv)
  let y : S.extensionLattice.kisinLocAinf := p ^ cost a n • ⟨x.val, x_mem⟩ +
    ∑ l : Fin m, υ • ⟨_, zTauUnit_inv_smul_sub_mem_kisinLocAinf (γ l) x.property⟩
  have hy : valueAt a μ y.val - Algebra.cast const ∈ hodgeFil (n + 1) := by
    simpa [y, depthStepOperator_apply] using h_const
  have hB : (B x).val = (S.extensionLattice.coordRetract y).val := by
    simp [B, y, depthOperator_apply, coordRetract_of_mem_kisinLoc, nsmul_mem]
  have hB_const : valueAt a μ (B x).val - Algebra.cast const ∈ hodgeFil (n + 1) := by
    rw [hB]
    exact valueAt_coordRetract_sub_mem_hodgeFil hμ y ((valueField a).algebraMap_mem const) hy
  have Bx_mem : (B x).val ∈ S.extensionLattice.kisinLocAinf := (B x).property.1
  exact valueAt_smul_sub_mem_hodgeFil_of_sub_const_mem Bx_mem hμ hB_const g

/-- Let `S` be a side of the chart `k` and `I` a finite set of steps `(a, n)`, of cost
`cost a n = v_p(n) + k.differentBound + 3 a` each. Call `x` deep for orders `o` at the letter `i`
(`deepElements`) if it lies over a constant at `i` and is fixed by `Γ'` modulo the vectors with
orders `o`. There is an additive map `A` of cost `e = ∑ cost a n` over `I`. It sends `x` deep for
`o` to an element deep for `o'` whenever `I` contains every step `(a, n)` with `o a u ≤ n < o' a u`
for a jump `u` at `i.stepBack a`, the letter `a` steps before `i`. -/
lemma exists_isOperatorOfCost_and_mem_deepElements (I : Finset ((_ : ℕ) × ℤ)) :
    ∃ A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc,
      S.IsOperatorOfCost (∑ q ∈ I, cost q.1 q.2) A ∧
      ∀ ⦃i : k.Letter⦄ ⦃o : ℕ → ℤ → ℤ⦄ ⦃x : S.extensionLattice.kisinLoc⦄, x ∈ S.deepElements i o →
        ∀ o' : ℕ → ℤ → ℤ,
          (∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ n : ℤ, o a u ≤ n → n < o' a u → ⟨a, n⟩ ∈ I) →
          A x ∈ S.deepElements i o' := by
  -- Induction on `I`, removing a pair `(a, n)` with `n` largest: compose the operator for the
  -- rest with the operator `B` that clears the step `n` at level `a`.
  induction I using Finset.induction_on_max_value (fun q : Σ _ : ℕ, ℤ ↦ q.2) with
  | empty =>
    refine ⟨.id _, by simp [IsOperatorOfCost], fun i o x ⟨hx_const, hx_deep⟩ o' cover ↦
      ⟨hx_const, fun g ↦ mem_withOrders_of_le (hx_deep g) fun a u hu ↦ ?_⟩⟩
    by_contra! h_lt
    exact notMem_empty _ (cover a u hu (o a u) le_rfl h_lt)
  | insert q I q_new q_max ih =>
    obtain ⟨a, n⟩ := q
    obtain ⟨A, A_cost, A_deep⟩ := ih
    obtain ⟨B, B_cost, B_step⟩ := S.exists_isOperatorOfCost_mem_hodgeFil_succ a n
    refine ⟨B.comp A, by simpa [q_new] using B_cost.comp A_cost, fun i o x hx o' cover ↦ ?_⟩
    -- Lower `o' a u` from `n + 1` to `n`. Then `I` covers the rest.
    let low (b : ℕ) (u : ℤ) : ℤ := if b = a ∧ o' b u = n + 1 then n else o' b u
    have cover_low (b : ℕ) (u : ℤ) (hu : u ∈ S.jumpSet (i.stepBack b)) (m : ℤ) (h_le : o b u ≤ m)
        (h_lt : m < low b u) : (⟨b, m⟩ : Σ _ : ℕ, ℤ) ∈ I := by
      refine mem_of_mem_insert_of_ne (cover b u hu m h_le (by grind)) fun h_eq ↦ ?_
      obtain ⟨rfl, rfl⟩ : b = a ∧ m = n := by simpa using h_eq
      -- here `m + 1 < o' b u`, so the pair `(b, m + 1)` contradicts the choice of `m`
      have succ_mem : (⟨b, m + 1⟩ : Σ _ : ℕ, ℤ) ∈ I :=
        mem_of_mem_insert_of_ne (cover b u hu (m + 1) (by lia) (by grind)) (by simp)
      exact (lt_add_one m).not_ge (q_max _ succ_mem)
    have deep_low : A x ∈ S.deepElements i low := A_deep hx low cover_low
    -- `B` keeps the depth `low`; it remains to raise the lowered orders
    obtain ⟨B_const, B_deep⟩ : B (A x) ∈ S.deepElements i low := B_cost.mem_deepElements deep_low
    refine ⟨B_const, fun g ↦ mem_withOrders_of_mem_hodgeFil (B_deep g) fun b u hu h_lt μ hμ ↦ ?_⟩
    obtain ⟨rfl, eq_succ⟩ : b = a ∧ o' b u = n + 1 := by grind
    rw [eq_succ]
    refine B_step (A x) μ hμ.1 (fun γ ↦ ?_) g
    obtain ⟨-, low_values⟩ := deep_low.2 γ
    simpa [low, eq_succ] using low_values b u hu μ hμ

/-- Let `S.pointsOver c i e orders depth` be the points of the extension of the side `S` that
project to `p ^ e` times the component of `1 ⊗ c` at the letter `i`, have the given orders, and are
fixed by `Γ'` modulo the vectors with orders `depth`. Let `x` be such a point. If `I` contains the
steps `(a, n)` from `depth` to `depth'` at all jumps `u` at the letter `a` steps before `i`, and
`e'` is at least `e` plus their costs `cost a n = v_p(n) + k.differentBound + 3 a`, then there is a
point over `p ^ e' • c` with depth `depth'` and orders `improvedOrders orders depth'`. -/
lemma pointsOver_nonempty_of_costs {e e' : ℕ} {depth depth' orders : ℕ → ℤ → ℤ}
    {x : S.extensionLattice.Ambient} (hx : x ∈ S.pointsOver c i e orders depth)
    (I : Finset ((_ : ℕ) × ℤ))
    (cover : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ n : ℤ,
      depth a u ≤ n → n < depth' a u → ⟨a, n⟩ ∈ I)
    (h_cost : e + ∑ q ∈ I, cost q.1 q.2 ≤ e') :
    (S.pointsOver c i e' (improvedOrders orders depth') depth').Nonempty := by
  -- Apply the operator `A` of `exists_isOperatorOfCost_and_mem_deepElements` to `y = p ^ s • x`,
  -- where `s` is the slack in `h_cost`.
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, e + ∑ q ∈ I, cost q.1 q.2 + s = e' := h_cost.dest
  obtain ⟨A, A_cost, A_deep⟩ := S.exists_isOperatorOfCost_and_mem_deepElements I
  obtain ⟨x_mem, pr_x, x_exp, x_deep⟩ := hx
  let y : S.extensionLattice.kisinLoc := p ^ s • ⟨x, x_mem⟩
  have y_deep {d : ℕ → ℤ → ℤ} (deep : x ∈ invariantsMod (S.extensionLattice.withOrders i d)) :
      y ∈ S.deepElements i d :=
    smul_of_tower_mem _ _ ⟨⟨p ^ e • c, by simp [pr_x]⟩, deep⟩
  have y_own : y ∈ S.deepElements i orders := y_deep (smul_sub_mem_withOrders x_exp)
  obtain ⟨-, deep⟩ : A y ∈ S.deepElements i depth' := A_deep (y_deep x_deep) depth' cover
  -- `A` keeps `orders`, as `y` is deep for them; the new depth then improves them
  have exp : A y ∈ locKisinPart (S.extensionLattice.withOrders i orders) :=
    A_cost.apply_mem_of_kerWithOrders_le (fun _ ⟨h_exp, _⟩ ↦ h_exp) (nsmul_mem x_exp _) y_own
  refine ⟨A y, (A y).2, ?_, mem_withOrders_improvedOrders exp deep, deep⟩
  -- `A y` and `p ^ (∑ q ∈ I, cost q.1 q.2) • y` lie over the same constant
  calc S.projTrivial.wittMap (A y).1
      = S.projTrivial.wittMap (p ^ (∑ q ∈ I, cost q.1 q.2) • y).1 :=
        sub_mem_ker_iff.1 (A_cost y_own).2
    _ = p ^ (∑ q ∈ I, cost q.1 q.2) • p ^ s • p ^ e • S.constantAt i c := by simp [y, pr_x]
    _ = p ^ (e + ∑ q ∈ I, cost q.1 q.2 + s) • S.constantAt i c := by module

/-- Let `x` lie in `S.pointsOver c i e o₁ o`: it lies over `p ^ e` times the constant of `c` at the
letter `i`, with orders `o₁`, and is fixed by `Γ'` modulo orders `o`. Then for `g` in `k.galMonoid`
the element `(g • x - x) / (z τ)` (`k.zTauUnit⁻¹ • (g • x - x)`) lies in `S.kerWithOrders i o`. -/
lemma zTauUnit_inv_smul_sub_mem_kerWithOrders (hx : x ∈ S.pointsOver c i e o₁ o) (g : k.galMonoid) :
    k.zTauUnit⁻¹ • (g • x - x) ∈ S.kerWithOrders i o := by
  obtain ⟨x_mem, pr_x, -, x_deep⟩ := hx
  refine ⟨JumpLattice.zTauUnit_inv_smul_sub_mem_withOrders x_mem (x_deep g), ?_⟩
  simp [k.galMonoid.smul_def, pr_x, smul_comm, constantAt, gal_smul_letterProj]

/-- Two points `x` and `w` over the same constant, with orders `o₁` and `o₂`, differ by a vector
over `0` with orders `o₁ ⊓ o₂`. -/
lemma sub_mem_kerWithOrders_of_pointsOver (hx : x ∈ S.pointsOver c i e o₁ o)
    (hw : w ∈ S.pointsOver c i e o₂ o₃) : w - x ∈ S.kerWithOrders i (o₁ ⊓ o₂) := by
  obtain ⟨-, pr_x, x_exp, -⟩ := hx
  obtain ⟨-, pr_w, w_exp, -⟩ := hw
  exact ⟨sub_mem (mem_withOrders_of_le w_exp (by simp))
    (mem_withOrders_of_le x_exp (by simp)), by simp [pr_w, pr_x]⟩

/-- Let `φ` be the Frobenius and `S.pointsOver c j e o o'` the points over `p ^ e` times the
constant of `c` at the letter `j` with orders `o` that are fixed by `Γ'` modulo orders `o'` (the
depth). The power `φ ^ l` moves such a point at the letter `i.stepBack l`, `l` steps before `i`, to
a point at `i` over the same constant, with orders `shiftedOrders l 0 o` and depth
`shiftedOrders l 1 o'`. -/
lemma phi_pow_smul_mem_pointsOver (hw : w ∈ S.pointsOver c (i.stepBack l) e o o') :
    φ ^ l • w ∈ S.pointsOver c i e (shiftedOrders l 0 o) (shiftedOrders l 1 o') := by
  have ⟨w_mem, pr_w, w_exp, _⟩ := hw
  refine ⟨phi_pow_smul_mem_kisinLoc w_mem, ?_, phi_pow_smul_mem_withOrders w_exp, fun g ↦ ?_⟩
  · simp [pr_w, smul_comm, phi_pow_smul_constantAt, Perm.coe_inv]
  -- `g • w - w` is divisible by `k.zTau`, and `φ ^ l • k.zTau` vanishes at the levels `a < l`,
  -- which raises the order there from `0` to `1`
  have quot : φ ^ l • k.zTauUnit⁻¹ • (g • w - w) ∈
      S.extensionLattice.withOrders i (shiftedOrders l 0 o') :=
    phi_pow_smul_mem_withOrders (zTauUnit_inv_smul_sub_mem_kerWithOrders hw g).1
  have factor : g • φ ^ l • w - φ ^ l • w =
      (φ ^ l • k.zTau) • φ ^ l • k.zTauUnit⁻¹ • (g • w - w) := by
    simp [← frobGroup_smul_smul, ← zTauUnit_smul, smul_sub, smul_phi_pow_comm]
  rw [factor]
  refine mem_withOrders_of_mem_hodgeFil (smul_mem _ _ quot) fun a u hu h_lt μ hμ ↦ ?_
  -- the order to reach differs from the order of the quotient only at the levels below `l`
  have ha : a < l := by lia
  have h_zTau : phiInvToBdR a (φ ^ l • k.zTau) ∈ hodgeFil 1 := by
    rw [phiInvToBdR_mem_hodgeFil_one_iff, zTau, smul_mul']
    exact (frobE_dvd_phi_pow_tau ha).mul_right _
  simpa [ha] using mul_mem_hodgeFil h_zTau (quot.2 a u hu μ hμ)

/-- The constant `1` of the Tate dual side at the letter `i` acts on `S.Ambient` as the projector to
the letter `i`. -/
lemma wittPairing_constantAt_one (i : k.Letter) (w : S.Ambient) :
    JumpLattice.wittPairing (C := S.kerLattice) (.lsmul O S.Carrier)
      (P.tateDualSide.constantAt i 1) w = S.letterProj i w := by
  revert w
  exact diagTensor_induction (by simp [constantAt, wittPairing_letterProj_left])

/-- Let `P` be a pairing of the lattices `Y`, `Y'` of two sides, given by a form `ψ : Y ⊗ Y' → O(1)`
and a linear map `P.toZp : O → ℤ_p`, modulo `p ^ P.exponent`. Its Tate dual side is the lattice
`Hom(Y ⊗ Y', O(1))`, extended by `O` through the cocycle of `P`. Pair a vector `n` of this
extension, tensored with `W(C^♭)`, with `w ⊗ y` by `P.extensionForm`, which sends `(λ, o)` to the
form `p ^ P.exponent • λ + o • ψ`. The value, reduced modulo `p ^ P.exponent` through `P.toZp`, is
the pairing `P.wittPairing` of `y` with `w` multiplied by the projection of `n` to `W(C^♭) ⊗ O`. -/
lemma map_wittPairing_extensionForm (n : P.tateDualSide.extensionLattice.Ambient) (w : S.Ambient)
    (y : S'.Ambient) :
    DiagTensor.map (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp)
        (JumpLattice.wittPairing (C := tateLattice O) P.extensionForm n
          (JumpLattice.wittPairing (C := S.tensorLattice S')
            (TensorProduct.mk O S.Carrier S'.Carrier) w y)) =
      P.wittPairing (JumpLattice.wittPairing (C := S.kerLattice) (.lsmul O S.Carrier)
        (P.tateDualSide.projTrivial.wittMap n) w) y := by
  -- Both sides are linear in each variable: compare them on pure tensors.
  revert n w y
  refine diagTensor_induction fun _ _ ↦ diagTensor_induction fun _ _ ↦ diagTensor_induction ?_
  -- `extensionForm (λ, o) = p ^ m • λ + o • ψ`: the terms in `ψ` agree, and `p ^ m • λ` is `0`
  -- modulo `p ^ m`
  have h_kill (a : WittCFlat) (z : Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ P.exponent)) χ)) :
      p ^ P.exponent • DiagTensor.mk a z = 0 := by
    rw [← map_nsmul, Selmer.nsmul_quot_eq_zero (by simp) z, map_zero]
  simp [extensionForm, modPairing, mul_assoc, -nsmul_eq_mul, h_kill]

end Points

end PairingSide

end New.Lift.KummerChart

end
