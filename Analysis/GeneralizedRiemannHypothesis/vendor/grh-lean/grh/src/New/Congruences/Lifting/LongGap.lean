import New.Congruences.Lifting.SidePoints

/-!
# The long gap lemma for a side of a Kummer chart, by expansion in powers of E

This file concerns a side `S` over a Kummer chart, whose distinguished element is written `E`. It
defines the constants modulo `E ^ A` and expands vectors in powers of `E` with such constants as
coefficients. It then proves the long gap lemma. The proof multiplies a lift by `f(E)`, with `f`
monic of degree `N`, and takes the `N`-th Taylor coefficient of `p ^ (4 δ)` times the product.

## Main definitions and results

* `New.Lift.KummerChart.JumpLattice.constantsModE`: the constants modulo E^A, with exponents
  `New.Lift.KummerChart.JumpLattice.shiftedStdOrders`.
* `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_long_gap`: the long gap lemma. On an
  unramified Kummer chart, if `E ^ s` kills the cokernel at `i` and `p ^ κ` kills it at
  `i.stepBack l`, the jumps at `i` and the `l - 1` letters before it are at most `g`, `3 ≤ p ^ l`,
  `A ≤ p ^ l * δ`, and there is the long gap `s + g * ∑ a < l, p ^ a < A`, then a constant of the
  trivial lattice lifts, up to a power of p, to a point of the extension at `i` with a large order
  at E at the very negative jumps.

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
* `New.Lift.KummerChart.JumpLattice.withOrders`: for a lattice `L` with a finite set of jumps at
  each letter, the vectors of W(C^♭)⊗L at a letter whose value at φ^a E on the forms of jump u is
  divisible by t^{c(a,u)}; they are said to have the orders `c`.
* `New.Lift.KummerChart.PairingSide`, `New.Lift.KummerChart.PairingSide.KillsCokernel`: one side of
  a pairing: lattices Y and C (`paramLattice`), an O-linear map `cocycleMap` from C to the
  crystalline cocycles Z_f(Y), and for each letter a finite set of integers that contains 0, the
  jumps. The extension `extensionLattice` of C by Y maps by `projTrivial` to `trivialLattice`, the
  lattice C with trivial action. `KillsCokernel`: `p ^ κ * E ^ s` multiplies the part of A_inf ⊗ C
  at a letter into the image of the standard module of level 0 of the extension.
* `New.Lift.KummerChart.PairingSide.pointsOver`: `S.pointsOver c i e o d` is the set of the vectors
  `x` of the Kisin module of the extension, with all φ^a E inverted, that lie over `p ^ e c` at `i`,
  have the orders `o` and have the depth `d`: every `g • x - x` with `g` in Γ' has exponents `d`.

## Relation to the literature

See `New.Congruences.Lifting.CutExponentBounds` for related work.
-/

namespace New.Lift.KummerChart

section LongGap

open Period Submodule Finset Polynomial JumpLattice algebraMap

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O}

/-- The system of exponents obtained from the standard one of level `l` (`0` for `a < l`, `-u` for
`a ≥ l`) by adding `o u` at `a = 0`, that is, at `E`. Here `a` stands for the element φ^a E. -/
abbrev JumpLattice.shiftedStdOrders (l : ℕ) (o : ℤ → ℤ) (a : ℕ) (u : ℤ) : ℤ :=
  stdOrders l a u + if 0 = a then o u else 0

/-- The constants modulo `E ^ A` at the letter `i` of a lattice `L`. Let `x` lie in
`L.stdOrdersPart l i`: in the Kisin module of `L` with all `φ^a E` inverted, at `i`, with the
standard orders of level `l`. This means that the value at `φ^a E` of each form of jump `u` is
divisible by `t ^ c`, where `c` is `0` for `a < l` and `-u` for `a ≥ l`. It is a constant if every
`g • x - x`, for `g` in the subgroup `Γ'` of the chart, has these orders raised by `A` at `E`, that
is, at `a = 0`. The constants form a ℤ_p-module. -/
noncomputable def JumpLattice.constantsModE (l : ℕ) (A : ℕ) (i : k.Letter) :
    Submodule ℤ_[p] (Ambient (k := k) (O := O) (L := L)) :=
  (L.stdOrdersPart l i).restrictScalars ℤ_[p] ⊓
    invariantsMod (withOrders i (shiftedStdOrders l fun _ : ℤ ↦ A))

section ConstantsModE

variable {x : L.Ambient} {l A : ℕ} {i : k.Letter} {o : ℤ → ℤ}

/-- If `x` has the standard orders of level `l` raised by `o` at `E`, it has them raised by any
`o' ≤ o`. -/
lemma JumpLattice.mem_withOrders_shiftedStdOrders_of_le {o' : ℤ → ℤ}
    (hx : x ∈ L.withOrders i (shiftedStdOrders l o)) (h_le : ∀ u : ℤ, o' u ≤ o u) :
    x ∈ L.withOrders i (shiftedStdOrders l o') :=
  mem_withOrders_of_le hx (by grind)

/-- The power `E ^ m` adds `m` to the exponents `o` by which the standard ones are raised at `E`.
Here `k.frobEUnit 0` is `E` as a unit. -/
lemma JumpLattice.frobEUnit_zpow_smul_mem_withOrders_shiftedStdOrders (m : ℤ)
    (hx : x ∈ L.withOrders i (shiftedStdOrders l o)) :
    k.frobEUnit 0 ^ m • x ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ o u + m) :=
  frobEUnit_zpow_smul_mem_withOrders 0 m hx (by grind)

lemma JumpLattice.shiftedStdOrders_zero : shiftedStdOrders l (fun _ : ℤ ↦ (0 : ℤ)) = stdOrders l :=
  funext₂ fun a u ↦ by simp [shiftedStdOrders]

/-- The constants modulo `E ^ A` are stable under multiplication by the unramified Witt vectors
`W(𝔽_{p^f})`. -/
lemma JumpLattice.wittFq_smul_mem_constantsModE (w : WittFq k.f)
    (hx : x ∈ L.constantsModE l A i) : (w : k.S) • x ∈ L.constantsModE l A i := by
  obtain ⟨hx_part, hx_inv⟩ := hx
  refine ⟨smul_mem (L.stdOrdersPart l i) (w : k.S) hx_part, fun g ↦ ?_⟩
  obtain ⟨_, γ, rfl⟩ := g
  -- `Γ'` fixes the coefficient `w`.
  simpa [fixes, smul_eq_val_smul, frobGroup_smul_smul, smul_sub] using smul_mem _ _
    (hx_inv ⟨_, γ, rfl⟩)

/-- A map of lattices `F : L → L'` sends constants modulo `E ^ A` to constants modulo `E ^ A`, if
the jump sets of `L'` lie in those of `L`. -/
lemma JumpLattice.Hom.wittMap_mem_constantsModE {L' : JumpLattice O} (F : L.Hom L')
    (hU : L'.jumpSet ≤ L.jumpSet) (hx : x ∈ L.constantsModE l A i) :
    F.wittMap x ∈ L'.constantsModE l A i := by
  obtain ⟨⟨hx_loc, hx_std⟩, hx_inv⟩ := hx
  refine ⟨⟨F.wittMap_mem_kisinLoc hx_loc, F.wittMap_mem_withOrders hU hx_std⟩, fun g ↦ ?_⟩
  simpa [k.galMonoid.smul_def] using F.wittMap_mem_withOrders hU (hx_inv g)

lemma JumpLattice.frobEUnit_zero_smul : k.frobEUnit 0 • x = k.E • x := rfl

/-- The standard orders of level `l` (`stdOrders l`) are `0` for `a < l` and `-u` for `a ≥ l`;
`shiftedStdOrders l o` adds `o u` to them at `a = 0`. Let `0 < l`, let `ξ` be a constant modulo
`E ^ A` (standard orders, and all `g • ξ - ξ` with `g ∈ Γ'` have them raised by `A` at `a = 0`) and
let `y` have the standard orders. If `ξ + E • y` has the orders `shiftedStdOrders l o`, then `ξ` has
the standard orders raised by `A` at `a = 0` on the jumps `u` with `0 < o u`. -/
lemma JumpLattice.mem_withOrders_of_add_E_smul_mem (hl : 0 < l) {ξ y : L.Ambient}
    (hξ : ξ ∈ L.constantsModE l A i) (hy : y ∈ L.withOrders i (stdOrders l))
    (h_exp : ξ + k.E • y ∈ L.withOrders i (shiftedStdOrders l o)) :
    ξ ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ if o u ≤ 0 then 0 else A) := by
  -- `E • y` has exponent `1` at `E`, so `ξ` has `min 1 o`. As `ξ` is a constant modulo `E ^ A`,
  -- a positive exponent improves to `A`.
  obtain ⟨-, hξ_inv⟩ := hξ
  have hEy : k.E • y ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ min 1 (o u)) := by
    rw [← frobEUnit_zero_smul, ← zpow_one (k.frobEUnit 0)]
    exact frobEUnit_zpow_smul_mem_withOrders 0 1 hy (by grind)
  have h_min : ξ ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ min 1 (o u)) := by
    rw [← add_mem_cancel_right hEy]
    exact mem_withOrders_shiftedStdOrders_of_le h_exp fun u ↦ min_le_right 1 (o u)
  have h_improved : ∀ a : ℕ, ∀ u ∈ L.jumpSet (i.stepBack a),
      shiftedStdOrders l (fun v : ℤ ↦ if o v ≤ 0 then 0 else A) a u ≤
        improvedOrders (shiftedStdOrders l fun v : ℤ ↦ min 1 (o v))
          (shiftedStdOrders l fun _ : ℤ ↦ A) a u := by grind
  exact mem_withOrders_of_le (mem_withOrders_improvedOrders h_min hξ_inv) h_improved

/-- Let `0 < l`, let all `ξ n` be constants modulo `E ^ A` and let `y` have the standard orders. If
`∑ n ≤ N, E ^ n • ξ n + E ^ (N + 1) • y` has the standard orders raised by `o ≤ A` at `E`, then
`ξ N` has them raised by `A` at the jumps `u` with `N < o u`. -/
lemma JumpLattice.mem_withOrders_of_expansion_mem (hl : 0 < l) {ξ : ℕ → L.Ambient}
    {y : L.Ambient} {N : ℕ} (hξ : ∀ n : ℕ, ξ n ∈ L.constantsModE l A i)
    (hy : y ∈ L.withOrders i (stdOrders l)) (ho : ∀ u : ℤ, o u ≤ A)
    (h_exp : ∑ n ∈ range (N + 1), k.E ^ n • ξ n + k.E ^ (N + 1) • y ∈
      L.withOrders i (shiftedStdOrders l o)) :
    ξ N ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ if o u ≤ N then 0 else A) := by
  -- Peel off the constant term and divide by `E`; this lowers `N` and `o` by one.
  induction N generalizing ξ o with
  | zero => exact mem_withOrders_of_add_E_smul_mem hl (hξ 0) hy (by simpa using h_exp)
  | succ N ih =>
    set y' : L.Ambient := ∑ n ∈ range (N + 1), k.E ^ n • ξ (n + 1) + k.E ^ (N + 1) • y with hy'
    have h_split : ∑ n ∈ range (N + 1 + 1), k.E ^ n • ξ n + k.E ^ (N + 1 + 1) • y =
        ξ 0 + k.E • y' := by
      rw [sum_range_succ', add_right_comm, add_comm]
      simp only [hy', smul_add, smul_sum, pow_succ', mul_smul, pow_zero, one_smul]
    rw [h_split] at h_exp
    have hy'_std : y' ∈ L.withOrders i (stdOrders l) := by
      refine add_mem (sum_mem fun n _ ↦ ?_) (smul_of_tower_mem _ _ hy)
      obtain ⟨⟨-, h_std⟩, -⟩ := hξ (n + 1)
      exact smul_of_tower_mem _ _ h_std
    have h_le : ∀ u : ℤ, o u ≤ (if o u ≤ 0 then 0 else A : ℤ) := by grind
    have h_const : ξ 0 ∈ L.withOrders i (shiftedStdOrders l o) :=
      mem_withOrders_shiftedStdOrders_of_le
        (mem_withOrders_of_add_E_smul_mem hl (hξ 0) hy'_std h_exp) h_le
    have hy'_exp : y' ∈ L.withOrders i (shiftedStdOrders l fun u : ℤ ↦ o u + -1) := by
      rw [add_mem_cancel_left h_const, ← frobEUnit_zero_smul] at h_exp
      simpa only [zpow_neg_one, inv_smul_smul] using
        frobEUnit_zpow_smul_mem_withOrders_shiftedStdOrders (-1) h_exp
    have h_index : ∀ u : ℤ, (if o u ≤ (N + 1 : ℕ) then 0 else A : ℤ) ≤
        (if o u + -1 ≤ N then 0 else A : ℤ) := by grind
    exact mem_withOrders_shiftedStdOrders_of_le (ih (fun n ↦ hξ (n + 1)) (by grind) hy'_exp) h_index

/-- The forms of `L` are the `A_inf`-linear maps `μ : W(C^♭) ⊗ L → B_dR` that are equivariant on
`1 ⊗ L` for the subgroup `Γ'` (`k.subgroup`) of the chart; `toGp` maps it to the Galois group. Let
`0 < l`. Let `x` lie in the image under `φ ^ l` of the `A_inf`-module `L.kisinAinf`, and let all
forms take values at `x` in the field `𝒦₀ = k.valueField 0`. Let `g μ(x) - μ(x)` lie in
`hodgeFil A = t ^ A B_dR⁺` for all forms `μ` and all `g` in `Γ'`. Then the projection
`L.letterProj i x` of `x` to the letter `i` is a constant modulo `E ^ A`: it has the standard
orders of level `l`, and every `g • y - y` for this projection `y` has them raised by `A` at
`E`. -/
lemma JumpLattice.letterProj_mem_constantsModE (hl : 0 < l) (i : k.Letter)
    (hx_points : x ∈ L.valueFieldPoints (frobKisinAinf l))
    (hx_forms : ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g • μ x - μ x ∈ hodgeFil A) :
    L.letterProj i x ∈ L.constantsModE l A i := by
  have h_part : L.letterProj i x ∈ stdOrdersPart l i :=
    letterProj_mem_stdOrdersPart hx_points
  -- `g • y - y` keeps the standard exponents, so only the exponent `A` at `E` (`a = 0`) is new.
  refine ⟨h_part, fun g ↦ ?_⟩
  obtain ⟨⟨h_value, -⟩, h_std⟩ := h_part
  obtain ⟨_, γ, rfl⟩ := g
  refine mem_withOrders_of_mem_hodgeFil (smul_sub_mem_withOrders h_std _)
    fun a u _ h_lt μ hμ ↦ ?_
  obtain rfl : 0 = a := by_contra fun h_ne ↦ by simp [shiftedStdOrders, h_ne] at h_lt
  obtain ⟨hμ_form, -⟩ := hμ
  -- The hypothesis on `x` applies to the form `μ ∘ letterProj i`.
  have h_mem : toGp γ • μ (L.letterProj i x) - μ (L.letterProj i x) ∈ hodgeFil A :=
    hx_forms _ (comp_letterProj_mem_forms hμ_form) γ
  have h_exponent : shiftedStdOrders l (fun _ : ℤ ↦ A) 0 u = A := by
    simp [shiftedStdOrders, stdOrders, hl]
  rwa [valueAt_smul_sub h_value hμ_form, h_exponent, valueAt_zero]

/-- On an unramified chart (`E = z + p`), every `s` in the ring `k.S = Λ⟦z⟧` has an expansion in
powers of `E` with coefficients in `Λ = WittFq k.f = W(𝔽_{p^f})`: there are `w n` such that
`s = ∑ n < N, E ^ n * w n` modulo `E ^ N` for all `N`. -/
lemma exists_expansion_pow_E (hk : k.IsUnramified) (s : k.S) :
    ∃ w : ℕ → WittFq k.f, ∀ N : ℕ, ∃ t : k.S,
      s = ∑ n ∈ range N, k.E ^ n * (w n : k.S) + k.E ^ N * t := by
  -- As `e = 1`, division by `E` leaves a remainder in `W(𝔽_{p^f})`; divide repeatedly.
  obtain ⟨-, he, -⟩ := hk
  have h_rem (r : k.S) : ∃ (w : WittFq k.f) (t : k.S), r - w = k.E * t := by
    obtain ⟨w, hw⟩ := k.exists_dvd_sub_sum_z_pow 0 (N := 1) (by simp [he]) r
    exact ⟨w 0, by simpa [Algebra.smul_def, Chart.frobE, dvd_def] using hw⟩
  choose w t h_div using h_rem
  -- The remainders of the iterated quotients `t^[n] s` are the digits.
  refine ⟨fun n : ℕ ↦ w (t^[n] s), fun N ↦ ⟨t^[N] s, ?_⟩⟩
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, Function.iterate_succ_apply']
    linear_combination ih + k.E ^ N * h_div (t^[N] s)

/-- Expansion in powers of `E` with nearly invariant coefficients, on an unramified chart (`e = 1`).
Let `x` be a vector of the Kisin module of `L` with all `φ^a E` inverted at the letter `i`, with the
standard orders of level `l`: the value at `φ^a E` on the jump `u` has order `0` for `a < l` and
`-u` for `a ≥ l`. Let `0 < l`, `3 ≤ p ^ l`, and let `δ` be a natural number with `A ≤ p ^ l * δ`;
the price of the expansion is the factor `p ^ (4 * δ)`. Then there are constants `ξ n` modulo
`E ^ A` such that for every `N` the vector `p ^ (4 * δ) • x` is `∑ n < N, E ^ n • ξ n` plus `E ^ N`
times a vector of `L.stdOrdersPart l i`. -/
lemma JumpLattice.exists_taylor_expansion_of_mem_stdOrdersPart (hl : 0 < l)
    (hk : k.IsUnramified) {δ : ℕ} (h_three : 3 ≤ p ^ l) (h_depth : A ≤ p ^ l * δ)
    (hx : x ∈ L.stdOrdersPart l i) :
    ∃ ξ : ℕ → L.Ambient,
      (∀ n : ℕ, ξ n ∈ L.constantsModE l A i) ∧
      ∀ N : ℕ, ∃ y ∈ L.stdOrdersPart l i,
        p ^ (4 * δ) • x = ∑ n ∈ range N, k.E ^ n • ξ n + k.E ^ N • y := by
  -- The frame theorem writes `p ^ (4 * δ) • x` as `∑ a, r a • b a` with `r a` in `S` and `b a`
  -- constants modulo `E ^ A`. Expand each `r a` in powers of `E` and collect the terms.
  obtain ⟨h_points, h_letter⟩ := mem_stdOrdersPart_iff.1 hx
  have ⟨_, (he : k.e = 1), _⟩ := hk
  let almostFixed : Set L.Ambient :=
    {y ∈ L.valueFieldPoints (L.frobKisinAinf l) |
      ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g • μ y - μ y ∈ hodgeFil A}
  have hx_span : p ^ (4 * δ) • x ∈ span k.S almostFixed :=
    frame_theorem.pow_smul_mem_span_of_mem_valueFieldPoints l A δ (by rwa [he, mul_one])
      (by rwa [he, one_mul]) x h_points
  obtain ⟨m, r, v, h_sum⟩ : ∃ (m : ℕ) (r : Fin m → k.S) (v : Fin m → almostFixed),
      ∑ a : Fin m, r a • (v a : L.Ambient) = p ^ (4 * δ) • x := mem_span_set'.1 hx_span
  let b : Fin m → L.Ambient := fun a ↦ L.letterProj i (v a)
  have hb (a : Fin m) : b a ∈ L.constantsModE l A i := by
    obtain ⟨hv_points, hv_forms⟩ := (v a).property
    exact letterProj_mem_constantsModE hl i hv_points hv_forms
  have h_comb : p ^ (4 * δ) • x = ∑ a : Fin m, r a • b a := by
    simpa [b, mem_letterPart_iff_letterProj.1 h_letter] using congrArg (L.letterProj i) h_sum.symm
  have h_expand : ∀ a : Fin m, ∃ w : ℕ → WittFq k.f, ∀ N : ℕ, ∃ t : k.S,
      r a = ∑ n ∈ range N, k.E ^ n * (w n : k.S) + k.E ^ N * t :=
    fun a ↦ exists_expansion_pow_E hk (r a)
  choose w t h_digits using h_expand
  refine ⟨fun n : ℕ ↦ ∑ a : Fin m, (w a n : k.S) • b a,
    fun n ↦ sum_mem fun a _ ↦ wittFq_smul_mem_constantsModE (w a n) (hb a),
    fun N ↦ ⟨∑ a : Fin m, t a N • b a, sum_smul_mem _ _ fun a _ ↦ (hb a).left, ?_⟩⟩
  calc p ^ (4 * δ) • x = ∑ a : Fin m, r a • b a := h_comb
    _ = ∑ a : Fin m, (∑ n ∈ range N, k.E ^ n * (w a n : k.S) + k.E ^ N * t a N) • b a := by
        simp only [← h_digits]
    _ = ∑ n ∈ range N, k.E ^ n • ∑ a : Fin m, (w a n : k.S) • b a +
          k.E ^ N • ∑ a : Fin m, t a N • b a := by
        simp only [add_smul, sum_smul, mul_smul, smul_sum, sum_add_distrib]
        rw [sum_comm]

lemma JumpLattice.frobEUnit_zpow_natCast_smul (a n : ℕ) :
    k.frobEUnit a ^ (n : ℤ) • x = k.frobE a ^ n • x := by
  rw [zpow_natCast, frobEUnit_pow_smul]
  rfl

/-- On an unramified chart, let `y` be a vector of `W(C^♭) ⊗ L` with orders
`raisedOrdersAtZero (-s)` at the letter `i`: the value at `φ^a E` of a form of jump `u` is divisible
by `t` to the power `-u - s` for `a = 0` and `-u` for the other `a`. Then there is a monic `f` in
`ℤ[X]` of degree `s + g * ∑ j < l, p ^ j` such that `f(E) • y` has orders `g - u` at `φ^a E` for
`a < l` and `-u` for `a ≥ l`. -/
lemma JumpLattice.exists_isMonicOfDegree_aeval_smul_mem (hk : k.IsUnramified) {s : ℕ} (g l : ℕ)
    {y : L.Ambient} (hy : y ∈ L.withOrders i (raisedOrdersAtZero (-s))) :
    ∃ f : ℤ[X],
      f.IsMonicOfDegree (s + g * ∑ t ∈ range l, p ^ t) ∧
      aeval k.E f • y ∈ L.withOrders i fun (a : ℕ) (u : ℤ) ↦ (if a < l then g else 0) - u := by
  -- Take `f(E) = E^s ∏_{a<l} (φ^a E)^g`, which is monic in `E` since `φ^a E = (E - p)^(p^a) + p`.
  obtain ⟨hE, -⟩ := hk
  induction l with
  | zero =>
    refine ⟨X ^ s, by simpa using isMonicOfDegree_X_pow ℤ s, ?_⟩
    rw [map_pow, aeval_X, show k.E = k.frobE 0 by rfl, ← frobEUnit_zpow_natCast_smul]
    exact frobEUnit_zpow_smul_mem_withOrders 0 s hy (by grind)
  | succ l ih =>
    obtain ⟨f, hf, hfy⟩ := ih
    let F : ℤ[X] := (X - Polynomial.C (p : ℤ)) ^ p ^ l + (p : ℤ[X])
    have hF : F.IsMonicOfDegree (1 * p ^ l) :=
      ((isMonicOfDegree_X_sub_one _).pow (p ^ l)).add_right (q := p) (by simp [NeZero.pos])
    have h_eval : aeval k.E F = k.frobE l :=
      Subtype.ext (by simp [F, val_frobE, phi_pow_smul_z, hE])
    refine ⟨F ^ g * f, ?_, ?_⟩
    · rw [sum_range_succ, mul_add, ← add_assoc, add_comm, mul_comm g]
      simpa only [one_mul] using (hF.pow g).mul hf
    · rw [map_mul, map_pow, h_eval, mul_smul, ← frobEUnit_zpow_natCast_smul]
      exact frobEUnit_zpow_smul_mem_withOrders l g hfy (by grind)

/-- Let `0 < l`, let `f` be monic of degree `N < A`, let all `ξ n` be constants modulo `E ^ A` in
the extension and let `y` have the standard orders. Suppose that `projTrivial` sends
`∑ n ≤ N, E ^ n • ξ n + E ^ (N + 1) • y` to `p ^ e • f(E) • c`, where `c` stands for
`S.constantAt i c`, the image of `1 ⊗ c` at the letter `i`. Then it sends `ξ N` to `p ^ e • c` up to
a vector that has the standard orders raised by `A` at `E`. -/
lemma PairingSide.projTrivial_coeff_sub_mem_withOrders {S : PairingSide O} (hl : 0 < l)
    {f : ℤ[X]} {N e : ℕ} (hf : f.IsMonicOfDegree N) (hA : N < A) {c : S.paramLattice}
    {ξ : ℕ → S.extensionLattice.Ambient} {y : S.extensionLattice.Ambient}
    (hξ : ∀ n : ℕ, ξ n ∈ S.extensionLattice.constantsModE l A i)
    (hy : y ∈ S.extensionLattice.withOrders i (stdOrders l))
    (h_over : S.projTrivial.wittMap (∑ n ∈ range (N + 1), k.E ^ n • ξ n + k.E ^ (N + 1) • y) =
      p ^ e • aeval k.E f • S.constantAt i c) :
    S.projTrivial.wittMap (ξ N) - p ^ e • S.constantAt i c ∈
      S.trivialLattice.withOrders i (shiftedStdOrders l fun _ : ℤ ↦ A) := by
  -- The differences `η n` of the coefficients on the two sides are constants modulo `E ^ A` and
  -- form an expansion of `0`.
  have hU : S.trivialLattice.jumpSet ≤ S.extensionLattice.jumpSet := fun j ↦
    singleton_subset_iff.2 (S.zero_mem j)
  have hc : S.constantAt i c ∈ S.trivialLattice.constantsModE l A i :=
    ⟨constantAt_mem_stdOrdersPart c, fun g ↦ by
      simp [k.galMonoid.smul_def, constantAt, gal_smul_letterProj]⟩
  set η : ℕ → S.trivialLattice.Ambient :=
    fun n ↦ S.projTrivial.wittMap (ξ n) - p ^ e • f.coeff n • S.constantAt i c with hη_def
  have hη (n : ℕ) : η n ∈ S.trivialLattice.constantsModE l A i :=
    sub_mem (S.projTrivial.wittMap_mem_constantsModE hU (hξ n)) (nsmul_mem (zsmul_mem hc _) _)
  have h_poly : p ^ e • aeval k.E f • S.constantAt i c =
      ∑ n ∈ range (N + 1), k.E ^ n • p ^ e • f.coeff n • S.constantAt i c := by
    simp only [aeval_eq_sum_range, hf.natDegree_eq, sum_smul, smul_sum, smul_assoc,
      smul_comm (k.E ^ _)]
  have h_zero : ∑ n ∈ range (N + 1), k.E ^ n • η n + k.E ^ (N + 1) • S.projTrivial.wittMap y =
    0 := by
    simp only [hη_def, smul_sub, sum_sub_distrib]
    rw [← h_poly, ← h_over, sub_add_eq_add_sub, sub_eq_zero]
    simp
  have hη_exp : η N ∈ S.trivialLattice.withOrders i
      (shiftedStdOrders l fun _ : ℤ ↦ if (A : ℤ) ≤ N then 0 else A) :=
    mem_withOrders_of_expansion_mem hl hη (S.projTrivial.wittMap_mem_withOrders hU hy)
      (fun _ ↦ le_rfl) (by simp only [h_zero, ZeroMemClass.zero_mem])
  have h_lead : f.coeff N = 1 := by rw [← hf.natDegree_eq, hf.monic.coeff_natDegree]
  simpa only [hη_def, h_lead, one_smul, Nat.cast_le, hA.not_ge, ite_false] using hη_exp

end ConstantsModE

/-- Let `p ^ κ` kill the cokernel of the side `S` at the letter `l` steps before `i`. Let `z` be a
vector of the trivial lattice `S.trivialLattice` at `i` with the standard orders of level `l`
(`stdOrdersPart l i`). Then `p ^ κ • z` is the image under `projTrivial` of a vector of the
extension `S.extensionLattice` with the same exponents at `i`. -/
lemma PairingSide.exists_lift_pow_smul_of_killsCokernel_stepBack {l κ : ℕ} {i : k.Letter}
    {S : PairingSide O} (h_kill : S.KillsCokernel (i.stepBack l) κ 0) {z : S.trivialLattice.Ambient}
    (hz : z ∈ S.trivialLattice.stdOrdersPart l i) :
    ∃ x ∈ S.extensionLattice.stdOrdersPart l i, S.projTrivial.wittMap x = p ^ κ • z := by
  -- `φ ^ l` carries the ideal of the killers at the letter `i.stepBack l` to that at `i`.
  have h_mem : ((p ^ κ : k.S) : Ainf) ∈ S.liftIdeal 0 l i := by
    simpa [-CharP.cast_eq_zero] using (phi_pow_smul_mem_liftIdeal_iff l).2 h_kill
  obtain ⟨t, ht⟩ := exists_lift_of_mem_liftIdeal (f := p ^ κ) h_mem
  simpa [← Nat.cast_smul_eq_nsmul Ainf] using ht z hz

/-- The Taylor coefficient in the long gap lemma. Let `S` be a side, with lattices Y and
`C = S.paramLattice`, cocycles, and a finite jump set `S.jumpSet` at each letter. Let the chart be
unramified (`E = z + p` and `e = 1`). Let `0 < l`, `3 ≤ p ^ l` and `A ≤ p ^ l δ`. Let `E ^ s` kill
the cokernel at `i` (`KillsCokernel i 0 s`: it multiplies `A_inf ⊗ C` at `i` into the image of the
extension of level `0`). Let the jumps at the `l` letters `i.stepBack a` (`a` Frobenius steps before
`i`, `a < l`) be at most `g`, and let `N = s + g (1 + p + ⋯ + p ^ (l - 1)) < A`. Then for each `c`
in `C` there is a `ξ` in `constantsModE l A i` of the extension lattice, a constant modulo `E ^ A`.
It has the standard orders of level `l` (`0` below `l`, `-u` on the jump `u` from `l` on), raised by
`A` at `E` at the jumps `u < -N`. Moreover `projTrivial` sends `ξ` to `p ^ (4 δ) • S.constantAt i c`
up to a vector of the trivial lattice with these orders raised by `A` at `E` at every jump. -/
lemma PairingSide.exists_wittMap_sub_smul_constantAt_mem_of_long_gap {l A s g δ N : ℕ}
    {i : k.Letter} {S : PairingSide O} (hl : 0 < l) (hk : k.IsUnramified) (h_three : 3 ≤ p ^ l)
    (h_depth : A ≤ p ^ l * δ) (h_kill : S.KillsCokernel i 0 s)
    (h_jumps : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), u ≤ g)
    (hN : s + g * ∑ a ∈ range l, p ^ a = N) (h_long : N < A) (c : S.paramLattice) :
    ∃ ξ ∈ S.extensionLattice.constantsModE l A i,
      ξ ∈ S.extensionLattice.withOrders i (shiftedStdOrders l fun u : ℤ ↦ if u < -N then A else 0) ∧
      S.projTrivial.wittMap ξ - p ^ (4 * δ) • S.constantAt i c ∈
        S.trivialLattice.withOrders i (shiftedStdOrders l fun _ : ℤ ↦ A) := by
  -- Multiply a point `y` over `c` by `f(E)` with `f` monic of degree `N`, and take the `N`-th
  -- Taylor coefficient of `p^(4δ) f(E) y`.
  -- As the jumps are at most `g`, the exponents of `f(E) y` are at least these two systems.
  have h_std (a : ℕ) (u : ℤ) (hu : u ∈ S.jumpSet (i.stepBack a)) :
      stdOrders l a u ≤ (if a < l then g else 0) - u := by grind
  have h_shifted (a : ℕ) (u : ℤ) (hu : u ∈ S.jumpSet (i.stepBack a)) :
      shiftedStdOrders l (fun v : ℤ ↦ min (A : ℤ) (g - v)) a u ≤ (if a < l then g else 0) - u := by
        grind
  obtain ⟨y, hy, hy_over, hy_exp, -⟩ :
      (S.pointsOver c i 0 (raisedOrdersAtZero (-s)) (raisedOrdersAtZero (-s))).Nonempty :=
    pointsOver_nonempty_of_killsCokernel h_kill c
  obtain ⟨f, hf, hfy⟩ : ∃ f : ℤ[X], f.IsMonicOfDegree N ∧
      aeval k.E f • y ∈ S.extensionLattice.withOrders i
        fun (a : ℕ) (u : ℤ) ↦ (if a < l then g else 0) - u := by
    rw [← hN]
    exact exists_isMonicOfDegree_aeval_smul_mem hk g l hy_exp
  have hfy_part : aeval k.E f • y ∈ S.extensionLattice.stdOrdersPart l i :=
    ⟨smul_mem _ _ hy, mem_withOrders_of_le hfy h_std⟩
  obtain ⟨ξ, hξ, h_taylor⟩ : ∃ ξ : ℕ → S.extensionLattice.Ambient,
      (∀ n : ℕ, ξ n ∈ S.extensionLattice.constantsModE l A i) ∧
      ∀ M : ℕ, ∃ y' ∈ S.extensionLattice.stdOrdersPart l i,
        p ^ (4 * δ) • aeval k.E f • y = ∑ n ∈ range M, k.E ^ n • ξ n + k.E ^ M • y' :=
    exists_taylor_expansion_of_mem_stdOrdersPart hl hk h_three h_depth hfy_part
  obtain ⟨y', ⟨-, hy'⟩, h_sum⟩ := h_taylor (N + 1)
  -- The exponents of `ξ N` at `E`, from the exponents `min A (g - u)` of `f(E) y`.
  have hξ_exp : ξ N ∈ S.extensionLattice.withOrders i
      (shiftedStdOrders l fun u : ℤ ↦ if min (A : ℤ) (g - u) ≤ N then 0 else A) := by
    refine mem_withOrders_of_expansion_mem hl hξ hy' (fun u ↦ min_le_left (A : ℤ) (g - u)) ?_
    rw [← h_sum]
    exact nsmul_mem (mem_withOrders_of_le hfy h_shifted) _
  -- If `u < -N`, then `N < g - u`, so `ξ N` has exponent `A` at `E`.
  refine ⟨ξ N, hξ N, mem_withOrders_shiftedStdOrders_of_le hξ_exp fun u ↦ by omega, ?_⟩
  refine projTrivial_coeff_sub_mem_withOrders hl hf h_long hξ hy' ?_
  simp [← h_sum, hy_over]

/-- Long gap, for a side `S` with lattice `C = S.paramLattice` and finite jump sets at the letters.
Let the chart be unramified, `3 ≤ p ^ l` and `A ≤ p ^ l δ`. Let `p ^ κ` kill the cokernel at the
letter `l` steps before `i`, and `E ^ s` the cokernel at `i`. Let the jumps at the `l` letters up to
`i` be at most `g`, and let `N = s + g (1 + p + ⋯ + p ^ (l - 1)) < A`. Then for each `c` in `C` the
extension has a point `x` at `i` over `p ^ (κ + 4 δ) c` with the standard orders of level `l`,
raised by `A` at `E` at the jumps `u < -N`, such that all `γ x - x` with `γ` in the subgroup `Γ'` of
the chart have the standard orders raised by `A` at `E` at every jump. -/
lemma PairingSide.pointsOver_nonempty_of_long_gap {l A κ s g δ N : ℕ} {i : k.Letter}
    {S : PairingSide O} (hk : k.IsUnramified) (h_three : 3 ≤ p ^ l) (h_depth : A ≤ p ^ l * δ)
    (h_kill_before : S.KillsCokernel (i.stepBack l) κ 0) (h_kill : S.KillsCokernel i 0 s)
    (h_jumps : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), u ≤ g)
    (hN : s + g * ∑ a ∈ range l, p ^ a = N) (h_long : N < A) (c : S.paramLattice) :
    (S.pointsOver c i (κ + 4 * δ) (shiftedStdOrders l fun u : ℤ ↦ if u < -N then A else 0)
      (shiftedStdOrders l fun _ : ℤ ↦ A)).Nonempty := by
  -- Take the Taylor coefficient `ξ` over `p^(4δ) c` up to an error `w` divisible by `E^A`. The
  -- killer `p^κ` lifts the error, so it can be removed.
  have hl : 0 < l := Nat.pos_of_ne_zero fun h_zero ↦ by simp [h_zero] at h_three
  obtain ⟨ξ, ⟨⟨hξ_loc, -⟩, hξ_inv⟩, hξ_order, hw_exp⟩ :
      ∃ ξ ∈ S.extensionLattice.constantsModE l A i,
        ξ ∈ S.extensionLattice.withOrders i (shiftedStdOrders l fun u : ℤ ↦ if u < -N then A else 0)
          ∧
        S.projTrivial.wittMap ξ - p ^ (4 * δ) • S.constantAt i c ∈
          S.trivialLattice.withOrders i (shiftedStdOrders l fun _ : ℤ ↦ A) :=
    exists_wittMap_sub_smul_constantAt_mem_of_long_gap hl hk h_three h_depth h_kill h_jumps hN
      h_long c
  set w : S.trivialLattice.Ambient := S.projTrivial.wittMap ξ - p ^ (4 * δ) • S.constantAt i c with
    hw
  have hw_loc : w ∈ S.trivialLattice.kisinLoc := by
    obtain ⟨hc_loc, -⟩ := constantAt_mem_stdOrdersPart (l := l) (i := i) c
    exact sub_mem (S.projTrivial.wittMap_mem_kisinLoc hξ_loc) (nsmul_mem hc_loc _)
  -- As `E ^ (-A) w` has the standard exponents, the killer lifts it, times `p ^ κ`, to some `x`.
  obtain ⟨x, ⟨hx, hx_exp⟩, hx_over⟩ : ∃ x ∈ S.extensionLattice.stdOrdersPart l i,
      S.projTrivial.wittMap x = p ^ κ • k.frobEUnit 0 ^ (-A : ℤ) • w := by
    refine exists_lift_pow_smul_of_killsCokernel_stepBack h_kill_before
      ⟨frobEUnit_zpow_smul_mem_kisinLoc_iff.2 hw_loc, ?_⟩
    simpa [shiftedStdOrders_zero] using frobEUnit_zpow_smul_mem_withOrders_shiftedStdOrders (-A)
      hw_exp
  have hEx_exp : k.frobEUnit 0 ^ (A : ℤ) • x ∈
      S.extensionLattice.withOrders i (shiftedStdOrders l fun _ : ℤ ↦ A) := by
    rw [← shiftedStdOrders_zero] at hx_exp
    simpa only [zero_add] using frobEUnit_zpow_smul_mem_withOrders_shiftedStdOrders A hx_exp
  set z : S.extensionLattice.Ambient := p ^ κ • ξ - k.frobEUnit 0 ^ (A : ℤ) • x with hz
  have hz_loc : z ∈ S.extensionLattice.kisinLoc :=
    sub_mem (nsmul_mem hξ_loc _) (frobEUnit_zpow_smul_mem_kisinLoc_iff.2 hx)
  have hz_over : S.projTrivial.wittMap z = p ^ (κ + 4 * δ) • S.constantAt i c := by
    have h_over : S.projTrivial.wittMap ξ = w + p ^ (4 * δ) • S.constantAt i c := by simp [hw]
    simp [hz, h_over, hx_over, smul_comm (_ ^ A) (p ^ κ), pow_add, mul_smul, smul_add,
      -nsmul_eq_mul]
  have hz_exp : z ∈
      S.extensionLattice.withOrders i (shiftedStdOrders l fun u : ℤ ↦ if u < -N then A else 0) :=
    sub_mem (nsmul_mem hξ_order _) (mem_withOrders_shiftedStdOrders_of_le hEx_exp fun u ↦ by omega)
  have hz_inv : z ∈ invariantsMod (S.extensionLattice.withOrders i
    (shiftedStdOrders l fun _ : ℤ ↦ A)) :=
    sub_mem (nsmul_mem hξ_inv _) (smul_sub_mem_withOrders hEx_exp)
  exact ⟨z, hz_loc, hz_over, hz_exp, hz_inv⟩

end LongGap

end New.Lift.KummerChart
