import IPRADerivations.Core.Parity
import IPRADerivations.Core.LinearCombination

/-!
# The scales of the approximate face collision (`dimension_invariance_ipra`, `thm:collision`)

Packet: `topology/dimension_invariance_ipra`, theorem `thm:collision`. Its proof sets
"`δ = 2^{-a}`, `k = a + d + 3`, `p = k + 1`, `N = 2^{μ(k)}`, `h = δ/2`" (`eq:scales`) and
computes (`eq:smallbound`)

  `2^{-k} + 2 · 2^{-p} = 2^{1−k} = δ/2^{d+2} ≤ δ/(4d) < δ/(2d) = h/d`,

"We used `d ≥ 1` and `d ≤ 2^d`", so that the large-variation alternative is excluded; then for
the returned opposite-face vertices

  `‖f(q) − f(q')‖ ≤ dist(F(u), F(v)) + 2^{1−p} < δ/2 + 2^{-k} ≤ δ/2 + δ/16 = 9δ/16 < δ`.

In units of `2^{-p}` the quantities are natural numbers: `2^{-p} = 1`, `2^{-k} = 2`,
`h = δ/2 = 2^{d+3}` and `δ = 2^{d+4}` (since `p − a = d + 4`). The sample distance of two
vertices of a Kuhn simplex is at most `2^{-k} + 2 · 2^{-p} = 4`.

* `lt_pw_two`: `d < 2^d`;
* `small_bound`: `s ≤ 4` gives `d · s < 2^{d+3}`, that is `s < h/d`: the sample distance is
  below the threshold of the large-variation alternative;
* `final_bound`: `D < 2^{d+3}` gives `D + 2 < 2^{d+4}`, that is
  `dist(F(u), F(v)) + 2^{1−p} < δ`: the strict conclusion of the theorem;
* `delta_units`: `2^{a + (d+4)} = 2^a · 2^{d+4}`, the conversion of `δ = 2^{-a}` into the unit.

Not derived: the modulus bound for the sampled table (the hypothesis `s ≤ 4`), and the
finite alternative `thm:alternative` for `d > 2` (the case `d = 2` of the finite obstruction is
`Topology/DimensionTwo`, `Topology/DimensionUnits`).
-/

namespace LeanProofs.IPRA.Topology.CollisionScales

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `d < 2^d` -/

/-- Variable `0 = d`. -/
private abbrev ltPwF : Fm PTm 1 := le (succ (var 0)) (pw two (var 0))

private theorem lt_pw₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] ltPwF := by
  refine ind _ trivial ?_ ?_
  · pw_subst
    refine le_of_eq_add (d := zero) ((pw_zero two).eqTrans ?_)
    ipra_ring
  · pw_subst
    refine le_of_eq_add (d := var 0 + monus (pw two (var 0)) (succ (var 0)) +
      monus (pw two (var 0)) (succ (var 0))) ?_
    ipra_lc natEq (pw_succ (Γ := [ltPwF]) two (var 0)) + 2 * natEq (eq_add_of_le (Prf.hyp0 (Γ := []) (φ := ltPwF)))

/-- `d < 2^d`. -/
theorem lt_pw_two (d : PTm n) : Γ ⊢[PRAAx] lt d (pw two d) := by
  have h := inst (Γ := Γ) lt_pw₀ ![d]
  simp at h
  exact h

/-! ## The two strict bounds -/

/-- `d + 3` and `d + 4` as exponents. -/
abbrev e3 (d : PTm n) : PTm n := succ (succ (succ d))
abbrev e4 (d : PTm n) : PTm n := succ (e3 d)

/-- `eq:smallbound`: a sample distance `s ≤ 4` (in units of `2^{-p}`) satisfies
`d · s < 2^{d+3} = h`. -/
theorem small_bound {d s : PTm n} (hs : Γ ⊢[PRAAx] le s (num 4)) :
    Γ ⊢[PRAAx] lt (d * s) (pw two (e3 d)) := by
  refine le_of_eq_add (d := d * monus (num 4) s + num 4 * d + num 7 +
    num 8 * monus (pw two d) (succ d)) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) two (succ (succ d))) + 2 * natEq (pw_succ (Γ := Γ) two (succ d)) +
    4 * natEq (pw_succ (Γ := Γ) two d) + 8 * natEq (eq_add_of_le (lt_pw_two (Γ := Γ) d)) +
    𝔞 d * natEq (eq_add_of_le hs)

/-- The last chain of `thm:collision`: `D < 2^{d+3} = δ/2` gives `D + 2 < 2^{d+4} = δ`. -/
theorem final_bound {d D : PTm n} (h : Γ ⊢[PRAAx] lt D (pw two (e3 d))) :
    Γ ⊢[PRAAx] lt (D + two) (pw two (e4 d)) := by
  refine le_of_eq_add (d := monus (pw two (e3 d)) (succ D) + num 8 * d + num 6 +
    num 8 * monus (pw two d) (succ d)) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) two (e3 d)) + natEq (eq_add_of_le h) +
    natEq (pw_succ (Γ := Γ) two (succ (succ d))) + 2 * natEq (pw_succ (Γ := Γ) two (succ d)) +
    4 * natEq (pw_succ (Γ := Γ) two d) + 8 * natEq (eq_add_of_le (lt_pw_two (Γ := Γ) d))

/-- `δ = 2^{-a}` is `2^{d+4}` units of `2^{-p}`, `p = a + d + 4`. -/
theorem delta_units (a d : PTm n) :
    Γ ⊢[PRAAx] pw two (a + e4 d) ≐ pw two a * pw two (e4 d) :=
  pw_add two a (e4 d)

end LeanProofs.IPRA.Topology.CollisionScales
