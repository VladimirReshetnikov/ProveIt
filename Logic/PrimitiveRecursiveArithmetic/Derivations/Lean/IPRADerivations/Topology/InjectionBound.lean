import IPRADerivations.DiophantineNumberTheory.MinkowskiPigeonhole
import IPRADerivations.Foundations.GapRecovery

/-!
# An injection of `d` indices into `m` values gives `d ≤ m` (`dimension_invariance_ipra`)

Packet: `topology/dimension_invariance_ipra`, the finite pigeonhole step at the end of
"A full simplex forces separated thresholds" and the search for a repeated coordinate in
"Extracting the positive alternative". There the map is `i ↦ j_i`, from the `d` source
directions to the `m` target coordinates.

For a binary primitive recursive symbol `f(i, x)` with a runtime parameter `x`; the numbers
`d`, `m` and `x` are variables of the object theory.

* `collision`: if `m < d` and `f(i, x) < m` for every `i < d`, then the explicit indices
  `i₀ = first f m x`, `j₀ = second f m x` satisfy `i₀ < j₀ < d` and `f(i₀, x) = f(j₀, x)`. This
  is the bounded search for the first repeated coordinate; the indices are the actual bounded
  pair search of `MinkowskiPigeonhole`, applied to the prefix `0, …, m`.
* `injection_bound`: if `f(i, x) < m` for every `i < d` and `f(i, x) ≠ f(j, x)` for all
  `i < j < d`, then `d ≤ m`.

The count argument of the packet (`c_j ≤ 1` for the fibre counts, whose total is the number of
indices) is the proof of `Core/Pigeonhole`, on which the pair search rests.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.InjectionBound

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiPigeonhole (prefixRange first second
  bounded_collision subst_first subst_second)
open LeanProofs.IPRA.Foundations.GapRecovery (subst_sh2')

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (f : PR 2)

/-- `∀ i < d. f(i, x) < m`. -/
abbrev rangeBelow (d m x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift d) ⟶ lt (ap2 f (var 0) (Syn.shift x)) (Syn.shift m))

/-- `∀ i j. i < j → j < d → f(i, x) ≠ f(j, x)`. -/
abbrev injBelow (d x : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (lt (var 1) (var 0) ⟶ (lt (var 0) (Syn.shift (Syn.shift d)) ⟶
    neg (ap2 f (var 1) (Syn.shift (Syn.shift x)) ≐ ap2 f (var 0) (Syn.shift (Syn.shift x))))))

theorem range_at {d m x i : PTm n} (h : Γ ⊢[PRAAx] rangeBelow f d m x) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] lt (ap2 f i x) m := by
  have a : Γ ⊢[PRAAx] lt i d ⟶ lt (ap2 f i x) m := by
    simpa only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift] using Prf.allE i h
  exact .impE a hi

theorem inj_at {d x : PTm n} (h : Γ ⊢[PRAAx] injBelow f d x) (i j : PTm n) :
    Γ ⊢[PRAAx] lt i j ⟶ (lt j d ⟶ neg (ap2 f i x ≐ ap2 f j x)) := by
  have a := Prf.allE j (Prf.allE i h)
  simpa [subst_sh2', subst_ap2] using a

theorem shift_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) :
    Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_lt h

/-- More indices than values: the pair search over the prefix `0, …, m` returns a collision
below `d`. -/
theorem collision {d m x : PTm n} (hmd : Γ ⊢[PRAAx] lt m d) (hr : Γ ⊢[PRAAx] rangeBelow f d m x) :
    Γ ⊢[PRAAx] lt (first f m x) (second f m x) ⋏
      (lt (second f m x) d ⋏ (ap2 f (first f m x) x ≐ ap2 f (second f m x) x)) := by
  have hm : Γ ⊢[PRAAx] le one m := by
    refine .orE (zero_or_succ m) ?_ ?_
    · have h0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] lt zero d := lt_of_le_of_lt (zero_le m) hmd.wk
      have r := range_at f hr.wk h0
      exact lt_zero_absurd _ (lt_congr (.eqRefl _) Prf.hyp0 r)
    · exact Order.zero_lt_of_eq_succ Prf.hyp0
  have hp : Γ ⊢[PRAAx] prefixRange f m x := by
    refine .allI (.impI ?_)
    have ho := hr.allOpen
    exact .impE ho.wk (lt_of_le_of_lt Prf.hyp0 (shift_lt hmd).wk)
  have c := bounded_collision f m x hm hp
  exact .andI (.andE₁ c) (.andI (lt_of_le_of_lt (.andE₁ (.andE₂ c)) hmd) (.andE₂ (.andE₂ c)))

/-- An injection of the indices below `d` into the values below `m` gives `d ≤ m`. -/
theorem injection_bound {d m x : PTm n} (hr : Γ ⊢[PRAAx] rangeBelow f d m x)
    (hi : Γ ⊢[PRAAx] injBelow f d x) : Γ ⊢[PRAAx] le d m := by
  refine .orE (lt_or_le m d) ?_ Prf.hyp0
  have c := collision f (Γ := lt m d :: Γ) Prf.hyp0 hr.wk
  have h := inj_at f (Γ := lt m d :: Γ) hi.wk (first f m x) (second f m x)
  exact .botE _ (.impE (.impE (.impE h (.andE₁ c)) (.andE₁ (.andE₂ c))) (.andE₂ (.andE₂ c)))

/-! ## Closed forms -/

/-- Variables: `0 = d`, `1 = m`, `2 = x`. -/
abbrev collisionFormula : Fm PTm 3 :=
  lt (var 1) (var 0) ⟶ rangeBelow f (var 0) (var 1) (var 2) ⟶
    (lt (first f (var 1) (var 2)) (second f (var 1) (var 2)) ⋏
      (lt (second f (var 1) (var 2)) (var 0) ⋏
        (ap2 f (first f (var 1) (var 2)) (var 2) ≐ ap2 f (second f (var 1) (var 2)) (var 2))))

/-- The first repeated coordinate: for all `d`, `m`, `x` with `m < d` and `f(i, x) < m` for
every `i < d`, the pair search returns `i₀ < j₀ < d` with `f(i₀, x) = f(j₀, x)`. -/
theorem collision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (collisionFormula f) :=
  closeUniv 3 (.impI (.impI (collision f Prf.hyp1 Prf.hyp0)))

/-- Variables: `0 = d`, `1 = m`, `2 = x`. -/
abbrev boundFormula : Fm PTm 3 :=
  rangeBelow f (var 0) (var 1) (var 2) ⟶ injBelow f (var 0) (var 2) ⟶ le (var 0) (var 1)

/-- The pigeonhole step of the dimension obstruction: for all `d`, `m`, `x`, an injection
`i ↦ f(i, x)` of the indices below `d` into the values below `m` gives `d ≤ m`. -/
theorem injection_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (boundFormula f) :=
  closeUniv 3 (.impI (.impI (injection_bound f Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Topology.InjectionBound
