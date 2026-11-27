import IPRADerivations.Foundations.BoundedDescent
import IPRADerivations.Foundations.BoundedFormulas

/-!
# Fixed points of an ascending bounded operator (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "Finite colimits by bounded
equivalence closure": "Its equivalence closure can be computed by finite reachability. ... The
finite reachability bound is essential."

The termination half of every such closure computation, separated from any particular
relation: a primitive recursive operator `T` on coded states with a measure `m` that is bounded
by `b` and strictly increases whenever `T` moves the state reaches a fixed point, and the number
of iterations is the term `b(s₀) ∸ m(s₀)`.

The data are unary terms `T`, `m`, `b` and a validity bit `V`. The hypotheses (`Ascent`) are
rules at arbitrary terms and contexts:

* `T` preserves validity;
* `m(s) ≤ b(s)` for valid `s`;
* `b(T(s)) = b(s)` for valid `s`;
* `V(s) = 1` and `T(s) ≠ s` give `m(s) < m(T(s))`.

Then (`descent`) the rank `b ∸ m` and the terminal test `[T(s) = s]` satisfy the hypotheses of
`thm:rank` (`Foundations/BoundedDescent`), and for a valid `s₀`:

* `fixpoint`: `T(T^r(s₀)) = T^r(s₀)` for `r = b(s₀) ∸ m(s₀)`;
* `fixpoint_succ`: `T^{r+1}(s₀) = T^r(s₀)`;
* `valid_iter`: every iterate is valid;
* `fixpoint_closed`: the closed sentence.

No order on states and no monotonicity of `T` is assumed: equality of codes is decidable, and
that is all the argument uses.

Instance with every hypothesis discharged (`saturate`): `T(s) = s + (1 ∸ s)` with measure
`sg s ≤ 1`; it moves only `0`, and `saturate_closed` is its fixed point statement.

Not derived: the instantiation to the transitive closure of a coded relation on `[N]` (the
packet's Warshall recurrence), which additionally needs the closure invariants.
-/

namespace LeanProofs.IPRA.Foundations.BoundedFixpoint

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.IterationFusion
open LeanProofs.IPRA.Foundations.BoundedDescent
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb one_ne_zero sg_cases)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The hypotheses: a bounded measure that strictly increases whenever the operator moves. -/
structure Ascent (T m b V : PTm 1) : Prop where
  pres : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] app1 V (app1 T s) ≐ one)
  bound : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] le (app1 m s) (app1 b s))
  stable : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] app1 b (app1 T s) ≐ app1 b s)
  asc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] neg (app1 T s ≐ s)) →
      (Γ ⊢[PRAAx] lt (app1 m s) (app1 m (app1 T s)))

/-- The rank `b(s) ∸ m(s)`. -/
def rk (m b : PTm 1) : PTm 1 := monus b m

/-- The fixed-point test `[T(s) = s]`. -/
def fx (T : PTm 1) : PTm 1 := eqb T (var 0)

theorem app1_rk (m b : PTm 1) (s : PTm k) :
    app1 (rk m b) s = monus (app1 b s) (app1 m s) := by simp [app1, rk]

theorem app1_fx (T : PTm 1) (s : PTm k) : app1 (fx T) s = eqb (app1 T s) s := by
  simp [app1, fx]

section Fix

variable {T m b V : PTm 1}

/-- An ascent is a descent of the rank `b ∸ m` with terminal test `[T(s) = s]`. -/
theorem descent (H : Ascent T m b V) : Descent T (rk m b) (fx T) V where
  pres := H.pres
  fix := fun _ hd => by
    rw [app1_fx] at hd
    exact eq_of_eqb hd
  dec := fun {k Γ s} hv hd => by
    rw [app1_fx] at hd
    rw [app1_rk, app1_rk]
    have hne : Γ ⊢[PRAAx] neg (app1 T s ≐ s) := .impI (.impE hd.wk (eqb_of_eq Prf.hyp0))
    refine le_of_eq_add (d := monus (app1 m (app1 T s)) (succ (app1 m s))) ?_
    ipra_lc natEq (eq_add_of_le (H.bound (H.pres hv))) - natEq (eq_add_of_le (H.bound hv)) +
      natEq (eq_add_of_le (H.asc hv hne)) - natEq (H.stable hv)

/-- Every iterate of a valid state is valid. -/
theorem valid_iter (H : Ascent T m b V) {s₀ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 V s₀ ≐ one)
    (t : PTm k) : Γ ⊢[PRAAx] app1 V (iter T t s₀) ≐ one :=
  Prf.andE₁ (descent_inv (descent H) h₀ t)

/-- The iterate `T^{b(s₀) ∸ m(s₀)}(s₀)` of a valid state is a fixed point of `T`. -/
theorem fixpoint (H : Ascent T m b V) {s₀ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 V s₀ ≐ one) :
    Γ ⊢[PRAAx] app1 T (iter T (monus (app1 b s₀) (app1 m s₀)) s₀) ≐
      iter T (monus (app1 b s₀) (app1 m s₀)) s₀ := by
  have t := terminal (descent H) h₀
  rw [app1_fx, app1_rk] at t
  exact eq_of_eqb t

/-- One more iteration does not move the state. -/
theorem fixpoint_succ (H : Ascent T m b V) {s₀ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 V s₀ ≐ one) :
    Γ ⊢[PRAAx] iter T (succ (monus (app1 b s₀) (app1 m s₀))) s₀ ≐
      iter T (monus (app1 b s₀) (app1 m s₀)) s₀ :=
  (iter_succ T _ s₀).eqTrans (fixpoint H h₀)

/-- The fixed point as a closed sentence. Variable: `0 = s₀`. -/
theorem fixpoint_closed (H : Ascent T m b V) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((app1 V (var 0) ≐ one) ⟶
      (app1 T (iter T (monus (app1 b (var 0)) (app1 m (var 0))) (var 0)) ≐
        iter T (monus (app1 b (var 0)) (app1 m (var 0))) (var 0))) :=
  closeUniv 1 (.impI (fixpoint H Prf.hyp0))

end Fix

/-! ## An instance: saturating at one -/

/-- `T(s) = s + (1 ∸ s)`: it sends `0` to `1` and fixes every positive `s`. -/
def upT : PTm 1 := var 0 + monus one (var 0)

/-- The measure `sg s`. -/
def sgT : PTm 1 := monus one (monus one (var 0))

theorem app1_upT (s : PTm k) : app1 upT s = s + monus one s := by simp [app1, upT]
theorem app1_sgT (s : PTm k) : app1 sgT s = sg s := by simp [app1, sgT]

/-- `T(s) = s + (1 ∸ s)` with measure `sg s ≤ 1` satisfies the hypotheses. -/
theorem saturate : Ascent upT sgT trueT trueT where
  pres := fun _ => by rw [app1_trueT]; exact .eqRefl _
  bound := fun {k Γ s} _ => by
    rw [app1_sgT, app1_trueT]
    exact .orE (sg_cases s) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le one))
      (le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl one))
  stable := fun _ => by rw [app1_trueT, app1_trueT]; exact .eqRefl _
  asc := fun {k Γ s} _ hne => by
    rw [app1_upT] at hne ⊢
    rw [app1_sgT, app1_sgT]
    refine .orE (zero_or_succ s) ?_ ?_
    · -- `s = 0`: the measure goes from `0` to `1`
      have hz : ((s ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero := Prf.hyp0
      have v : ((s ≐ zero) :: Γ) ⊢[PRAAx] s + monus one s ≐ succ zero :=
        (congrAdd hz ((congrMonus (.eqRefl _) hz).eqTrans (monus_zero _))).eqTrans
          ((add_comm _ _).eqTrans (add_zero _))
      exact lt_congr (sg_of_zero hz).eqSymm (sg_of_pos v).eqSymm (le_refl one)
    · -- `s ≥ 1`: the operator does not move `s`
      have hp : ((s ≐ succ (pred s)) :: Γ) ⊢[PRAAx] s ≐ succ (pred s) := Prf.hyp0
      have hle : ((s ≐ succ (pred s)) :: Γ) ⊢[PRAAx] le one s :=
        le_congr (.eqRefl _) hp.eqSymm
          (le_of_eq_add (d := pred s) (by ipra_ring))
      exact .botE _ (.impE hne.wk ((congrAdd (.eqRefl s) hle).eqTrans (add_zero s)))

/-- The saturating operator reaches its fixed point after `1 ∸ sg s₀` steps, as a closed
sentence with every hypothesis discharged. -/
theorem saturate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (app1 upT (iter upT (monus one (sg (var 0))) (var 0)) ≐
      iter upT (monus one (sg (var 0))) (var 0)) := by
  refine closeUniv 1 ?_
  have t := fixpoint (Γ := ([] : List (Fm PTm 1))) saturate (s₀ := var 0)
    (by rw [app1_trueT]; exact .eqRefl _)
  rw [app1_trueT, app1_sgT] at t
  exact t

end LeanProofs.IPRA.Foundations.BoundedFixpoint
