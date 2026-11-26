import IPRADerivations.Foundations.BoundedDescent
import IPRADerivations.Foundations.TraceClosure
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Finite descent with an explicit range, with a guarded step

Packet: `foundations/ipra_framework_2026-11-15`, `framework.tex`, Lemma "Finite descent with explicit range":
for PR `H(x) ∈ {0, 1}`, height `h(x)` and step `T(x)` with
`H(x) = 1 ∧ h(x) > 0 ⟹ H(T x) = 1 ∧ h(T x) < h(x)`, from `H(x) = 1` there is `y = T^{h(x)}(x)` with
`H(y) = 1` and `h(y) = 0`.

As stated, the lemma needs a repair: the height drops by *at least* one, so it can reach `0` before step
`h(x)`, and the remaining applications of `T` are at height-`0` states, where the hypothesis says nothing
(for `h(x) = x`, `H(x) = [x ≤ 2]`, `T(x) = 0` for `x > 0` and `T(0) = 5`, the hypothesis holds, but from
`x = 2` the iterate `T²(2) = T(0) = 5` has `H = 0` and `h = 5`). The proof's
invariant `h(x_t) ≤ h(x) − t` is only maintained while the height is positive. Two repairs, both derived:

* `gstep` (with `gstep_zero`, `gstep_pos`): the guarded step `T'(x) = T(x)` if `h(x) > 0`, `T'(x) = x` if
  `h(x) = 0` (the overlapping-branch `TraceClosure.branchStep` with the Boolean `[h(x) = 0]`, `zeroH`);
* `guarded_descent`: `T'` satisfies the hypotheses of `BoundedDescent.Descent` with rank `h`, terminal test
  `[h = 0]` and validity `H`;
* `explicit_range` (the lemma, repaired): `H(x) = 1` gives `H(y) = 1 ∧ h(y) = 0` for `y = T'^{h(x)}(x)`;
* `explicit_range_fix`: if moreover `T` fixes valid states of height `0`, the unguarded `y = T^{h(x)}(x)`
  works, as the packet states.

The descent hypothesis is `Hyp`, two rules over all contexts.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GuardedDescent

open_ipra
open LeanProofs.IPRA.Foundations.IterationFusion (app1 iter congrApp1)
open LeanProofs.IPRA.Foundations.BoundedDescent (Descent descent_inv terminal)
open LeanProofs.IPRA.Foundations.TraceClosure (branchStep app1_branchStep)
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The descent hypothesis: `H(x) = 1 ∧ h(x) > 0 ⟹ H(T x) = 1 ∧ h(T x) < h(x)`. -/
structure Hyp (T h V : PTm 1) : Prop where
  valid : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] lt zero (app1 h s)) → (Γ ⊢[PRAAx] app1 V (app1 T s) ≐ one)
  dec : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] lt zero (app1 h s)) →
      (Γ ⊢[PRAAx] lt (app1 h (app1 T s)) (app1 h s))

variable (T h V : PTm 1)

/-- The terminal test `[h(x) = 0]`. -/
def zeroH : PTm 1 := eqb h zero

/-- The guarded step: `x` at height `0`, `T(x)` otherwise. -/
def gstep : PTm 1 := branchStep (zeroH h) (Syn.var 0) T

theorem app1_zeroH (s : PTm k) : app1 (zeroH h) s = eqb (app1 h s) zero := by
  simp [app1, zeroH]

theorem app1_var0 (s : PTm k) : app1 (Syn.var 0) s = s := by simp [app1]

variable {T h V}

theorem gstep_zero {s : PTm k} (hz : Γ ⊢[PRAAx] app1 h s ≐ zero) : Γ ⊢[PRAAx] app1 (gstep T h) s ≐ s := by
  have hb : Γ ⊢[PRAAx] app1 (zeroH h) s ≐ one := by rw [app1_zeroH]; exact eqb_of_eq hz
  rw [gstep, app1_branchStep, app1_var0]
  exact (congrAdd ((congrMul hb (.eqRefl _)).eqTrans (one_mul _))
    ((congrMul ((congrMonus (.eqRefl _) hb).eqTrans (monus_self one)) (.eqRefl _)).eqTrans
      (zero_mul _))).eqTrans (add_zero _)

theorem gstep_pos {s : PTm k} (hp : Γ ⊢[PRAAx] lt zero (app1 h s)) :
    Γ ⊢[PRAAx] app1 (gstep T h) s ≐ app1 T s := by
  have hb : Γ ⊢[PRAAx] app1 (zeroH h) s ≐ zero := by rw [app1_zeroH]; exact eqb_zero_of_gt hp
  rw [gstep, app1_branchStep, app1_var0]
  exact (congrAdd ((congrMul hb (.eqRefl _)).eqTrans (zero_mul _))
    ((congrMul ((congrMonus (.eqRefl _) hb).eqTrans (monus_zero one)) (.eqRefl _)).eqTrans
      (one_mul _))).eqTrans (zero_add _)

theorem pos_of_succ {X : PTm k} (hx : Γ ⊢[PRAAx] X ≐ succ (pred X)) : Γ ⊢[PRAAx] lt zero X := by
  show Γ ⊢[PRAAx] le (succ zero) X
  have e := natEq hx
  ipra_le 𝔞 (pred X) using linear_combination e

/-- The guarded step satisfies the hypotheses of `BoundedDescent.Descent`. -/
theorem guarded_descent (H : Hyp T h V) : Descent (gstep T h) h (zeroH h) V where
  pres := fun {_} {Γ} {s} hv => by
    refine .orE (zero_or_succ (app1 h s)) ?_ ?_
    · exact (congrApp1 V (gstep_zero Prf.hyp0)).eqTrans hv.wk
    · have hp : ((app1 h s ≐ succ (pred (app1 h s))) :: Γ) ⊢[PRAAx] lt zero (app1 h s) := pos_of_succ Prf.hyp0
      exact (congrApp1 V (gstep_pos hp)).eqTrans (H.valid hv.wk hp)
  fix := fun hv hd => by
    rw [app1_zeroH] at hd
    exact gstep_zero (eq_of_eqb hd)
  dec := fun {_} {Γ} {s} hv hnd => by
    refine .orE (zero_or_succ (app1 h s)) ?_ ?_
    · have hz : ((app1 h s ≐ zero) :: Γ) ⊢[PRAAx] app1 (zeroH h) s ≐ one := by
        rw [app1_zeroH]; exact eqb_of_eq Prf.hyp0
      exact .botE _ (.impE hnd.wk hz)
    · have hp : ((app1 h s ≐ succ (pred (app1 h s))) :: Γ) ⊢[PRAAx] lt zero (app1 h s) := pos_of_succ Prf.hyp0
      exact lt_congr (congrApp1 h (gstep_pos hp)).eqSymm (.eqRefl _) (H.dec hv.wk hp)

/-- "Finite descent with explicit range", repaired: `y = T'^{h(x)}(x)` has `H(y) = 1` and `h(y) = 0`. -/
theorem explicit_range (H : Hyp T h V) {x : PTm k} (hx : Γ ⊢[PRAAx] app1 V x ≐ one) :
    Γ ⊢[PRAAx] (app1 V (iter (gstep T h) (app1 h x) x) ≐ one) ⋏
      (app1 h (iter (gstep T h) (app1 h x) x) ≐ zero) := by
  have t := terminal (guarded_descent H) hx
  rw [app1_zeroH] at t
  exact .andI (Prf.andE₁ (descent_inv (guarded_descent H) hx _)) (eq_of_eqb t)

/-- If `T` also fixes valid states of height `0`, the unguarded iterate `T^{h(x)}(x)` works. -/
theorem explicit_range_fix (H : Hyp T h V)
    (hfix : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
      (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] app1 h s ≐ zero) → (Γ ⊢[PRAAx] app1 T s ≐ s))
    {x : PTm k} (hx : Γ ⊢[PRAAx] app1 V x ≐ one) :
    Γ ⊢[PRAAx] (app1 V (iter T (app1 h x) x) ≐ one) ⋏ (app1 h (iter T (app1 h x) x) ≐ zero) := by
  have D : Descent T h (zeroH h) V :=
    { pres := fun {_} {Γ} {s} hv => by
        refine .orE (zero_or_succ (app1 h s)) ?_ ?_
        · exact (congrApp1 V (hfix hv.wk Prf.hyp0)).eqTrans hv.wk
        · exact H.valid hv.wk (pos_of_succ Prf.hyp0)
      fix := fun hv hd => by
        rw [app1_zeroH] at hd
        exact hfix hv (eq_of_eqb hd)
      dec := fun {_} {Γ} {s} hv hnd => by
        refine .orE (zero_or_succ (app1 h s)) ?_ ?_
        · have hz : ((app1 h s ≐ zero) :: Γ) ⊢[PRAAx] app1 (zeroH h) s ≐ one := by
            rw [app1_zeroH]; exact eqb_of_eq Prf.hyp0
          exact .botE _ (.impE hnd.wk hz)
        · exact H.dec hv.wk (pos_of_succ Prf.hyp0) }
  have t := terminal D hx
  rw [app1_zeroH] at t
  exact .andI (Prf.andE₁ (descent_inv D hx _)) (eq_of_eqb t)

end LeanProofs.IPRA.Foundations.GuardedDescent
