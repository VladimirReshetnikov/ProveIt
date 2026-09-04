import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Iterated derivatives of a solution of an autonomous equation

If `W' = φ ∘ W` on an open set, every higher derivative of `W` is again a
function of `W`: with `G₀ = id` and `G_{n+1} = G_n' · φ`,

`W^{(n)} = G_n ∘ W`.

The proof is the chain rule, `(G_n ∘ W)' = (G_n' ∘ W) · (φ ∘ W)`, applied on
the open set where the identity is already known at order `n`.  Nothing about
`W` is used except the equation, and nothing about `φ` except that the
`G_n` are differentiable with the stated derivatives, so the lemma is stated
with the family `G` and its derivatives `G'` as hypotheses.

This is the mechanism behind every "polynomial recurrence for all
derivatives" of an inverse function: for the Lambert function
`W' = e^{-W}/(1+W)`, and `G_n(w) = e^{-nw} P_n(w)/(1+w)^{2n-1}` with the
polynomials `P_n` obeying `P_{n+1} = (1+w)P_n' - (nw+3n-1)P_n`; for the inverse
Fabius function the same shape appears with the dilation equation in place of
the exponential.  The lemma isolates the part that does not depend on which.
-/

set_option autoImplicit false

open Filter Topology

namespace AutonomousODE

variable {W φ : ℝ → ℝ} {s : Set ℝ}

/-- **Iterated derivatives of a solution of `W' = φ(W)`.**  On an open set
`s` where `W` satisfies the equation, if each `G n` is differentiable at the
values of `W` with derivative `G' n`, and along those values `G 0` is the
identity and `G (n+1) = G' n · φ`, then `iteratedDeriv n W = G n ∘ W` on
`s`.  The hypotheses on `G` are asked only on the range of `W` over `s`,
because that is the only place the chain rule ever evaluates them; for the
Lambert function this is what lets the recurrence step assume `w ≠ -1`. -/
theorem iteratedDeriv_eq_comp (hs : IsOpen s)
    (hW : ∀ x ∈ s, HasDerivAt W (φ (W x)) x)
    (G G' : ℕ → ℝ → ℝ)
    (hG0 : ∀ x ∈ s, G 0 (W x) = W x)
    (hGd : ∀ n, ∀ x ∈ s, HasDerivAt (G n) (G' n (W x)) (W x))
    (hGs : ∀ n, ∀ x ∈ s, G (n + 1) (W x) = G' n (W x) * φ (W x)) :
    ∀ n, ∀ x ∈ s, iteratedDeriv n W x = G n (W x) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [iteratedDeriv_zero, hG0 x hx]
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    -- on the open set `s` the order-`n` identity holds near `x`
    have heq : iteratedDeriv n W =ᶠ[𝓝 x] G n ∘ W :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) fun y hy => ih y hy
    rw [heq.deriv_eq]
    have hcomp : HasDerivAt (G n ∘ W) (G' n (W x) * φ (W x)) x :=
      (hGd n x hx).comp x (hW x hx)
    rw [hcomp.deriv, hGs n x hx]

/-- The same statement with the derivative family read off pointwise: when
each `G n` is differentiable everywhere, `G' n = deriv (G n)`, `G 0 = id`,
and the recurrence `G (n+1) = deriv (G n) · φ` holds everywhere. -/
theorem iteratedDeriv_eq_comp_of_differentiable (hs : IsOpen s)
    (hW : ∀ x ∈ s, HasDerivAt W (φ (W x)) x)
    (G : ℕ → ℝ → ℝ)
    (hG0 : ∀ w, G 0 w = w)
    (hGd : ∀ n, Differentiable ℝ (G n))
    (hGs : ∀ n w, G (n + 1) w = deriv (G n) w * φ w) :
    ∀ n, ∀ x ∈ s, iteratedDeriv n W x = G n (W x) :=
  iteratedDeriv_eq_comp hs hW G (fun n => deriv (G n)) (fun x _ => hG0 (W x))
    (fun n x _ => (hGd n (W x)).hasDerivAt) (fun n x _ => hGs n (W x))

end AutonomousODE
