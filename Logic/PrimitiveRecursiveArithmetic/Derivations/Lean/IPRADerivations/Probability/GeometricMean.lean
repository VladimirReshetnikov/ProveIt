import IPRADerivations.Core.Powers
import IPRADerivations.Core.LinearCombination

/-!
# The finite identity behind the mean of the geometric distribution

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:geometric`: for `P(X = k) = p(1 − p)^{k−1}`,
`E[X] = 1/p`. "The finite polynomial identity `∑_{k=1}^N k q^{k−1} = (1 − (N+1)q^N + Nq^{N+1})/(1 − q)²` is proved
by multiplying the sum by `1 − q` twice and telescoping, with no differentiation needed."

For rational `q = u/v` with `v = u + w` (`p = w/v`), the scaled partial sum `S(N) = ∑_{k<N} (k+1) u^k v^{N−1−k}`
(so `∑_{k=1}^N k q^{k−1} = S(N)/v^{N−1}`) is defined by primitive recursion, `S(0) = 0`,
`S(N + 1) = v S(N) + (N + 1) u^N`, and the identity cleared of denominators reads, in natural numbers,

* `geometric_identity`: `w² S(N) + (N + 1) u^N v = v^{N+1} + N u^{N+1}`,

by quantifier-free induction on `N`. Multiplying by `p = w/v` gives the partial expectation
`p ∑ k q^{k−1} = (1 − (N+1)q^N + Nq^{N+1})/p`, which tends to `1/p`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.GeometricMean

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The step; variables `0 = N`, `1 = S(N)`, `2 = ⟨u, w⟩`. -/
abbrev sStep : PTm 3 := (fstT (var 2) + sndT (var 2)) * var 1 + succ (var 0) * pw (fstT (var 2)) (var 0)
abbrev sF : PR 2 := rec2 zero sStep
/-- `S(N)` for `q = u/(u + w)`. -/
abbrev gS (N u w : PTm n) : PTm n := ap2 sF N (pairT u w)

theorem gS_zero (u w : PTm n) : Γ ⊢[PRAAx] gS zero u w ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero sStep (pairT u w)

theorem gS_succ (N u w : PTm n) :
    Γ ⊢[PRAAx] gS (succ N) u w ≐ (u + w) * gS N u w + succ N * pw u N := by
  have h := rec2_succ (Γ := Γ) zero sStep N (pairT u w)
  simp only [PTm.subst_add, PTm.subst_mul, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    subst_fstT, subst_sndT] at h
  refine h.eqTrans ?_
  refine congrAdd (congrMul (congrAdd (fst_pair u w) (snd_pair u w)) (.eqRefl _))
    (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (fst_pair u w)))

/-- Variables: `0 = N` (induction), `1 = u`, `2 = w`. -/
private abbrev gF : Fm PTm 3 :=
  var 2 * var 2 * gS (var 0) (var 1) (var 2) + succ (var 0) * pw (var 1) (var 0) * (var 1 + var 2) ≐
    pw (var 1 + var 2) (succ (var 0)) + var 0 * pw (var 1) (succ (var 0))

theorem geo_base (u w : PTm n) :
    Γ ⊢[PRAAx] w * w * gS zero u w + succ zero * pw u zero * (u + w) ≐
      pw (u + w) (succ zero) + zero * pw u (succ zero) := by
  have e0 := natEq (gS_zero (Γ := Γ) u w)
  have p0 := natEq (pw_zero (Γ := Γ) u)
  have p1 := natEq (pw_succ (Γ := Γ) (u + w) zero)
  have p2 := natEq (pw_zero (Γ := Γ) (u + w))
  apply deriveNat; ipra_simps
  rw [e0, p0, p1, p2]; ring

theorem geo_step {N u w : PTm n}
    (ih : Γ ⊢[PRAAx] w * w * gS N u w + succ N * pw u N * (u + w) ≐ pw (u + w) (succ N) + N * pw u (succ N)) :
    Γ ⊢[PRAAx] w * w * gS (succ N) u w + succ (succ N) * pw u (succ N) * (u + w) ≐
      pw (u + w) (succ (succ N)) + succ N * pw u (succ (succ N)) := by
  ipra_lc (Groth.ι (Q.mk Γ w)) ^ 2 * natEq (gS_succ (Γ := Γ) N u w) -
    (Groth.ι (Q.mk Γ N) + 1) * natEq (pw_succ (Γ := Γ) u (succ N)) - natEq (pw_succ (Γ := Γ) (u + w) (succ N)) +
    (Groth.ι (Q.mk Γ u) + Groth.ι (Q.mk Γ w)) * natEq ih +
    (Groth.ι (Q.mk Γ N) * Groth.ι (Q.mk Γ u) + 2 * Groth.ι (Q.mk Γ N) * Groth.ι (Q.mk Γ w) + Groth.ι (Q.mk Γ u) + 2 * Groth.ι (Q.mk Γ w)) * natEq (pw_succ (Γ := Γ) u N)

private theorem g₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] gF := by
  refine ind _ trivial ?_ ?_
  · simp
    exact geo_base _ _
  · simp
    exact geo_step Prf.hyp0

/-- `prop:geometric`, the finite identity: `w² S(N) + (N + 1) u^N v = v^{N+1} + N u^{N+1}`, `v = u + w`. -/
theorem geometric_identity (N u w : PTm n) :
    Γ ⊢[PRAAx] w * w * gS N u w + succ N * pw u N * (u + w) ≐ pw (u + w) (succ N) + N * pw u (succ N) := by
  have h := inst (Γ := Γ) g₀ (![N, u, w] : Fin 3 → PTm n)
  simpa using h

end LeanProofs.IPRA.Probability.GeometricMean
