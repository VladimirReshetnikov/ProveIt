import IPRADerivations.Foundations.TriangularUniqueness
import IPRADerivations.Core.Header

/-!
# The Hurwitz examples determine their solutions (`ipra_coherent_methods_2026-11-15`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, the examples after (10) of
`thm:hurwitz-ode`: "Taking `A_j = 1` gives the Bell recurrence, while `Y' = Y ⋆ Y`, `Y_0 = 1`,
gives `Y_n = n!`". `Foundations/HurwitzProduct` shows that the Bell numbers and the
factorials satisfy these systems; here the systems are shown to have no other solutions, by
`Foundations/TriangularUniqueness`.

* `hw_congr₂`: `(a ⋆ b)_n` reads both factors only up to index `n`;
* `square_unique`: if iPRA derives `y(0, x) = 1` and `y(n + 1, x) = (y ⋆ y)_n` for a term `y`,
  then it derives `y(n, x) = n!`;
* `bell_unique`: if iPRA derives `y(0, x) = 1` and `y(n + 1, x) = (1 ⋆ y)_n`, then it derives
  `y(n, x) = B_n`.

In both cases the solution is produced without dividing by a factorial, and uniqueness is the
packet's bounded-prefix induction.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HurwitzUniqueness

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_zero)
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB)
open LeanProofs.IPRA.Foundations.HurwitzProduct
open LeanProofs.IPRA.Foundations.TriangularUniqueness

variable {k : ℕ} {Γ : List (Fm PTm k)}

section Congr

variable (a b a' b' : PTm 2)

/-- The summands of `(a ⋆ b)_n` and `(a' ⋆ b')_n` agree when the factors agree up to `n`. -/
theorem hw_pt {j n x : PTm k} (ha : Γ ⊢[PRAAx] agree a a' (succ n) x)
    (hb : Γ ⊢[PRAAx] agree b b' (succ n) x) (hj : Γ ⊢[PRAAx] lt j (succ n)) :
    Γ ⊢[PRAAx] inst2 (bgB (cv a b)) j (pairT n (pairT n x)) ≐
      inst2 (bgB (cv a' b')) j (pairT n (pairT n x)) := by
  have hl : Γ ⊢[PRAAx] lt (monus n j) (succ n) :=
    (succ_monus_succ (monus n j) n).eqTrans (monus_le' n j)
  refine (term_at a b j n n x).eqTrans (.eqTrans ?_ (term_at a' b' j n n x).eqSymm)
  exact congrMul (.eqRefl _) (congrMul (agree_elim a a' ha hj) (agree_elim b b' hb hl))

/-- `(a ⋆ b)_n` reads both factors only up to index `n`. -/
theorem hw_congr₂ {n x : PTm k} (ha : Γ ⊢[PRAAx] agree a a' (succ n) x)
    (hb : Γ ⊢[PRAAx] agree b b' (succ n) x) : Γ ⊢[PRAAx] hw a b n x ≐ hw a' b' n x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT]
  have e : Syn.shift (succ n) = succ (Syn.shift n) := by simp [Syn.shift]
  have ha' := ha.shift
  rw [shift_agree, e] at ha'
  have hb' := hb.shift
  rw [shift_agree, e] at hb'
  have hj : (lt (var 0) (Syn.shift (succ n)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (succ (Syn.shift n)) :=
    (congrArg (fun t => (lt (var 0) (Syn.shift (succ n)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) t) e).mp Prf.hyp0
  exact hw_pt a b a' b' ha'.wk hb'.wk hj

end Congr

/-! ## `Y' = Y ⋆ Y` -/

/-- If `y(0) = 1` and `y(n + 1) = (y ⋆ y)_n`, then `y(n) = n!`. -/
theorem square_unique {y : PTm 2}
    (h₀ : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] inst2 y zero x ≐ one)
    (hy : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
      Γ ⊢[PRAAx] inst2 y (succ n) x ≐ hw y y n x)
    (n x : PTm k) : Γ ⊢[PRAAx] inst2 y n x ≐ fact n := by
  have u := unique (Γ := Γ) (y := y) (y' := factB) (F := hwB y y) (F' := hwB factB factB)
    { init := fun x => by rw [inst2_factB]; exact (h₀ x).eqTrans (fact_zero zero).eqSymm
      step := fun n x => by rw [inst2_hwB]; exact hy n x
      step' := fun n x => by rw [inst2_factB, inst2_hwB]; exact (hw_fact n x).eqSymm
      tri := fun h => by rw [inst2_hwB, inst2_hwB]; exact hw_congr₂ y y factB factB h h } n x
  rw [inst2_factB] at u
  exact u

/-! ## `Y' = A ⋆ Y` with `A_j = 1` -/

/-- If `y(0) = 1` and `y(n + 1) = (1 ⋆ y)_n`, then `y(n) = B_n`. -/
theorem bell_unique {y : PTm 2}
    (h₀ : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] inst2 y zero x ≐ one)
    (hy : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
      Γ ⊢[PRAAx] inst2 y (succ n) x ≐ hw oneB y n x)
    (n x : PTm k) : Γ ⊢[PRAAx] inst2 y n x ≐ bell n := by
  have u := hurwitz_linear_unique (Γ := Γ) (A := oneB) (y := y) (y' := bellB)
    (fun x => by rw [inst2_bellB]; exact (h₀ x).eqTrans bell_zero.eqSymm) hy
    (fun n x => by rw [inst2_bellB]; exact (hw_one_bell n x).eqSymm) n x
  rw [inst2_bellB] at u
  exact u

end LeanProofs.IPRA.Foundations.HurwitzUniqueness
