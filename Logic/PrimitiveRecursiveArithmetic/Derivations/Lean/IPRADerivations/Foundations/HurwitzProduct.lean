import IPRADerivations.Combinatorics.BinomialTransform

/-!
# The Hurwitz product and its derivation (`ipra_coherent_methods_2026-11-15`, (6), (7))

Packet: `foundations/ipra_coherent_methods_2026-11-15`, Section 4, the Hurwitz (divided-power)
algebra used in `thm:hurwitz-ode`: the product (6)

`(a ⋆ b)_n = ∑_{j ≤ n} C(n, j) a_j b_{n−j}`

and the typed Leibniz identity after (7), with `(D a)_n = a_{n+1}`:

`(D (a ⋆ b))_n = (D a ⋆ b)_n + (a ⋆ D b)_n`.

Sequences are arbitrary terms `a(j, x)`, `b(j, x)` (variables `0 = j`, `1 = x`), so the
identities hold for all coefficient sequences presented in iPRA, with no factorial
denominators.

* `hw a b n x`: the coefficient `(a ⋆ b)_n`; `hw_zero`: `(a ⋆ b)_0 = a_0 b_0`;
* `leibniz`: `(a ⋆ b)_{n+1} = (D a ⋆ b)_n + (a ⋆ D b)_n`, closed form `leibniz_closed`.

The proof is the Pascal step for binomial-weighted sums (`pascal_sum` of
`Combinatorics/BinomialTransform`) applied to the summand `a_j b_{N−j}` with `N = n + 1`
fixed, followed by two reindexings: `(n + 1) ∸ (j + 1) = n ∸ j`, and
`(n + 1) ∸ j = (n ∸ j) + 1` for `j ≤ n`. The demand for one extra coefficient of each
factor is visible in the statement: the right-hand side reads `a` and `b` up to index `n + 1`.

Not derived: associativity and commutativity of `⋆`, the recurrence (9) for a polynomial
system and `thm:hurwitz-ode` itself.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HurwitzProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB inst2_bg inst2_bgs pascal_sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(n + 1) ∸ j = (n ∸ j) + 1` for `j ≤ n`. -/
theorem succ_monus_of_le {j n : PTm k} (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] monus (succ n) j ≐ succ (monus n j) := by
  have e₁ := natEq (eq_add_of_le h)
  have e₂ := natEq (eq_add_of_le (le_trans h (le_succ_self n)))
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂

section Product

variable (a b : PTm 2)

/-- The summand `a_j b_{N ∸ j}`; variables `0 = j`, `1 = ⟨N, x⟩`. -/
def cv : PTm 2 :=
  inst2 a (var 0) (sndT (var 1)) * inst2 b (monus (fstT (var 1)) (var 0)) (sndT (var 1))

theorem cv_at (j N x : PTm k) :
    Γ ⊢[PRAAx] inst2 (cv a b) j (pairT N x) ≐ inst2 a j x * inst2 b (monus N j) x := by
  have e : inst2 (cv a b) j (pairT N x) =
      inst2 a j (sndT (pairT N x)) * inst2 b (monus (fstT (pairT N x)) j) (sndT (pairT N x)) := by
    show Syn.subst ![j, pairT N x] (cv a b) = _
    simp [cv]
  rw [e]
  exact congrMul (congrInst2 a (.eqRefl _) (snd_pair _ _))
    (congrInst2 b (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- The coefficient `(a ⋆ b)_n = ∑_{j ≤ n} C(n, j) a_j b_{n ∸ j}`. -/
abbrev hw (n x : PTm k) : PTm k := ap2 (sumF (bgB (cv a b))) (succ n) (pairT n (pairT n x))

/-- A summand of the binomial-weighted sum, evaluated. -/
theorem term_at (j n N x : PTm k) :
    Γ ⊢[PRAAx] inst2 (bgB (cv a b)) j (pairT n (pairT N x)) ≐
      binom n j * (inst2 a j x * inst2 b (monus N j) x) := by
  rw [inst2_bg]
  exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _))
    ((congrInst2 (cv a b) (.eqRefl _) (snd_pair _ _)).eqTrans (cv_at a b j N x))

/-- A summand of the shifted sum, evaluated. -/
theorem shift_term_at (j n N x : PTm k) :
    Γ ⊢[PRAAx] inst2 (bgB (shiftBody (cv a b))) j (pairT n (pairT N x)) ≐
      binom n j * (inst2 a (succ j) x * inst2 b (monus N (succ j)) x) := by
  rw [inst2_bgs]
  exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _))
    ((congrInst2 (cv a b) (.eqRefl _) (snd_pair _ _)).eqTrans (cv_at a b (succ j) N x))

/-- `(a ⋆ b)_0 = a_0 b_0`. -/
theorem hw_zero (x : PTm k) :
    Γ ⊢[PRAAx] hw a b zero x ≐ inst2 a zero x * inst2 b zero x := by
  have s := natEq (sum_succ' (Γ := Γ) (bgB (cv a b)) zero (pairT zero (pairT zero x)))
  have z := natEq (sum_zero (Γ := Γ) (bgB (cv a b)) (pairT zero (pairT zero x)))
  have t := natEq (term_at (Γ := Γ) a b zero zero zero x)
  have c := natEq (binom_zero' (Γ := Γ) (zero : PTm k))
  have m := natEq (congrInst2 (Γ := Γ) b (monus_zero (zero : PTm k)) (.eqRefl x))
  apply deriveNat; ipra_simps
  linear_combination s + z + t +
    𝔞 (inst2 a zero x) * 𝔞 (inst2 b (monus zero zero) x) * c + 𝔞 (inst2 a zero x) * m

/-- The first sum after the Pascal step is `(a ⋆ D b)_n`: `(n + 1) ∸ j = (n ∸ j) + 1`. -/
theorem first_pt {j n x : PTm k} (h : Γ ⊢[PRAAx] lt j (succ n)) :
    Γ ⊢[PRAAx] inst2 (bgB (cv a b)) j (pairT n (pairT (succ n) x)) ≐
      inst2 (bgB (cv a (shiftBody b))) j (pairT n (pairT n x)) := by
  have hle : Γ ⊢[PRAAx] le j n := (succ_monus_succ j n).eqSymm.eqTrans h
  have r := term_at (Γ := Γ) a (shiftBody b) j n n x
  rw [inst2_shiftBody] at r
  refine (term_at a b j n (succ n) x).eqTrans (.eqTrans ?_ r.eqSymm)
  exact congrMul (.eqRefl _)
    (congrMul (.eqRefl _) (congrInst2 b (succ_monus_of_le hle) (.eqRefl _)))

/-- The second sum after the Pascal step is `(D a ⋆ b)_n`: `(n + 1) ∸ (j + 1) = n ∸ j`. -/
theorem second_pt (j n x : PTm k) :
    Γ ⊢[PRAAx] inst2 (bgB (shiftBody (cv a b))) j (pairT n (pairT (succ n) x)) ≐
      inst2 (bgB (cv (shiftBody a) b)) j (pairT n (pairT n x)) := by
  have r := term_at (Γ := Γ) (shiftBody a) b j n n x
  rw [inst2_shiftBody] at r
  refine (shift_term_at a b j n (succ n) x).eqTrans (.eqTrans ?_ r.eqSymm)
  exact congrMul (.eqRefl _)
    (congrMul (.eqRefl _) (congrInst2 b (succ_monus_succ n j) (.eqRefl _)))

/-- The Leibniz rule of the Hurwitz product:
`(a ⋆ b)_{n+1} = (D a ⋆ b)_n + (a ⋆ D b)_n`. -/
theorem leibniz (n x : PTm k) :
    Γ ⊢[PRAAx] hw a b (succ n) x ≐ hw (shiftBody a) b n x + hw a (shiftBody b) n x := by
  have p := natEq (pascal_sum (Γ := Γ) (cv a b) n (pairT (succ n) x))
  have c₁' : Γ ⊢[PRAAx] ap2 (sumF (bgB (cv a b))) (succ n) (pairT n (pairT (succ n) x)) ≐
      ap2 (sumF (bgB (cv a (shiftBody b)))) (succ n) (pairT n (pairT n x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
    exact first_pt a b Prf.hyp0
  have c₂' : Γ ⊢[PRAAx]
      ap2 (sumF (bgB (shiftBody (cv a b)))) (succ n) (pairT n (pairT (succ n) x)) ≐
      ap2 (sumF (bgB (cv (shiftBody a) b))) (succ n) (pairT n (pairT n x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
    exact second_pt a b _ _ _
  have c₁ := natEq c₁'
  have c₂ := natEq c₂'
  apply deriveNat; ipra_simps
  linear_combination p + c₁ + c₂

/-- The Leibniz rule as a closed sentence, for all coefficient terms `a`, `b`. Variables:
`0 = n`, `1 = x`. -/
theorem leibniz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (hw a b (succ (var 0)) (var 1) ≐
      hw (shiftBody a) b (var 0) (var 1) + hw a (shiftBody b) (var 0) (var 1)) :=
  closeUniv 2 (leibniz a b _ _)

end Product

end LeanProofs.IPRA.Foundations.HurwitzProduct
