import IPRADerivations.Combinatorics.BinomialTransform
import IPRADerivations.Probability.Variance
import IPRADerivations.Combinatorics.Bell

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

* `hw_fact`: for `Y_j = j!`, `(Y ⋆ Y)_n = (n + 1)! = Y_{n+1}`: the factorials solve
  `Y' = Y ⋆ Y`, `Y_0 = 1` (the packet's example after (10)); every summand
  `C(n, j) j! (n − j)!` is `n!` (`fact_pt`).

* `hw_comm`: `(a ⋆ b)_n = (b ⋆ a)_n`, by reflecting the sum (`sum_reflect`) and
  `C(n, n − j) = C(n, j)` (`binom_symm_of_le`); closed form `hw_comm_closed`.

* `hw_one_bell`: `(1 ⋆ B)_n = B_{n+1}` for the Bell numbers `B`: they solve `Y' = A ⋆ Y` with
  `A_j = 1`, `Y_0 = 1` (the packet's first example after (10)), from the Bell recurrence of
  `Combinatorics/Bell` and commutativity.

Not derived: associativity of `⋆`, the recurrence (9) for a polynomial
system and `thm:hurwitz-ode` itself.
-/

namespace LeanProofs.IPRA.Foundations.HurwitzProduct

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB inst2_bg inst2_bgs pascal_sum)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `(n + 1) ∸ j = (n ∸ j) + 1` for `j ≤ n`. -/
theorem succ_monus_of_le {j n : PTm k} (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] monus (succ n) j ≐ succ (monus n j) :=
  Common.monus_succ_of_le h

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
  ipra_lc natEq (sum_succ' (bgB (cv a b)) zero (pairT zero (pairT zero x))) +
    natEq (sum_zero (bgB (cv a b)) (pairT zero (pairT zero x))) + natEq (term_at a b zero zero zero x) +
    𝔞 (inst2 a zero x) * 𝔞 (inst2 b (monus zero zero) x) * natEq (binom_zero' (zero : PTm k)) + 𝔞 (inst2 a zero x) *
    natEq (congrInst2 b (monus_zero (zero : PTm k)) (.eqRefl x))

/-- The first sum after the Pascal step is `(a ⋆ D b)_n`: `(n + 1) ∸ j = (n ∸ j) + 1`. -/
theorem first_pt {j n x : PTm k} (h : Γ ⊢[PRAAx] lt j (succ n)) :
    Γ ⊢[PRAAx] inst2 (bgB (cv a b)) j (pairT n (pairT (succ n) x)) ≐
      inst2 (bgB (cv a (shiftBody b))) j (pairT n (pairT n x)) := by
  have hle : Γ ⊢[PRAAx] le j n := Order.le_of_lt_succ h
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
  ipra_lc p + c₁ + natEq c₂'

/-- The Leibniz rule as a closed sentence, for all coefficient terms `a`, `b`. Variables:
`0 = n`, `1 = x`. -/
theorem leibniz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (hw a b (succ (var 0)) (var 1) ≐
      hw (shiftBody a) b (var 0) (var 1) + hw a (shiftBody b) (var 0) (var 1)) :=
  closeUniv 2 (leibniz a b _ _)

end Product

/-! ## Commutativity -/

section Commutativity

open LeanProofs.IPRA.Analysis.Products (fact)

/-- `n ∸ (n ∸ j) = j` for `j ≤ n`. -/
theorem monus_monus_of_le {j n : PTm k} (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] monus n (monus n j) ≐ j :=
  Common.monus_monus_of_le h

/-- `C(n, n ∸ j) = C(n, j)` for `j ≤ n`. -/
theorem binom_symm_of_le {j n : PTm k} (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] binom n (monus n j) ≐ binom n j :=
  congrAp2 quoF (.eqRefl _)
    ((congrMul (.eqRefl _) (congrAp2 factF (monus_monus_of_le h) (.eqRefl _))).eqTrans
      (mul_comm _ _))

variable (a b : PTm 2)

/-- The reflected summand of `(a ⋆ b)_n` at `j` is the summand of `(b ⋆ a)_n` at `j`. -/
theorem comm_pt {j n x : PTm k} (h : Γ ⊢[PRAAx] lt j (succ n)) :
    Γ ⊢[PRAAx] inst2 (rflBody (bgB (cv a b))) j (pairT (succ n) (pairT n (pairT n x))) ≐
      inst2 (bgB (cv b a)) j (pairT n (pairT n x)) := by
  have hle : Γ ⊢[PRAAx] le j n := Order.le_of_lt_succ h
  rw [inst2_rflBody]
  -- the reflected index is `n ∸ j`
  have i₁ : Γ ⊢[PRAAx]
      monus (fstT (pairT (succ n) (pairT n (pairT n x)))) (succ j) ≐ monus n j :=
    (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ n j)
  have c₁ := (congrInst2 (bgB (cv a b)) i₁ (snd_pair (succ n) (pairT n (pairT n x)))).eqTrans
    (term_at (Γ := Γ) a b (monus n j) n n x)
  ipra_lc natEq c₁ - natEq (term_at b a j n n x) +
    𝔞 (inst2 a (monus n j) x) * 𝔞 (inst2 b (monus n (monus n j)) x) * natEq (binom_symm_of_le hle) +
    𝔞 (binom n j) * 𝔞 (inst2 a (monus n j) x) * natEq (congrInst2 b (monus_monus_of_le hle) (.eqRefl x))

/-- The Hurwitz product is commutative: `(a ⋆ b)_n = (b ⋆ a)_n`. -/
theorem hw_comm (n x : PTm k) : Γ ⊢[PRAAx] hw a b n x ≐ hw b a n x := by
  refine (sum_reflect (bgB (cv a b)) (succ n) (pairT n (pairT n x))).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
  exact comm_pt a b Prf.hyp0

/-- Commutativity as a closed sentence, for all coefficient terms. Variables: `0 = n`,
`1 = x`. -/
theorem hw_comm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (hw a b (var 0) (var 1) ≐ hw b a (var 0) (var 1)) :=
  closeUniv 2 (hw_comm a b _ _)

end Commutativity

/-! ## The solution of `Y' = Y ⋆ Y`, `Y_0 = 1` -/

section Factorial

open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)

/-- The sequence `j ↦ j!`. -/
def factB : PTm 2 := fact (var 0)

theorem inst2_factB (j x : PTm k) : inst2 factB j x = fact j := by simp [inst2, factB]

/-- Every summand of `(Y ⋆ Y)_n` for `Y_j = j!` is `n!`: `C(n, j) j! (n − j)! = n!`. -/
theorem fact_pt {j n x : PTm k} (h : Γ ⊢[PRAAx] lt j (succ n)) :
    Γ ⊢[PRAAx] inst2 (bgB (cv factB factB)) j (pairT n (pairT n x)) ≐ fact n := by
  have hle : Γ ⊢[PRAAx] le j n := Order.le_of_lt_succ h
  have t := term_at (Γ := Γ) factB factB j n n x
  rw [inst2_factB, inst2_factB] at t
  exact t.eqTrans ((mul_comm _ _).eqTrans (binom_eq hle).eqSymm)

/-- `(Y ⋆ Y)_n = (n + 1)!` for `Y_j = j!`: the factorials solve `Y' = Y ⋆ Y`, `Y_0 = 1`,
since `Y_{n+1} = (n + 1)!`. No division by a factorial occurs. -/
theorem hw_fact (n x : PTm k) : Γ ⊢[PRAAx] hw factB factB n x ≐ fact (succ n) := by
  have c : Γ ⊢[PRAAx] hw factB factB n x ≐ succ n * fact n := by
    refine sum_const_of _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, subst_ap2, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    exact fact_pt Prf.hyp0
  exact c.eqTrans ((mul_comm _ _).eqTrans (fact_succ n zero).eqSymm)

/-- `∑_{j ≤ n} C(n, j) j! (n − j)! = (n + 1)!` as a closed sentence. Variables: `0 = n`,
`1 = x`. -/
theorem hw_fact_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (hw factB factB (var 0) (var 1) ≐ fact (succ (var 0))) :=
  closeUniv 2 (hw_fact _ _)

end Factorial

/-! ## The Bell numbers solve `Y' = A ⋆ Y` with `A_j = 1` -/

section BellNumbers

open LeanProofs.IPRA.Combinatorics.Bell (bell bell_succ recB inst2_rec)

/-- The sequence `j ↦ B_j` of Bell numbers. -/
def bellB : PTm 2 := bell (var 0)

/-- The constant sequence `1`. -/
def oneB : PTm 2 := one

theorem inst2_bellB (j x : PTm k) : inst2 bellB j x = bell j := by simp [inst2, bellB]

theorem inst2_oneB (j x : PTm k) : inst2 oneB j x = one := by simp [inst2, oneB]

/-- A summand of `(B ⋆ 1)_n` is the summand `C(n, j) B_j` of the Bell recurrence. -/
theorem bell_pt (j n x : PTm k) :
    Γ ⊢[PRAAx] inst2 (bgB (cv bellB oneB)) j (pairT n (pairT n x)) ≐ inst2 recB j n := by
  have t := term_at (Γ := Γ) bellB oneB j n n x
  rw [inst2_bellB, inst2_oneB] at t
  rw [inst2_rec]
  refine t.eqTrans (congrMul (.eqRefl _) ?_)
  exact (mul_comm _ _).eqTrans (one_mul _)

/-- `(B ⋆ 1)_n = ∑_{j ≤ n} C(n, j) B_j = B_{n+1}`. -/
theorem hw_bell_one (n x : PTm k) : Γ ⊢[PRAAx] hw bellB oneB n x ≐ bell (succ n) := by
  refine .eqTrans ?_ (bell_succ n).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT]
  exact bell_pt _ _ _

/-- `(1 ⋆ B)_n = B_{n+1}`: the Bell numbers satisfy `Y' = A ⋆ Y` with `A_j = 1` and
`Y_0 = 1`, the packet's example after (10). -/
theorem hw_one_bell (n x : PTm k) : Γ ⊢[PRAAx] hw oneB bellB n x ≐ bell (succ n) :=
  (hw_comm oneB bellB n x).eqTrans (hw_bell_one n x)

/-- The Bell example as a closed sentence. Variables: `0 = n`, `1 = x`. -/
theorem hw_one_bell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (hw oneB bellB (var 0) (var 1) ≐ bell (succ (var 0))) :=
  closeUniv 2 (hw_one_bell _ _)

end BellNumbers

end LeanProofs.IPRA.Foundations.HurwitzProduct
