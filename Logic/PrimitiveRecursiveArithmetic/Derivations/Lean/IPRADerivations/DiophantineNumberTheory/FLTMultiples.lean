import IPRADerivations.DiophantineNumberTheory.FermatQuartic
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Fermat's Last Theorem for exponents divisible by 4

Packet: `diophantine-number-theory/flt_ipra`, the exponent-four branch of Theorem `thm:main`,
by exponent lifting (Lemma `lem:lifting`) from `FermatQuartic.flt4`:

`∀ n x y z. 4 ∣ n → x, y ≥ 1 → xⁿ + yⁿ ≠ zⁿ`.

With `n = 4k`, a solution gives `(xᵏ)⁴ + (yᵏ)⁴ = (zᵏ)⁴` with `xᵏ, yᵏ ≥ 1` (`pw_mul`,
`pw_pos`). The case `n = 0` is included (`1 + 1 ≠ 1`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (q4)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (flt4 flt4Formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `(a + 1)ᵐ ≥ 1`. -/
theorem pw_pos (a m : PTm n) : Γ ⊢[PRAAx] pw (succ a) m ≐ succ (pred (pw (succ a) m)) :=
  Common.pos_pw (Common.succ_pos a) m

/-- `a⁴ = q4 a`. -/
theorem pw_four (a : PTm n) : Γ ⊢[PRAAx] pw a (two * two) ≐ q4 a := by
  have e : Γ ⊢[PRAAx] (two * two : PTm n) ≐ succ (succ (succ (succ zero))) := by
    ipra_ring
  refine (congrPw (.eqRefl _) e).eqTrans ?_
  refine withEq (pw_succ (Γ := Γ) a (succ (succ (succ zero)))) fun h₁ =>
    withEq (pw_succ (Γ := Γ) a (succ (succ zero))) fun h₂ =>
    withEq (pw_succ (Γ := Γ) a (succ zero)) fun h₃ =>
    withEq (pw_succ (Γ := Γ) a zero) fun h₄ => withEq (pw_zero (Γ := Γ) a) fun h₅ => ?_
  apply deriveNat; ipra_simps; rw [h₁, h₂, h₃, h₄, h₅]; ring

/-- `xⁿ = (xᵏ)⁴` for `n = 4k`. -/
theorem pw_lift {x N k : PTm n} (hN : Γ ⊢[PRAAx] N ≐ (two * two) * k) :
    Γ ⊢[PRAAx] pw x N ≐ q4 (pw x k) :=
  (congrPw (.eqRefl _) (hN.eqTrans (mul_comm _ _))).eqTrans ((pw_mul x k (two * two)).eqSymm.eqTrans
    (pw_four _))

/-- `FLT(n)` for `4 ∣ n`; variables `0 = n`, `1 = x - 1`, `2 = y - 1`, `3 = z`. -/
abbrev fltFourFormula : Fm PTm 4 :=
  dvd (two * two) (var 0) ⟶
    neg (pw (succ (var 1)) (var 0) + pw (succ (var 2)) (var 0) ≐ pw (var 3) (var 0))

theorem flt_multiple_of_four : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 fltFourFormula := by
  refine closeUniv 4 (.impI (.impI ?_))
  have h4 : ([pw (succ (var 1)) (var 0) + pw (succ (var 2)) (var 0) ≐ pw (var 3) (var 0),
      dvd (two * two) (var 0)] : List (Fm PTm 4)) ⊢[PRAAx] (two * two : PTm 4) ≐ succ (pred (two * two)) :=
    pos_mul two_pos two_pos
  have hN := eq_of_dvd' h4 Prf.hyp1
  have X := pw_pos (Γ := [pw (succ (var 1)) (var 0) + pw (succ (var 2)) (var 0) ≐ pw (var 3) (var 0),
      dvd (two * two) (var 0)]) (var 1 : PTm 4) (quo (var 0) (two * two))
  have Y := pw_pos (Γ := [pw (succ (var 1)) (var 0) + pw (succ (var 2)) (var 0) ≐ pw (var 3) (var 0),
      dvd (two * two) (var 0)]) (var 2 : PTm 4) (quo (var 0) (two * two))
  have F := inst (Γ := [pw (succ (var 1)) (var 0) + pw (succ (var 2)) (var 0) ≐ pw (var 3) (var 0),
      dvd (two * two) (var 0)]) (Prf.allOpen (Prf.allOpen (Prf.allOpen flt4)))
    (![pred (pw (succ (var 1)) (quo (var 0) (two * two))), pred (pw (succ (var 2)) (quo (var 0) (two * two))),
      pw (var 3) (quo (var 0) (two * two))] : Fin 3 → PTm 4)
  simp only [flt4Formula, Fm.subst_eq, subst_neg, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ] at F
  refine .impE F ?_
  have qX := congrMul (congrMul X X) (congrMul X X)
  have qY := congrMul (congrMul Y Y) (congrMul Y Y)
  exact (congrAdd qX qY).eqSymm.eqTrans ((congrAdd (pw_lift hN).eqSymm (pw_lift hN).eqSymm).eqTrans
    (Prf.hyp0.eqTrans (pw_lift hN)))

end LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples

export_ipra DiophantineNumberTheory.FLTMultiples (pw_pos)
