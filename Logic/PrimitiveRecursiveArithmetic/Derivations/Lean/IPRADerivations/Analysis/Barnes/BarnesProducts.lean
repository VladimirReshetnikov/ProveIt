import IPRADerivations.Analysis.Barnes.BarnesInteger
import IPRADerivations.Analysis.RationalArithmetic.Powers.Pochhammer

/-!
# Finite products in the Barnes functional equation

Packet: `analysis/barnes_g_ipra_2026-11-16`, Section 4. The monomial
cancellation used in `eq:finite-ratio` is proved after clearing denominators,
with both the cutoff and the argument variables of the object formula.
The positive-integer instances of `eq:gamma-finite-product` and
`eq:gamma-finite-quotient` use the existing Barnes and factorial symbols.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BarnesProducts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.BarnesInteger (barnes barnes_zero barnes_succ barnes_pos)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_zero poch_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (quo_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The numerator factor `(z + i + 1)^(i + 1)`. -/
abbrev upperBody : PTm 2 := pw (succ (var 1 + var 0)) (succ (var 0))
/-- The denominator factor `(z + i)^(i + 1)`. -/
abbrev lowerBody : PTm 2 := pw (var 1 + var 0) (succ (var 0))

abbrev upper (N z : PTm n) : PTm n := ap2 (prodF upperBody) N z
abbrev lower (N z : PTm n) : PTm n := ap2 (prodF lowerBody) N z

theorem upper_zero (z : PTm n) : Γ ⊢[PRAAx] upper zero z ≐ one := prod_zero _ _
theorem lower_zero (z : PTm n) : Γ ⊢[PRAAx] lower zero z ≐ one := prod_zero _ _

theorem upper_succ (N z : PTm n) :
    Γ ⊢[PRAAx] upper (succ N) z ≐ upper N z * pw (succ (z + N)) (succ N) := by
  simpa only [PTm.subst_add, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] using
    (prod_succ (Γ := Γ) upperBody N z)

theorem lower_succ (N z : PTm n) :
    Γ ⊢[PRAAx] lower (succ N) z ≐ lower N z * pw (z + N) (succ N) := by
  simpa only [PTm.subst_add, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] using
    (prod_succ (Γ := Γ) lowerBody N z)

private theorem cancellation_base (z : PTm n) :
    Γ ⊢[PRAAx] upper zero z * poch z zero ≐ pw (z + zero) zero * lower zero z := by
  have u := natEq (upper_zero (Γ := Γ) z)
  have l := natEq (lower_zero (Γ := Γ) z)
  have p := natEq (poch_zero (Γ := Γ) z)
  have e := natEq (pw_zero (Γ := Γ) (z + zero))
  apply deriveNat
  ipra_simps
  rw [u, l, p, e]

private theorem cancellation_step {N z : PTm n}
    (ih : Γ ⊢[PRAAx] upper N z * poch z N ≐ pw (z + N) N * lower N z) :
    Γ ⊢[PRAAx] upper (succ N) z * poch z (succ N) ≐
      pw (z + succ N) (succ N) * lower (succ N) z := by
  have u := natEq (upper_succ (Γ := Γ) N z)
  have l := natEq (lower_succ (Γ := Γ) N z)
  have p := natEq (poch_succ (Γ := Γ) z N)
  have e := natEq (pw_succ (Γ := Γ) (z + N) N)
  have s := natEq (congrAp2 (Γ := Γ) powF (.eqRefl (succ N)) (add_succ z N))
  have h := natEq ih
  apply deriveNat
  ipra_simps
  rw [u, l, p, e, s]
  linear_combination 𝔞(pw (succ (z + N)) (succ N)) * (𝔞(z) + 𝔞(N)) * h

/-- Variables `0 = N`, `1 = z`. -/
abbrev cancellationFormula : Fm PTm 2 :=
  upper (var 0) (var 1) * poch (var 1) (var 0) ≐
    pw (var 1 + var 0) (var 0) * lower (var 0) (var 1)

private theorem cancellation_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] cancellationFormula := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact cancellation_base _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact cancellation_step Prf.hyp0

/-- The cleared monomial cancellation behind `eq:finite-ratio`, including
the zero cutoff and zero argument. -/
theorem finite_ratio (N z : PTm n) :
    Γ ⊢[PRAAx] upper N z * poch z N ≐ pw (z + N) N * lower N z := by
  have h := inst (Γ := Γ) cancellation_open (![N, z] : Fin 2 → PTm n)
  simpa using h

theorem finite_ratio_sentence : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 cancellationFormula :=
  closeUniv 2 cancellation_open

/-- The factors are `Γ(k + i + 1) = (k + i)!` at natural `k` and `i`. -/
abbrev gammaBody : PTm 2 := fact (var 1 + var 0)
abbrev gammaProduct (N k : PTm n) : PTm n := ap2 (prodF gammaBody) N k

theorem gammaProduct_zero (k : PTm n) : Γ ⊢[PRAAx] gammaProduct zero k ≐ one := prod_zero _ _

theorem gammaProduct_succ (N k : PTm n) :
    Γ ⊢[PRAAx] gammaProduct (succ N) k ≐ gammaProduct N k * fact (k + N) := by
  simpa only [PTm.subst_add, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_zero] using
    (prod_succ (Γ := Γ) gammaBody N k)

private theorem gamma_base (k : PTm n) :
    Γ ⊢[PRAAx] barnes (k + zero) ≐ barnes k * gammaProduct zero k := by
  have b := natEq (congrAp2 (Γ := Γ) (prodF BarnesInteger.facB) (add_zero k) (.eqRefl zero))
  have p := natEq (gammaProduct_zero (Γ := Γ) k)
  apply deriveNat
  ipra_simps
  rw [b, p]
  ring

private theorem gamma_step {N k : PTm n}
    (ih : Γ ⊢[PRAAx] barnes (k + N) ≐ barnes k * gammaProduct N k) :
    Γ ⊢[PRAAx] barnes (k + succ N) ≐ barnes k * gammaProduct (succ N) k := by
  have b := natEq ((congrAp2 (Γ := Γ) (prodF BarnesInteger.facB)
    (add_succ k N) (.eqRefl zero)).eqTrans (barnes_succ (k + N)))
  have p := natEq (gammaProduct_succ (Γ := Γ) N k)
  have h := natEq ih
  apply deriveNat
  ipra_simps
  rw [b, p, h]
  ring

/-- Variables `0 = N`, `1 = k`. -/
abbrev gammaFormula : Fm PTm 2 :=
  barnes (var 1 + var 0) ≐ barnes (var 1) * gammaProduct (var 0) (var 1)

private theorem gamma_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] gammaFormula := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero]
    exact gamma_base _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero]
    exact gamma_step Prf.hyp0

/-- `eq:gamma-finite-product` at all positive integer arguments,
`G(k + N + 1) = G(k + 1) ∏_{i<N} Γ(k + i + 1)`. -/
theorem gamma_finite_product (N k : PTm n) :
    Γ ⊢[PRAAx] barnes (k + N) ≐ barnes k * gammaProduct N k := by
  have h := inst (Γ := Γ) gamma_open (![N, k] : Fin 2 → PTm n)
  simpa using h

theorem gamma_finite_product_sentence : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 gammaFormula :=
  closeUniv 2 gamma_open

/-- `eq:gamma-finite-quotient` at positive integers, with exact division. -/
theorem gamma_finite_quotient (N k : PTm n) :
    Γ ⊢[PRAAx] quo (barnes (k + N)) (barnes k) ≐ gammaProduct N k :=
  quo_of_eq (barnes_pos k) (gamma_finite_product N k)

/-- Variables `0 = N`, `1 = k`. -/
abbrev gammaQuotientFormula : Fm PTm 2 :=
  quo (barnes (var 1 + var 0)) (barnes (var 1)) ≐ gammaProduct (var 0) (var 1)

theorem gamma_finite_quotient_sentence :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 gammaQuotientFormula :=
  closeUniv 2 (gamma_finite_quotient (var 0) (var 1))

#print axioms finite_ratio_sentence
#print axioms gamma_finite_product_sentence
#print axioms gamma_finite_quotient_sentence

end LeanProofs.IPRA.Analysis.BarnesProducts
