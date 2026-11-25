import IPRADerivations.Analysis.GaussianScalarSineTaylor
import IPRADerivations.Analysis.GaussianPolynomialExponentialLinear

/-!
# The literal sinc factorial sum

The signed even powers use the same odd factorials as the finite sine
polynomial. Multiplying this sinc sum by its argument gives the exact
finite sine polynomial, including at a zero argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarSincTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyValues (imaginaryPoint)
open GaussianNamedSineFromExponential (multiplier)
open GaussianRationalPolynomialExponential (inverseFactorial scalarSum)
open GaussianScalarExponentialOddTaylor (scalarTerm)
open GaussianScalarSineTaylor (signedTerm signedBody signedSum finite_sine_taylor)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalFiniteSum (sum sum_multiply multiplyBody multiply_body_at)
open GaussianRationalHorner (qadd qmul qzero canonical)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone power powerF power_zero power_succ)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qone_canonical)
open GaussianReciprocalHorner (qmul_associative qadd_commutative qsub_add_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sincTerm (z j : PTm n) : PTm n :=
  qmul (parityPoint j) (qmul (inverseFactorial (succ (two*j))) (power z (two*j)))
def sincBody : PTm 2 := sincTerm (var 1) (var 0)
def sincTaylor (z K : PTm n) : PTm n := sum sincBody K z
def sincTail (z K : PTm n) : PTm n := sum (shiftBody sincBody) K z

@[simp] theorem subst_sincTerm {m : ℕ} (σ : Fin n → PTm m) (z j : PTm n) :
    Syn.subst σ (sincTerm z j) = sincTerm (Syn.subst σ z) (Syn.subst σ j) := by
  simp [sincTerm]

@[simp] theorem subst_sincTaylor {m : ℕ} (σ : Fin n → PTm m) (z K : PTm n) :
    Syn.subst σ (sincTaylor z K) = sincTaylor (Syn.subst σ z) (Syn.subst σ K) := by
  simp [sincTaylor]

@[simp] theorem subst_sincTail {m : ℕ} (σ : Fin n → PTm m) (z K : PTm n) :
    Syn.subst σ (sincTail z K) = sincTail (Syn.subst σ z) (Syn.subst σ K) := by
  simp [sincTail]

theorem sinc_body_at (z j : PTm n) : inst2 sincBody j z = sincTerm z j := by
  simp [sincBody,inst2]

theorem sinc_canonical (z K : PTm n) : Γ ⊢[PRAAx] canonical (sincTaylor z K) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _

theorem sinc_zero (z : PTm n) : Γ ⊢[PRAAx] sincTaylor z zero ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem sinc_tail_zero (z : PTm n) : Γ ⊢[PRAAx] sincTail z zero ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem sinc_tail_succ (z K : PTm n) : Γ ⊢[PRAAx]
    sincTail z (succ K) ≐ qadd (sincTail z K) (sincTerm z (succ K)) := by
  simpa only [sincTail,inst2_shiftBody,sinc_body_at] using
    GaussianRationalFiniteSum.sum_succ (Γ := Γ) (shiftBody sincBody) K z

theorem sinc_term_zero (z : PTm n) : Γ ⊢[PRAAx] sincTerm z zero ≐ qone := by
  have deg : Γ ⊢[PRAAx] two*zero ≐ zero := mul_zero two
  have inv : Γ ⊢[PRAAx] inverseFactorial (succ (two*zero)) ≐ inverseFactorial one := by
    simpa only [GaussianRationalPolynomialExponential.subst_inverseFactorial,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (inverseFactorial (var 0) : PTm 1)
        (σ := ![succ (two*zero)]) (σ' := ![one]) (fun i => by fin_cases i; exact congrSucc deg)
  have fact := inv.eqTrans GaussianPolynomialExponentialLinear.inverse_factorial_one
  have weight := (congrAp2 powerF deg (.eqRefl z)).eqTrans (power_zero z)
  have id : Γ ⊢[PRAAx] qmul qone qone ≐ qone :=
    GaussianPolynomialDeterminantTerms.one_mul_canonical _ qone_canonical
  exact (qmul_congr GaussianRationalParityPower.parity_zero ((qmul_congr fact weight).eqTrans id)).eqTrans id

theorem sinc_head_tail (z K : PTm n) : Γ ⊢[PRAAx] sincTaylor z (succ K) ≐ qadd qone (sincTail z K) := by
  have h := GaussianRationalFiniteSum.sum_shift_first (Γ := Γ) sincBody K z
  rw [sinc_body_at] at h
  exact h.eqTrans (qadd_congr (sinc_term_zero z) (.eqRefl _))

theorem sinc_difference_tail (z K : PTm n) :
    Γ ⊢[PRAAx] qsub (sincTaylor z (succ K)) qone ≐ sincTail z K :=
  (qsub_congr ((sinc_head_tail z K).eqTrans (qadd_commutative _ _)) (.eqRefl _)).eqTrans
    (qsub_add_cancel _ _ (GaussianRationalFiniteSum.sum_canonical _ _ _))

private theorem swap_inner (a b c : PTm n) :
    Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

theorem sine_term_factors (z j : PTm n) : Γ ⊢[PRAAx]
    signedTerm z j ≐ qmul z (sincTerm z j) := by
  let d := two*j
  let a := inverseFactorial (succ d)
  let k := parityPoint j
  let w := power z d
  have h := (qmul_commutative (Γ := Γ) z w).eqTrans (power_succ z d).eqSymm
  have arrange := (swap_inner (Γ := Γ) z k (qmul a w)).eqTrans
    (qmul_congr (.eqRefl k) ((swap_inner z a w).eqTrans (qmul_congr (.eqRefl a) h)))
  exact arrange.eqSymm

theorem sine_taylor_factors (z K : PTm n) : Γ ⊢[PRAAx] signedSum z K ≐ qmul z (sincTaylor z K) := by
  apply Prf.eqSymm
  refine (sum_multiply sincBody z K z).eqSymm.eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded (multiplyBody sincBody) signedBody K (pairT z z) z (.allI (.impI ?_)))
  let x := Syn.shift z
  let C := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have e := multiply_body_at (Γ := C) sincBody x (var 0) x
  rw [sinc_body_at] at e
  have right : inst2 signedBody (var 0) x = signedTerm x (var 0) := by
    simp [signedBody,signedTerm,scalarTerm,inst2]
  have h : C ⊢[PRAAx] qmul x (sincTerm x (var 0)) ≐ inst2 signedBody (var 0) x := by
    rw [right]
    exact (sine_term_factors (Γ := C) x (var 0)).eqSymm
  simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,subst_pairT,C,x] using e.eqTrans h

theorem finite_sine_sinc (z K : PTm n) : Γ ⊢[PRAAx]
    qmul multiplier (qsub (scalarSum (qmul imaginaryPoint z) (two*K))
      (scalarSum (qnegative (qmul imaginaryPoint z)) (two*K))) ≐ qmul z (sincTaylor z K) :=
  (finite_sine_taylor z K).eqTrans (sine_taylor_factors z K)

theorem actual_finite_sine_sinc_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (signedSum (var 0) (var 1) ≐ qmul (var 0) (sincTaylor (var 0) (var 1))) :=
  closeUniv 2 (sine_taylor_factors _ _)

theorem actual_finite_exponential_sinc_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul multiplier (qsub (scalarSum (qmul imaginaryPoint (var 0)) (two*var 1))
      (scalarSum (qnegative (qmul imaginaryPoint (var 0))) (two*var 1))) ≐ qmul (var 0) (sincTaylor (var 0) (var 1))) :=
  closeUniv 2 (finite_sine_sinc _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarSincTaylor
