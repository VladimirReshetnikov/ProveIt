import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianRationalLowCoefficientConvolution

/-!
# Exact first three coefficients of actual polynomial convolution

The actual stored convolution's constant, linear and quadratic entries
are the literal finite Cauchy formulas. Both input degrees remain internal;
each reader retains the degree guard required by the original constructor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialFirstCoefficients

open_ipra
open GaussianRationalHorner (qmul qadd)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalLowCoefficientConvolution (term termBody data cauchySum term_at coefficient_cauchy)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem prefix_one (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum termBody one (data P Q N M e) ≐ term P Q N M e zero :=
  GaussianRationalFiniteSum.sum_singleton _ _ (term_at P Q N M e zero)
    (GaussianRationalHorner.qmul_canonical _ _)
theorem prefix_two (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum termBody two (data P Q N M e) ≐ qadd (term P Q N M e zero) (term P Q N M e one) :=
  (GaussianRationalFiniteSum.sum_succ _ one _).eqTrans (qadd_congr (prefix_one P Q N M e) (term_at P Q N M e one))
theorem prefix_three (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum termBody (succ two) (data P Q N M e) ≐
      qadd (qadd (term P Q N M e zero) (term P Q N M e one)) (term P Q N M e two) :=
  (GaussianRationalFiniteSum.sum_succ _ two _).eqTrans (qadd_congr (prefix_two P Q N M e) (term_at P Q N M e two))

theorem term_first (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    term P Q N M e zero ≐ qmul (entry P N) (entry Q (monus M e)) :=
  qmul_congr (entry_congr (.eqRefl _) (monus_zero N))
    (entry_congr (.eqRefl _) (congrMonus (.eqRefl _) (monus_zero e)))
theorem term_last (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    term P Q N M e e ≐ qmul (entry P (monus N e)) (entry Q M) :=
  qmul_congr (.eqRefl _) (entry_congr (.eqRefl _)
    ((congrMonus (.eqRefl _) (monus_self e)).eqTrans (monus_zero M)))

theorem constant_value (P Q N M : PTm n) : Γ ⊢[PRAAx]
    entry (product P Q N M) (N+M) ≐ qmul (entry P N) (entry Q M) :=
  (entry_congr (.eqRefl _) (monus_zero (N+M)).eqSymm).eqTrans
    ((coefficient_cauchy P Q N M zero (zero_le N) (zero_le M)).eqTrans
      ((prefix_one P Q N M zero).eqTrans
        ((term_first P Q N M zero).eqTrans
          (qmul_congr (.eqRefl _) (entry_congr (.eqRefl _) (monus_zero M))))))

theorem linear_value (P Q N M : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    entry (product P Q N M) (monus (N+M) one) ≐
      qadd (qmul (entry P N) (entry Q (monus M one))) (qmul (entry P (monus N one)) (entry Q M)) :=
  (coefficient_cauchy P Q N M one hN hM).eqTrans
    ((prefix_two P Q N M one).eqTrans (qadd_congr (term_first P Q N M one) (term_last P Q N M one)))

theorem quadratic_value (P Q N M : PTm n) (hN : Γ ⊢[PRAAx] le two N) (hM : Γ ⊢[PRAAx] le two M) : Γ ⊢[PRAAx]
    entry (product P Q N M) (monus (N+M) two) ≐
      qadd (qadd (qmul (entry P N) (entry Q (monus M two)))
        (qmul (entry P (monus N one)) (entry Q (monus M one))))
          (qmul (entry P (monus N two)) (entry Q M)) := by
  have mid : Γ ⊢[PRAAx] term P Q N M two one ≐ qmul (entry P (monus N one)) (entry Q (monus M one)) :=
    qmul_congr (.eqRefl _) (entry_congr (.eqRefl _) (congrMonus (.eqRefl _)
      ((succ_monus_succ one zero).eqTrans (monus_zero one))))
  exact (coefficient_cauchy P Q N M two hN hM).eqTrans
    ((prefix_three P Q N M two).eqTrans
      (qadd_congr (qadd_congr (term_first P Q N M two) mid) (term_last P Q N M two)))

theorem actual_convolution_constant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) ≐
      qmul (entry (var 0) (var 2)) (entry (var 1) (var 3))) :=
  closeUniv 4 (constant_value _ _ _ _)
theorem actual_convolution_linear_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ (le one (var 3) ⟶
      entry (product (var 0) (var 1) (var 2) (var 3)) (monus (var 2+var 3) one) ≐
        qadd (qmul (entry (var 0) (var 2)) (entry (var 1) (monus (var 3) one)))
          (qmul (entry (var 0) (monus (var 2) one)) (entry (var 1) (var 3))))) := by
  exact closeUniv 4 (.impI (.impI (linear_value _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialFirstCoefficients
