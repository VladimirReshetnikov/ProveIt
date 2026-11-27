import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianPolynomialLowJetProduct
import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmCoefficientRecursion

/-!
# Original polynomial product algebra through actual exponent readers

The already proved actual product association, commutation and original
coefficient-addition programs give normalized exponent-reader identities.
All list shapes and numerical degree guards are explicit. The finite
addition rule is derived from original convolution accumulation, and
commutation jets use the original actual product code. No polynomial
algebra or desired coefficient law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialExponentAlgebra

open_ipra
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalPolynomialProduct (product product_lookup)
open GaussianRationalPolynomialBuffers (added)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianFiniteLogarithmCoefficientRecursion (product_commuted_exponent)
open GaussianPolynomialLowJetProduct (jetEqual)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem associative_reader (P Q R N M L e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ N) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (hR : Γ ⊢[PRAAx] length R ≐ succ L) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (product (product P Q N M) R (N+M) L) ((N+M)+L) e ≐
      exponentCoefficient (product P (product Q R M L) N (M+L)) (N+(M+L)) e := by
  have range := le_trans he (le_trans (le_add_right N M) (le_add_right (N+M) L))
  exact (exponent_inside _ _ _ range).eqTrans
    ((GaussianRationalPolynomialPowerEuler.product_associative_coefficient P Q R N M L _ hP hQ hR
      (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
        ((entry_congr (.eqRefl _) (congrMonus (by ipra_ring) (.eqRefl e))).eqTrans
          (exponent_inside _ _ _ (le_trans he (le_add_right N (M+L)))).eqSymm))

theorem right_distribution (P A B N M e : PTm n) (he : Γ ⊢[PRAAx] le e (N+M)) : Γ ⊢[PRAAx]
    exponentCoefficient (product P (added A B (succ M)) N M) (N+M) e ≐
      qadd (exponentCoefficient (product P A N M) (N+M) e) (exponentCoefficient (product P B N M) (N+M) e) := by
  have range : Γ ⊢[PRAAx] le (monus (N+M) e) (N+M) := GaussianRationalMonicReconstruction.monus_le_left _ _
  exact (exponent_inside _ _ _ he).eqTrans
    ((product_lookup _ _ _ _ _ range).eqTrans
      ((GaussianRationalMonicReconstruction.coefficient_added P A B M (succ N) (monus (N+M) e)).eqTrans
        (qadd_congr ((product_lookup _ _ _ _ _ range).eqSymm.eqTrans (exponent_inside _ _ _ he).eqSymm)
          ((product_lookup _ _ _ _ _ range).eqSymm.eqTrans (exponent_inside _ _ _ he).eqSymm))))

theorem left_distribution (A B C D E e : PTm n)
    (hA : Γ ⊢[PRAAx] length A ≐ succ D) (hB : Γ ⊢[PRAAx] length B ≐ succ D)
    (hC : Γ ⊢[PRAAx] length C ≐ succ E)
    (heD : Γ ⊢[PRAAx] le e D) (heE : Γ ⊢[PRAAx] le e E) : Γ ⊢[PRAAx]
    exponentCoefficient (product (added A B (succ D)) C D E) (D+E) e ≐
      qadd (exponentCoefficient (product A C D E) (D+E) e) (exponentCoefficient (product B C D E) (D+E) e) :=
  (product_commuted_exponent _ _ _ _ _ (GaussianRationalPolynomialBuffers.added_length _ _ _) hC heD).eqTrans
    ((right_distribution C A B E D e (le_trans heE (le_add_right E D))).eqTrans
      (qadd_congr (product_commuted_exponent C E A D e hC hA heE)
        (product_commuted_exponent C E B D e hC hB heE)))

theorem commutative_jet (P Q N M H : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ N) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (hH : Γ ⊢[PRAAx] le H N) : Γ ⊢[PRAAx]
    jetEqual (product P Q N M) (N+M) (product Q P M N) (M+N) H := by
  have ps := GaussianRationalPolynomialPowerEuler.shift_length P N hP
  have qs := GaussianRationalPolynomialPowerEuler.shift_length Q M hQ
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hH.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    le_trans ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) hs.wk
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product,PTm.subst_add] using
    product_commuted_exponent (Syn.shift P) (Syn.shift N) (Syn.shift Q) (Syn.shift M) (var 0) ps.wk qs.wk hi

theorem original_actual_polynomial_product_exponent_association_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 4) ⟶ length (var 2) ≐ succ (var 5) ⟶
      le (var 6) (var 3) ⟶
      exponentCoefficient (product (product (var 0) (var 1) (var 3) (var 4)) (var 2) (var 3+var 4) (var 5))
        ((var 3+var 4)+var 5) (var 6) ≐
      exponentCoefficient (product (var 0) (product (var 1) (var 2) (var 4) (var 5)) (var 3) (var 4+var 5))
        (var 3+(var 4+var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (associative_reader _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_actual_polynomial_product_right_distribution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 3+var 4) ⟶
      exponentCoefficient (product (var 0) (added (var 1) (var 2) (succ (var 4))) (var 3) (var 4)) (var 3+var 4) (var 5) ≐
        qadd (exponentCoefficient (product (var 0) (var 1) (var 3) (var 4)) (var 3+var 4) (var 5))
          (exponentCoefficient (product (var 0) (var 2) (var 3) (var 4)) (var 3+var 4) (var 5))) :=
  closeUniv 6 (.impI (right_distribution _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialExponentAlgebra
