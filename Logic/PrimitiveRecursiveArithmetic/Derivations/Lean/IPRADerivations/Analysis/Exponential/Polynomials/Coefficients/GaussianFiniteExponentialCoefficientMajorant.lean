import IPRADerivations.Analysis.Exponential.Polynomials.Coefficients.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant

/-!
# A finite absolute coefficient majorant for the actual exponential program

The original factorial-weighted polynomial exponential, at arbitrary internal
cutoff K, has weighted coefficient norm bounded by the actual scalar
exponential partial sum at A, whenever its input weighted norm is at most A.
Consequently the bound is 3^A, uniformly in K. Both inductions retain the
original fixed-cap coefficient buffers. This supplies the finite exponential
coefficient majorant used in Gamma C19; it does not assume a coefficient
bound for a Gamma input polynomial or assert an infinite power-series limit.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteExponentialCoefficientMajorant

open_ipra
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length)
open GaussianRationalPolynomialExponential (stage inverseFactorial factorial_positive polynomial)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalCoefficientScaling (scaled)
open GaussianFiniteExponentialWeightedNorm (weighted_congr weighted_nonnegative multiply_bounds singleton_weighted_norm inverse_factorial_norm)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_nonnegative)
open GaussianPositiveExponentialMajorant (value natCode_congr)
open GaussianExponentialDiskMajorant (numerator real_majorant_represents)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalL1 (qL1)
open RationalArgmin (rationalLE)
open RationalArithmetic (multiply add)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerBudget (A j : PTm n) : PTm n := natCode (pw A j)
def termBudget (A j : PTm n) : PTm n := fraction (pw A j) (Products.fact j)
ipra_subst powerBudget
ipra_subst termBudget [Products.fact]

theorem power_budget_zero (A : PTm n) : Γ ⊢[PRAAx] powerBudget A zero ≐ natCode one :=
  natCode_congr (pw_zero A)
theorem power_budget_succ (A j : PTm n) : Γ ⊢[PRAAx]
    powerBudget A (succ j) ≐ multiply (powerBudget A j) (natCode A) :=
  (natCode_congr (pw_succ A j)).eqTrans (GaussianRationalSyntheticBounds.natCode_multiply _ _).eqSymm

def powerLaw (C N K t A j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget A j)
ipra_subst powerLaw

theorem power_zero (C N K t A : PTm n) : Γ ⊢[PRAAx] powerLaw C N K t A zero := by
  refine .impI ?_
  have actual := (weighted_congr (Γ := le zero K :: Γ) (GaussianRationalPolynomialPowers.prefix_zero C N K)
    (zero_mul N) (.eqRefl _)).eqTrans (singleton_weighted_norm t)
  exact RationalArgmin.rationalLE_congr actual.eqSymm (power_budget_zero A).eqSymm (RationalArgmin.reflexive _)

theorem power_step (C N K t A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A))
    (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget A j)) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K (succ j)) (succ j*N) t) (powerBudget A (succ j)) := by
  have first := GaussianRationalPolynomialDilation.weighted_product_bound
    (powerPrefix C N K j) C (j*N) N t (prefix_length _ _ _ _) hC
  have second := multiply_bounds _ _ _ _ (weighted_nonnegative C N t) (natCode_nonnegative _) ih hNorm
  exact RationalArgmin.rationalLE_congr
    (weighted_congr (GaussianRationalPolynomialPowers.prefix_succ C N K j hj).eqSymm (by ipra_ring) (.eqRefl _))
    (power_budget_succ A j).eqSymm (RationalArgmin.transitive first second)

theorem power_bound (C N K t A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget A j) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] rationalLE (weightedNorm (Syn.shift C) (Syn.shift N) (Syn.shift t)) (natCode (Syn.shift A)) := by
    simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianRationalPolynomialDilation.subst_weightedNorm,
      GaussianRationalSyntheticBounds.subst_natCode,Syn.shift] using hNorm.shift
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t) (Syn.shift A) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_powerLaw]
    · exact power_zero _ _ _ _ _
    · exact .impI (power_step _ _ _ _ _ _ cs.wk.wk ns.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] powerLaw C N K t A j := by
    simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

/-- The factorial is retained, rather than replaced by the unit bound. -/
theorem factorial_power_budget (A j : PTm n) : Γ ⊢[PRAAx]
    multiply (qL1 (inverseFactorial j)) (powerBudget A j) ≐ termBudget A j :=
  (RationalAlgebra.multiply_congr (inverse_factorial_norm j) (.eqRefl _)).eqTrans
    ((RationalNonnegativePowers.fraction_multiply one (Products.fact j) (pw A j) one
      (factorial_positive j) (le_refl one)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by ipra_ring)))

theorem weighted_term_bound (C N K t A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] rationalLE
      (weightedNorm (scaled (powerPrefix C N K j) (inverseFactorial j)) (j*N) t) (termBudget A j) := by
  have first := GaussianRationalPolynomialDilation.weighted_scaled_bound (Γ := Γ) (powerPrefix C N K j) (j*N) t
    (inverseFactorial j) (prefix_length _ _ _ _)
  have second := RationalArithmetic.multiply_monotone (qL1 (inverseFactorial j)) _ _
    (GaussianRationalL1.qL1_nonnegative _) (power_bound C N K t A j hC hNorm hj)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (factorial_power_budget A j) (RationalArgmin.transitive first second)

theorem scalar_zero (A : PTm n) : Γ ⊢[PRAAx] value A zero ≐ natCode one := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (GaussianRationalFiniteSum.sum_canonical _ _ _).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (real_majorant_represents A zero) (natCode_represents one) (factorial_positive _) (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [natEq (GaussianExponentialDiskMajorant.numerator_zero (Γ := Γ) A),
    natEq (fact_succ (Γ := Γ) zero zero)]
  ipra_simps
  rw [natEq (fact_zero (Γ := Γ) zero)]
  ipra_simps
  ring

theorem scalar_succ (A j : PTm n) : Γ ⊢[PRAAx]
    value A (succ j) ≐ add (value A j) (termBudget A (succ j)) := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) (value A j) (termBudget A (succ j))
    (ZT.ofNat (numerator A j)) (ZT.ofNat (pw A (succ j))) (Products.fact (succ j)) (Products.fact (succ j))
    (real_majorant_represents A j) (fraction_represents _ _ (factorial_positive _))
  apply Prf.eqSymm
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (GaussianRationalFiniteSum.sum_canonical _ _ _).andE₂.andE₁ rep (real_majorant_represents A (succ j))
    (GaussianRationalHorner.positive_product _ _ (factorial_positive _) (factorial_positive _)) (factorial_positive _)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  rw [natEq (GaussianExponentialDiskMajorant.numerator_succ (Γ := Γ) A j),
    natEq (fact_succ (Γ := Γ) (succ j) zero)]
  ipra_simps
  ring

def exponentialLaw (C N K t A j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (stage C N K j) (j*N) t) (value A j)
ipra_subst exponentialLaw

theorem exponential_zero (C N K t A : PTm n) : Γ ⊢[PRAAx] exponentialLaw C N K t A zero := by
  refine .impI ?_
  have actual := (weighted_congr (Γ := le zero K :: Γ) (GaussianRationalPolynomialExponential.stage_zero C N K)
    (zero_mul N) (.eqRefl _)).eqTrans (singleton_weighted_norm t)
  exact RationalArgmin.rationalLE_congr actual.eqSymm (scalar_zero A).eqSymm (RationalArgmin.reflexive _)

theorem exponential_step (C N K t A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K j) (j*N) t) (value A j)) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K (succ j)) (succ j*N) t) (value A (succ j)) := by
  have padded : Γ ⊢[PRAAx] weightedNorm (leftPad (stage C N K j) N) (succ j*N) t ≐
      weightedNorm (stage C N K j) (j*N) t :=
    (weighted_congr (.eqRefl _) (show Γ ⊢[PRAAx] succ j*N ≐ N+j*N by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianRationalPolynomialDilation.weighted_padding (stage C N K j) (j*N) t N
        (GaussianRationalPolynomialExponential.stage_length _ _ _ _))
  have oldBound := RationalArgmin.rationalLE_congr padded.eqSymm (.eqRefl _) ih
  have newBound := weighted_term_bound C N K t A (succ j) hC hNorm hj
  have sumBound := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ oldBound newBound
  have actual := GaussianRationalPolynomialDilation.weighted_added_bound (Γ := Γ)
    (leftPad (stage C N K j) N) (scaled (powerPrefix C N K (succ j)) (inverseFactorial (succ j))) (succ j*N) t
  exact RationalArgmin.rationalLE_congr
    (weighted_congr (GaussianRationalPolynomialExponential.stage_succ C N K j).eqSymm (.eqRefl _) (.eqRefl _))
    (scalar_succ A j).eqSymm (RationalArgmin.transitive actual sumBound)

theorem exponential_bound (C N K t A j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K j) (j*N) t) (value A j) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] rationalLE (weightedNorm (Syn.shift C) (Syn.shift N) (Syn.shift t)) (natCode (Syn.shift A)) := by
    simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianRationalPolynomialDilation.subst_weightedNorm,
      GaussianRationalSyntheticBounds.subst_natCode,Syn.shift] using hNorm.shift
  have all : Γ ⊢[PRAAx] .all (exponentialLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t) (Syn.shift A) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_exponentialLaw]
    · exact exponential_zero _ _ _ _ _
    · exact .impI (exponential_step _ _ _ _ _ _ cs.wk.wk ns.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] exponentialLaw C N K t A j := by
    simpa only [subst_exponentialLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem polynomial_scalar_majorant (C N K t A : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial C N K) (K*N) t) (value A K) :=
  exponential_bound C N K t A K hC hNorm (le_refl _)

theorem polynomial_numerical_majorant (C N K t A : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode A)) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial C N K) (K*N) t) (natCode (pw (num 3) A)) :=
  RationalArgmin.transitive (polynomial_scalar_majorant C N K t A hC hNorm)
    (GaussianPositiveExponentialMajorant.positive_real_majorant A K)

theorem actual_exponential_coefficient_scalar_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶
      (rationalLE (weightedNorm (var 0) (var 1) (var 3)) (natCode (var 4)) ⟶
        rationalLE (weightedNorm (polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3)) (value (var 4) (var 2)))) :=
  closeUniv 5 (.impI (.impI (polynomial_scalar_majorant _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_exponential_coefficient_numerical_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶
      (rationalLE (weightedNorm (var 0) (var 1) (var 3)) (natCode (var 4)) ⟶
        rationalLE (weightedNorm (polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3)) (natCode (pw (num 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (polynomial_numerical_majorant _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianFiniteExponentialCoefficientMajorant
