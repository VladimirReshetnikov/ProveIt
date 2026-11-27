import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRational.GaussianRationalFirstOrderPolynomial

/-!
# Uniform compact first-order bounds for actual rational polynomials

For U>=1 the old cleared Horner size is monotone in its prefix length.
Its terminal value M(C,U) bounds every actual synthetic-quotient cell
uniformly over anchors |t|<=U. The SAME padded quotient therefore has
original Euclidean coefficient bound M; the checked weighted-power
Horner estimate gives an anchor-independent quadratic Taylor constant.
The old Beta primitive is used unchanged, with all numerical degrees.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalUniformFirstOrderPolynomial

open_ipra
open GaussianRationalVariableHornerBudget (size size_succ denominator denominator_positive)
open GaussianRationalFirstOrderPolynomial (paddedQuotient slope remainder padded_length)
open GaussianRationalHorner (positive_product evaluate horner qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (quotient)
open GaussianEuclideanResidualRadius (coefficientBounds)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mass (C U : PTm n) : PTm n := size C U (length C)
def constant (C N U : PTm n) : PTm n := GaussianRationalHornerLipschitz.constant N U (mass C U)
def slopeConstant (C N U : PTm n) : PTm n := mass C U*GaussianRationalHornerLipschitz.geometric U (succ N)
ipra_subst mass
ipra_subst constant

ipra_subst slopeConstant

theorem size_index_congr (C U : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx] size C U k ≐ size C U l :=
  congrFst (congrAp2 GaussianRationalVariableHornerBudget.stateF h (.eqRefl _))
theorem size_increment (C U k : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx] le (size C U k) (size C U (succ k)) := by
  have grow : Γ ⊢[PRAAx] le (size C U k) (U*size C U k) := le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (size C U k) hU)
  exact le_trans grow (le_congr (.eqRefl _) (size_succ C U k).eqSymm (le_add_right _ _))

def sizeLaw (C U k j : PTm n) : Fm PTm n := le (size C U k) (size C U (k+j))
ipra_subst sizeLaw
theorem size_forward (C U k j : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx] sizeLaw C U k j := by
  have us : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by simpa [Fm.shift,Syn.shift] using hU.shift
  have all : Γ ⊢[PRAAx] .all (sizeLaw (Syn.shift C) (Syn.shift U) (Syn.shift k) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_sizeLaw]
    · exact le_congr (.eqRefl _) (size_index_congr C U (add_zero k)).eqSymm (le_refl _)
    · exact le_trans Prf.hyp0 (le_congr (.eqRefl _)
        (size_index_congr _ _ (add_succ (Syn.shift k) (var 0))).eqSymm
        (size_increment _ _ _ us.wk))
  simpa only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem size_monotone (C U k l : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    le (size C U k) (size C U l) :=
  le_congr (.eqRefl _) (size_index_congr C U (eq_add_of_le hkl).eqSymm) (size_forward C U k (monus l k) hU)

theorem prefix_bound (C U t k : PTm n) (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one)
    (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx] bounded (horner C t k) (mass C U) one := by
  have raw := GaussianRationalVariableHornerBudget.size_prefix C U t k ht hk
  have grow : Γ ⊢[PRAAx] le (size C U k) (mass C U*denominator C) :=
    le_trans (size_monotone C U k (length C) hU hk)
      (le_congr (by unfold mass; ipra_ring) (by ipra_ring)
        (mul_le_mul_right (mass C U) (denominator_positive (Γ := Γ) C)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (denominator_positive C) (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) grow) raw

theorem quotient_coefficient_bound (C t N U i : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one)
    (hi : Γ ⊢[PRAAx] lt i (length (paddedQuotient C t N))) : Γ ⊢[PRAAx]
    bounded (entry (paddedQuotient C t N) i) (mass C U) one := by
  have range : Γ ⊢[PRAAx] le i N := (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (padded_length C t N) hi)
  refine .orE (lt_or_le i one) ?_ ?_
  · exact GaussianRationalReciprocal.bound_congr (GaussianRationalPolynomialBuffers.pad_leading _ one i Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded (mass C U) one (le_refl one))
  · let j := monus i one
    have idx : (le one i :: Γ) ⊢[PRAAx] i ≐ one+j := eq_add_of_le Prf.hyp0
    have jN : (le one i :: Γ) ⊢[PRAAx] lt j N :=
      le_congr (by ipra_ring) (.eqRefl _) (le_congr idx (.eqRefl _) range.wk)
    have row : (le one i :: Γ) ⊢[PRAAx] entry (paddedQuotient C t N) i ≐ horner C t (succ j) :=
      (entry_congr (.eqRefl _) idx).eqTrans
        ((GaussianRationalPolynomialBuffers.pad_tail _ one j
          (lt_congr (.eqRefl _) (GaussianRationalSyntheticDivision.quotient_length C t N).eqSymm jN)).eqTrans
            (GaussianRationalSyntheticDivision.quotient_lookup C t N j jN))
    have cap : (le one i :: Γ) ⊢[PRAAx] le (succ j) (length C) :=
      le_trans jN (le_congr (.eqRefl _) hLen.wk.eqSymm (le_succ_self N))
    exact GaussianRationalReciprocal.bound_congr row.eqSymm (.eqRefl _) (.eqRefl _) (prefix_bound C U t (succ j) hU.wk ht.wk cap)

theorem quotient_coefficients (C t N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one) : Γ ⊢[PRAAx]
    coefficientBounds (paddedQuotient C t N) (mass C U) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hLen.shift
  have us : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by simpa [Fm.shift,Syn.shift] using hU.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift t) (Syn.shift U) one := by simpa [Fm.shift,Syn.shift] using ht.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalFirstOrderPolynomial.subst_paddedQuotient,subst_mass] using
    quotient_coefficient_bound (Syn.shift C) (Syn.shift t) (Syn.shift N) (Syn.shift U) (var 0) cs.wk us.wk ts.wk Prf.hyp0

/-- A compact derivative bound independent of the actual anchor t. -/
theorem slope_bound (C t N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one) : Γ ⊢[PRAAx]
    bounded (slope C t N) (slopeConstant C N U) one := by
  let D := paddedQuotient C t N
  have shape := padded_length (Γ := Γ) C t N
  have raw := GaussianRationalHornerLipschitz.size_prefix D t (mass C U) U (succ N)
    (quotient_coefficients C t N U hLen hU ht) ht (le_congr (.eqRefl _) shape.eqSymm (le_refl _))
  exact GaussianRationalReciprocal.bound_congr
    ((congrAp3 GaussianRationalHorner.hornerF shape.eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
      (GaussianRationalPolynomialBuffers.pad_evaluation _ one t)) (.eqRefl _) (.eqRefl _) raw

/-- Uniform quadratic first-order estimate with the SAME old polynomial,
original raw increment, and an anchor-independent finite constant. -/
theorem first_order_bound (C t h N U A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one) (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    bounded (remainder C t h N) (constant C N U*A*A) (B*B) := by
  let D := paddedQuotient C t N
  have raw := GaussianRationalHornerLipschitz.evaluation_bound D (qadd t h) t N U (mass C U) A B (padded_length C t N)
    (quotient_coefficients C t N U hLen hU ht) hx ht hB (GaussianRationalFirstOrderPolynomial.increment_distance t h A B hB hh)
  have actual := distance_congr (GaussianRationalPolynomialBuffers.pad_evaluation _ one (qadd t h))
    (GaussianRationalPolynomialBuffers.pad_evaluation _ one t) (.eqRefl _) (.eqRefl _) raw
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB hB hh actual
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalFirstOrderPolynomial.remainder_identity C t h N hLen).eqSymm
    (by unfold constant; ipra_ring) (.eqRefl _) product

/-- Original Beta polynomial: no source/output/derivative bound is given
as a premise. Its actual constructor supplies the only shape guard. -/
theorem beta_first_order_bound (z D N t h U A B : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    bounded (GaussianRationalFirstOrderPolynomial.betaRemainder z D N t h)
      (constant (GaussianEulerBetaPolynomialPrimitive.primitive z D N) N U*A*A) (B*B) :=
  first_order_bound _ _ _ _ _ _ _ (GaussianEulerBetaPolynomialPrimitive.primitive_length z D N) hU ht hx hB hh

/-- Uniform original-polynomial value budget on the compact disk. -/
theorem value_bound (C t U : PTm n) (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one) : Γ ⊢[PRAAx]
    bounded (evaluate C t) (mass C U) one := prefix_bound C U t (length C) hU ht (le_refl _)

/-- These three constants are computed from C,N,U alone, before choosing
an anchor or increment. The original old size/weighted sum are retained. -/
def output (C N U : PTm n) : PTm n := pairT (mass C U) (pairT (slopeConstant C N U) (constant C N U))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N U : PTm n) : PTm n := ap3 outputF C N U
theorem program_at (C N U : PTm n) : Γ ⊢[PRAAx] run C N U ≐ output C N U := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,U]

theorem actual_polynomial_uniform_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((length (var 0) ≐ succ (var 3) ⋏ le one (var 4) ⋏ bounded (var 1) (var 4) one ⋏ bounded (qadd (var 1) (var 2)) (var 4) one ⋏
      le one (var 6) ⋏ bounded (var 2) (var 5) (var 6)) ⟶
      bounded (remainder (var 0) (var 1) (var 2) (var 3))
        (constant (var 0) (var 3) (var 4)*var 5*var 5) (var 6*var 6)) :=
  closeUniv 7 (.impI (first_order_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem original_Beta_primitive_uniform_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 5) ⋏ bounded (var 3) (var 5) one ⋏ bounded (qadd (var 3) (var 4)) (var 5) one ⋏ le one (var 7) ⋏ bounded (var 4) (var 6) (var 7)) ⟶
      bounded (GaussianRationalFirstOrderPolynomial.betaRemainder (var 0) (var 1) (var 2) (var 3) (var 4))
        (constant (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2)) (var 2) (var 5)*var 6*var 6) (var 7*var 7)) :=
  closeUniv 8 (.impI (beta_first_order_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))
theorem actual_polynomial_uniform_slope_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (var 0) ≐ succ (var 2) ⋏ le one (var 3) ⋏ bounded (var 1) (var 3) one) ⟶
      bounded (slope (var 0) (var 1) (var 2)) (slopeConstant (var 0) (var 2) (var 3)) one) :=
  closeUniv 4 (.impI (slope_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_uniform_first_order_constants_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalUniformFirstOrderPolynomial
