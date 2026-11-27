import IPRADerivations.Analysis.Polynomials.Annihilators.GaussianAnnihilatorPolynomial
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticNormDegree

/-!
# The finite polynomial-witness bound for a superelliptic subspace

The supplied nonzero finite coefficient witness is compiled by the actual
annihilator-polynomial program. Its nonzero rows and weighted bound are
derived, and the original norm has that exact degree. An explicit zero
witness for this SAME polynomial then bounds the listed curve points.

This module is a witness-bound adapter. It does not construct a nonzero
functional from rank deficiency, or assume that an unfinished row-span
interface already proves the polynomial-zero witness. Those separate
evaluation and membership adapters can discharge the premise below.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceWitness

open_ipra
open LeanProofs.IPRA.Analysis.GaussianPolynomialWeightedDegree (weightedDegree)
open LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers (pointDistinct functionZeros)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (degree nonzeroCoefficients)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticNormDegree (pointPowers)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (f a m c L : PTm n) : PTm n :=
  GaussianAnnihilatorPolynomial.polynomial a m (degree f c) L

def weight (f a m c L : PTm n) : PTm n := weightedDegree (polynomial f a m c L) m L (degree f c)

def basisCount (f m c L : PTm n) : PTm n := GaussianWeightedMonomialBasis.count m (degree f c) L

def curveInput (f m c : PTm n) : Fm PTm n := le (succ one) m ⋏ (le one (degree f c) ⋏
  (gcd m (degree f c) ≐ one ⋏ (length f ≐ succ c ⋏ nonzeroCoefficients f c)))

def input (f a m c L : PTm n) : Fm PTm n := curveInput f m c ⋏
  ((length a ≐ basisCount f m c L) ⋏ GaussianAnnihilatorPolynomial.nonzeroLambda a m (degree f c) L)

def points (f m P : PTm n) : Fm PTm n := pointDistinct P ⋏ pointPowers f m P

/-- The explicit witness still to be derived from evaluation and span membership. -/
def zeroWitness (f a m c L P : PTm n) : Fm PTm n := functionZeros (polynomial f a m c L) m P

def certificate (f a m c L P : PTm n) : Fm PTm n :=
  GaussianSuperellipticNormDegree.certificate f (polynomial f a m c L) m L c ⋏
    (le (length P) (weight f a m c L) ⋏ le (weight f a m c L) L)

ipra_subst polynomial
ipra_subst weight
ipra_subst basisCount
@[simp] theorem subst_curveInput {l : ℕ} (σ : Fin n → PTm l) (f m c : PTm n) :
    (curveInput f m c).subst σ = curveInput (Syn.subst σ f) (Syn.subst σ m) (Syn.subst σ c) := by
  have hg (u v : PTm n) : Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
    simp only [gcd,subst_ex2,ConciseIPRA.PTm.subst_succ]
  simp [curveInput,hg]
ipra_subst input
ipra_subst points
ipra_subst zeroWitness

theorem annihilator_input (f a m c L : PTm n) (h : Γ ⊢[PRAAx] input f a m c L) :
    Γ ⊢[PRAAx] GaussianAnnihilatorPolynomial.input a m (degree f c) L :=
  .andI (le_trans (le_succ_self one) (.andE₁ (.andE₁ h))) (.andE₂ h)

theorem norm_input (f a m c L : PTm n) (h : Γ ⊢[PRAAx] input f a m c L) :
    Γ ⊢[PRAAx] GaussianSuperellipticNormDegree.input f (polynomial f a m c L) m L c := by
  have original := Prf.andE₁ h
  have rest := Prf.andE₂ original
  have fData := Prf.andE₂ (Prf.andE₂ rest)
  exact .andI (.andE₁ original) (.andI (.andE₁ rest) (.andI (.andE₁ (.andE₂ rest))
    (.andI (.andE₁ fData) (.andI (.andE₂ fData) (.andI
      (GaussianAnnihilatorPolynomial.polynomial_shape a m (degree f c) L)
      (GaussianAnnihilatorPolynomial.nonzero_rows a m (degree f c) L (.andE₂ (.andE₂ h))))))))

theorem exact_norm (f a m c L : PTm n) (h : Γ ⊢[PRAAx] input f a m c L) :
    Γ ⊢[PRAAx] GaussianSuperellipticNormDegree.certificate f (polynomial f a m c L) m L c :=
  GaussianSuperellipticNormDegree.original_norm_degree f (polynomial f a m c L) m L c (norm_input f a m c L h)

theorem weight_bound (f a m c L : PTm n) (h : Γ ⊢[PRAAx] input f a m c L) :
    Γ ⊢[PRAAx] le (weight f a m c L) L :=
  GaussianAnnihilatorPolynomial.weighted_bound a m (degree f c) L (annihilator_input f a m c L h)

theorem norm_points (f a m c L P : PTm n) (hP : Γ ⊢[PRAAx] points f m P)
    (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P) :
    Γ ⊢[PRAAx] GaussianSuperellipticNormDegree.pointInput f (polynomial f a m c L) m P :=
  .andI (.andE₁ hP) (.andI (.andE₂ hP) hZero)

theorem zero_witness_at (f a m c L P i : PTm n) (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialMonicCompanion.values (polynomial f a m c L) m (abscissa P i)) (ordinate P i) ≐ qzero := by
  have atPoint : Γ ⊢[PRAAx] lt i (length P) ⟶
      evaluate (GaussianPolynomialMonicCompanion.values (polynomial f a m c L) m (abscissa P i)) (ordinate P i) ≐ qzero := by
    simpa [zeroWitness,functionZeros] using hZero.allE i
  exact .impE atPoint hi

theorem weighted_point_bound (f a m c L P : PTm n) (h : Γ ⊢[PRAAx] input f a m c L)
    (hP : Γ ⊢[PRAAx] points f m P) (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P) :
    Γ ⊢[PRAAx] le (length P) (weight f a m c L) :=
  GaussianSuperellipticNormDegree.weighted_zero_bound f (polynomial f a m c L) m L c P
    (norm_input f a m c L h) (norm_points f a m c L P hP hZero)

theorem witness_bound (f a m c L P : PTm n) (h : Γ ⊢[PRAAx] input f a m c L)
    (hP : Γ ⊢[PRAAx] points f m P) (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P) :
    Γ ⊢[PRAAx] le (length P) L :=
  le_trans (weighted_point_bound f a m c L P h hP hZero) (weight_bound f a m c L h)

theorem witness_certificate (f a m c L P : PTm n) (h : Γ ⊢[PRAAx] input f a m c L)
    (hP : Γ ⊢[PRAAx] points f m P) (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P) :
    Γ ⊢[PRAAx] certificate f a m c L P :=
  .andI (exact_norm f a m c L h) (.andI (weighted_point_bound f a m c L P h hP hZero) (weight_bound f a m c L h))

def output (f a m c L P : PTm n) : PTm n := pairT (polynomial f a m c L)
  (pairT (GaussianSuperellipticNormDegree.originalNorm f (polynomial f a m c L) m L c)
    (pairT (weight f a m c L) (pairT (basisCount f m c L) (length P))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (f a m c L P : PTm n) : PTm n := app outputF ![f,a,m,c,L,P]
def outputField (p : PTm n) (i : Fin 5) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))] i

ipra_subst run
@[simp] theorem subst_outputField {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (outputField p i) = outputField (Syn.subst σ p) i := by fin_cases i <;> simp [outputField]

theorem program_at (f a m c L P : PTm n) : Γ ⊢[PRAAx] run f a m c L P ≐ output f a m c L P := by
  simpa [run,outputF,output,GaussianSuperellipticNormDegree.originalNorm] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![f,a,m,c,L,P]

theorem returned_fields (f a m c L P : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    outputField (run f a m c L P) i ≐ ![polynomial f a m c L,
      GaussianSuperellipticNormDegree.originalNorm f (polynomial f a m c L) m L c,
      weight f a m c L,basisCount f m c L,length P] i :=
  pairVectorField_eq 4 _ (program_at f a m c L P) i

theorem returned_weight_bound (f a m c L P : PTm n) (h : Γ ⊢[PRAAx] input f a m c L) :
    Γ ⊢[PRAAx] le (outputField (run f a m c L P) 2) L :=
  le_congr (returned_fields f a m c L P 2).eqSymm (.eqRefl _) (weight_bound f a m c L h)

theorem returned_point_bound (f a m c L P : PTm n) (h : Γ ⊢[PRAAx] input f a m c L)
    (hP : Γ ⊢[PRAAx] points f m P) (hZero : Γ ⊢[PRAAx] zeroWitness f a m c L P) :
    Γ ⊢[PRAAx] le (outputField (run f a m c L P) 4) L :=
  le_congr (returned_fields f a m c L P 4).eqSymm (.eqRefl _) (witness_bound f a m c L P h hP hZero)

theorem actual_compiled_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (polynomial (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 2) ⋏
      GaussianPolynomialMonicCompanion.rowShape (polynomial (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 4)) :=
  closeUniv 5 (.andI (GaussianAnnihilatorPolynomial.polynomial_length _ _ _ _)
    (GaussianAnnihilatorPolynomial.polynomial_shape _ _ _ _))
theorem actual_exact_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianSuperellipticNormDegree.certificate (var 0) (polynomial (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 4) (var 3)) :=
  closeUniv 5 (.impI (exact_norm _ _ _ _ _ Prf.hyp0))
theorem actual_compiled_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (weight (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4)) :=
  closeUniv 5 (.impI (weight_bound _ _ _ _ _ Prf.hyp0))
theorem actual_zero_witness_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (zeroWitness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ lt (var 6) (length (var 5)) ⟶
      evaluate (GaussianPolynomialMonicCompanion.values (polynomial (var 0) (var 1) (var 2) (var 3) (var 4))
        (var 2) (abscissa (var 5) (var 6))) (ordinate (var 5) (var 6)) ≐ qzero) :=
  closeUniv 7 (.impI (.impI (zero_witness_at _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_witness_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ points (var 0) (var 2) (var 5) ⟶
      zeroWitness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (witness_certificate _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_subspace_witness_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ points (var 0) (var 2) (var 5) ⟶
      zeroWitness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (length (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (witness_bound _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ points (var 0) (var 2) (var 5) ⟶
      zeroWitness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        le (outputField (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) 4) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (returned_point_bound _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceWitness
