import IPRADerivations.Analysis.Integration.Moments.Even.GaussianEvenMomentIntegral
import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence

/-!
# Literal even Gaussian rows on the reflected affine grid

The signed rational times are t and -t with the same positive grid
width. Both rows use the exact rational monomial and original decay at
the same normalized clock. The two finite quadratures are exactly equal.
The unchanged positive-half quadratic grid is compared to the literal
positive half with the physical-width-scaled observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEvenMomentSymmetricGrid

open_ipra
open GaussianGammaHalfIntegerDomain (argument)
open GaussianEvenMomentIntegrand (clock)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianMomentReflection (row)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianCompactRiemannName (evaluatorName nameData inside grid sampleBody sampleData quadrature)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit)
open GaussianEulerPositiveScalingIntegrand (fixedData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def momentData (N c d : PTm n) : PTm n := pairT N (pairT c d)
def signedTime (negative : Bool) (a b : PTm n) : PTm n :=
  if negative then qnegative (fraction a b) else fraction a b
def literal (negative : Bool) (p N a b c d : PTm n) : PTm n :=
  row (clock p N a b c d) (two*N) (signedTime negative a b) a b c d
def evaluatorTerm (negative : Bool) (p t x : PTm n) : PTm n :=
  literal negative p (fstT x) (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x))
def evaluatorF (negative : Bool) : PR 3 := PTm.toPR (evaluatorTerm negative (var 0) (var 1) (var 2))
def source (a C E T c d : PTm n) : Fm PTm n :=
  (le one E ⋏ (le one a ⋏ le (a+C) (E*T))) ⋏ (le one c ⋏ le one d)
def symmetricGrid (p M a C E N c d : PTm n) : PTm n :=
  qadd (quadrature (evaluatorF false) p M a C E (momentData N c d))
    (quadrature (evaluatorF true) p M a C E (momentData N c d))

ipra_subst momentData
@[simp] theorem subst_literal {m : ℕ} (σ : Fin n → PTm m) (side : Bool) (p N a b c d : PTm n) :
    Syn.subst σ (literal side p N a b c d) =
      literal side (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by
  cases side <;> simp [literal,signedTime]
ipra_subst evaluatorTerm
ipra_subst source
ipra_subst symmetricGrid

theorem evaluator_at (side : Bool) (p t N c d : PTm n) : Γ ⊢[PRAAx]
    ap3 (evaluatorF side) p t (momentData N c d) ≐ literal side p N (fstT t) (sndT t) c d := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 2)
    (literal side (var 0) (var 2) (fstT (var 1)) (sndT (var 1)) (var 3) (var 4)) p t ![N, c, d]
  simp only [subst_literal, subst_fstT, subst_sndT, Syn.subst_var] at read
  exact read

theorem reflected_row (p t N c d : PTm n) : Γ ⊢[PRAAx]
    ap3 (evaluatorF true) p t (momentData N c d) ≐ ap3 (evaluatorF false) p t (momentData N c d) :=
  (evaluator_at true p t N c d).eqTrans
    ((GaussianMomentReflection.even_row _ N (fstT t) (sndT t) c d).eqTrans (evaluator_at false p t N c d).eqSymm)

theorem reflected_quadrature (p M a C E N c d : PTm n) : Γ ⊢[PRAAx]
    quadrature (evaluatorF true) p M a C E (momentData N c d) ≐
      quadrature (evaluatorF false) p M a C E (momentData N c d) := by
  let x := momentData N c d
  let X := sampleData p M a C E x
  have cells : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      (sampleBody (evaluatorF true)) (sampleBody (evaluatorF false)) M X X := by
    refine .allI (.impI ?_)
    let p' := Syn.shift p
    let M' := Syn.shift M
    let a' := Syn.shift a
    let C' := Syn.shift C
    let E' := Syn.shift E
    let i : PTm (n+1) := var 0
    let x' := momentData (Syn.shift N) (Syn.shift c) (Syn.shift d)
    let Δ := lt i M' :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (sampleBody (evaluatorF true)) i (sampleData p' M' a' C' E' x') ≐
        inst2 (sampleBody (evaluatorF false)) i (sampleData p' M' a' C' E' x') :=
      (GaussianCompactRiemannName.sample_body_at _ i p' M' a' C' E' x').eqTrans
        ((reflected_row p' (grid i M' a' C' E') (Syn.shift N) (Syn.shift c) (Syn.shift d)).eqTrans
          (GaussianCompactRiemannName.sample_body_at _ i p' M' a' C' E' x').eqSymm)
    simpa only [GaussianRationalFiniteSum.termsEqual,X,x,GaussianCompactRiemannName.subst_sampleData,
      subst_momentData,Δ,i,p',M',a',C',E',x',Syn.shift] using e
  exact GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ cells)

theorem symmetric_grid_at (p M a C E N c d : PTm n) : Γ ⊢[PRAAx]
    symmetricGrid p M a C E N c d ≐
      qadd (quadrature (evaluatorF false) p M a C E (momentData N c d))
        (quadrature (evaluatorF false) p M a C E (momentData N c d)) :=
  GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (reflected_quadrature p M a C E N c d)

theorem wrapped_observations (p q t N c d E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEvenMomentIntegrand.source (fstT t) (sndT t) E T c d) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (evaluatorName GaussianEulerQuadraticKernelCompactName.evaluatorF) p (nameData t (fixedData (argument N) two c d)))
      (ap2 (evaluatorName (evaluatorF false)) q (nameData t (momentData N c d))) (unit p+unit q) (unit p*unit q) := by
  exact GaussianCompactRiemannName.wrapped_distance_from_decoded
    (GaussianEulerQuadraticKernelCompactName.evaluator_at p t (argument N) two c d)
    ((evaluator_at false q t N c d).eqTrans (GaussianEvenMomentIntegrand.sample_at q N (fstT t) (sndT t) c d).eqSymm)
    (GaussianEvenMomentIntegrand.original_observations p q N (fstT t) (sndT t) E T c d h)

/-- Recover the pointwise moment input under the time and two precision binders. -/
theorem shifted_point_source (a C E T c d : PTm n) (h : Γ ⊢[PRAAx] source a C E T c d) :
    ((inside (Syn.shift a) (Syn.shift C) (Syn.shift E) (var 0) :: Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
    GaussianEvenMomentIntegrand.source (fstT (var 2)) (sndT (var 2))
      (Syn.shift (Syn.shift (Syn.shift E))) (Syn.shift (Syn.shift (Syn.shift T)))
      (Syn.shift (Syn.shift (Syn.shift c))) (Syn.shift (Syn.shift (Syn.shift d))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift c) (Syn.shift d) :=
    by simpa only [Fm.shift, subst_source, Syn.shift] using h.shift
  have dom : (inside (Syn.shift a) (Syn.shift C) (Syn.shift E) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
      GaussianEvenMomentIntegrand.source (fstT (var 0)) (sndT (var 0)) (Syn.shift E) (Syn.shift T) (Syn.shift c) (Syn.shift d) :=
    .andI (.andI hs.andE₁.andE₁.wk (GaussianEulerCompactAdditivity.domain_of_inside (var 0) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) hs.andE₁.andE₂.andE₁.wk hs.andE₁.andE₁.wk
      hs.andE₁.andE₂.andE₂.wk Prf.hyp0)) hs.andE₂.wk
  simpa [Fm.shift, Syn.shift] using dom.shift.shift

theorem local_agreement (N a C E T c d : PTm n) (h : Γ ⊢[PRAAx] source a C E T c d) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.localAgreement GaussianEulerQuadraticKernelCompactName.evaluatorF
      (evaluatorF false) a C E (fixedData (argument N) two c d) (momentData N c d) := by
  refine .allI (.impI (.allI (.allI ?_)))
  simpa [GaussianCompactClientIndependence.localAgreement, GaussianCompactClientIndependence.agreementBody,
    crossEquivalent, Syn.shift, two, List.map_map] using
    wrapped_observations (var 1) (var 0) (var 2) (Syn.shift (Syn.shift (Syn.shift N)))
      (Syn.shift (Syn.shift (Syn.shift c))) (Syn.shift (Syn.shift (Syn.shift d)))
      (Syn.shift (Syn.shift (Syn.shift E))) (Syn.shift (Syn.shift (Syn.shift T)))
      (shifted_point_source a C E T c d h)

theorem original_grid_distance (p q M a C E T N c d : PTm n) (h : Γ ⊢[PRAAx] source a C E T c d)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerQuadraticKernelCompactName.evaluatorF p M a C E (fixedData (argument N) two c d))
      (quadrature (evaluatorF false) q M a C E (momentData N c d)) (C*(unit p+unit q)) (E*(unit p*unit q)) :=
  GaussianCompactClientIndependence.quadrature_distance _ _ p q M a C E _ _
    (local_agreement N a C E T c d h) h.andE₁.andE₂.andE₁ h.andE₁.andE₁ hM

theorem actual_even_Gaussian_symmetric_grid_double_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (symmetricGrid (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      qadd (quadrature (evaluatorF false) (var 0) (var 1) (var 2) (var 3) (var 4) (momentData (var 5) (var 6) (var 7)))
        (quadrature (evaluatorF false) (var 0) (var 1) (var 2) (var 3) (var 4) (momentData (var 5) (var 6) (var 7)))) :=
  closeUniv 8 (symmetric_grid_at _ _ _ _ _ _ _ _)

theorem actual_even_Gaussian_literal_grid_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 3) (var 4) (var 5) (var 6) (var 8) (var 9) ⟶ le one (var 2) ⟶
      distanceBounded
        (quadrature GaussianEulerQuadraticKernelCompactName.evaluatorF (var 0) (var 2) (var 3) (var 4) (var 5)
          (fixedData (argument (var 7)) two (var 8) (var 9)))
        (quadrature (evaluatorF false) (var 1) (var 2) (var 3) (var 4) (var 5) (momentData (var 7) (var 8) (var 9)))
        ((var 4)*(unit (var 0)+unit (var 1))) ((var 5)*(unit (var 0)*unit (var 1)))) :=
  closeUniv 10 (.impI (.impI (original_grid_distance _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEvenMomentSymmetricGrid
