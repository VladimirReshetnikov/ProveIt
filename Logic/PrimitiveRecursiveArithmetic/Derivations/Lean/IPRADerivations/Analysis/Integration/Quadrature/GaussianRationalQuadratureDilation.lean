import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayQuadrature

/-!
# Exact positive rational dilation of the original finite quadrature

The actual pullback evaluator calls the unchanged client at the encoded
time (c*a)/(d*b). Its affine grid is literally the grid on the dilated
interval after native distributivity; the original rational weight gives
the exact Jacobian c/d. No evaluator properness, continuity or integral
identity is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureDilation

open_ipra
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def timeMap (c d t : PTm n) : PTm n := pairT (c*fstT t) (d*sndT t)
def pullData (c d x : PTm n) : PTm n := pairT c (pairT d x)
def pullTerm (F : PR 3) (p t y : PTm n) : PTm n :=
  ap3 F p (timeMap (fstT y) (fstT (sndT y)) t) (sndT (sndT y))
def pullF (F : PR 3) : PR 3 := PTm.toPR (pullTerm F (var 0) (var 1) (var 2))
def source (c d E N : PTm n) : Fm PTm n := le one c ⋏ (le one d ⋏ (le one E ⋏ le one N))

ipra_subst timeMap
ipra_subst pullData
ipra_subst pullTerm
ipra_subst source

theorem pull_at (F : PR 3) (p t c d x : PTm n) : Γ ⊢[PRAAx]
    ap3 (pullF F) p t (pullData c d x) ≐ ap3 F p (timeMap c d t) x := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 2)
    (ap3 F (var 0) (timeMap (var 2) (var 3) (var 1)) (var 4)) p t ![c, d, x]
  simp only [subst_ap3, subst_timeMap, Syn.subst_var] at read
  exact read

theorem pull_fraction_at (F : PR 3) (p a b c d x : PTm n) : Γ ⊢[PRAAx]
    ap3 (pullF F) p (pairT a b) (pullData c d x) ≐ ap3 F p (pairT (c*a) (d*b)) x :=
  (pull_at F p (pairT a b) c d x).eqTrans
    (congrAp3 F (.eqRefl _) (congrPairT (congrMul (.eqRefl _) (fst_pair _ _)) (congrMul (.eqRefl _) (snd_pair _ _))) (.eqRefl _))

/-- These are identical actual evaluator calls after native arithmetic;
no equality of merely represented times is used. -/
theorem cell_at (F : PR 3) (i p N c d a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody F) i (sampleData p N (c*a) (c*C) (d*E) x) ≐
      inst2 (sampleBody (pullF F)) i (sampleData p N a C E (pullData c d x)) :=
  (sample_body_at F i p N (c*a) (c*C) (d*E) x).eqTrans
    ((congrAp3 F (.eqRefl _) (congrPairT (by ipra_ring) (by ipra_ring)) (.eqRefl _)).eqTrans
      ((pull_fraction_at F p (a*N+C*i) (E*N) c d x).eqSymm.eqTrans
        (sample_body_at (pullF F) i p N a C E (pullData c d x)).eqSymm))

theorem weight_factor (c d C E N : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] le one E) (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (fraction c d) (weight C E N) ≐ weight (c*C) (d*E) N := by
  have en := positive_product _ _ he hn
  have den := positive_product _ _ hd en
  exact (qmul_congr (fraction_is_radius_point c d hd) (fraction_is_radius_point C (E*N) en)).eqTrans
    ((GaussianDominantPairAlgebra.radius_multiply c d C (E*N) hd en).eqTrans
      ((fraction_is_radius_point (c*C) (d*(E*N)) den).eqSymm.eqTrans
        (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring))))

/-- The original finite quadrature satisfies the exact rational change
of variables t=(c/d)u at every original evaluation precision and count. -/
theorem original_quadrature_dilation (F : PR 3) (p N c d a C E x : PTm n)
    (hs : Γ ⊢[PRAAx] source c d E N) : Γ ⊢[PRAAx]
    quadrature F p N (c*a) (c*C) (d*E) x ≐
      qmul (fraction c d) (quadrature (pullF F) p N a C E (pullData c d x)) := by
  let f := sampleBody F
  let g := sampleBody (pullF F)
  let X := sampleData p N (c*a) (c*C) (d*E) x
  let Y := sampleData p N a C E (pullData c d x)
  have same : Γ ⊢[PRAAx] termsEqual f g N X Y := by
    refine .allI (.impI ?_)
    simpa [termsEqual,f,g,X,Y,Syn.shift] using
      cell_at (Γ := _ :: Γ.map Fm.shift) F (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x)
  have finite := GaussianRationalFiniteSum.sum_congr_bounded f g N X Y same
  exact (qmul_congr (weight_factor c d C E N hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂).eqSymm finite).eqTrans
    (GaussianReciprocalHorner.qmul_associative (fraction c d) (weight C E N) (sum g N Y))

theorem actual_original_positive_rational_quadrature_dilation_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 6) (var 1) ⟶
      quadrature F (var 0) (var 1) (var 2*var 4) (var 2*var 5) (var 3*var 6) (var 7) ≐
        qmul (fraction (var 2) (var 3)) (quadrature (pullF F) (var 0) (var 1) (var 4) (var 5) (var 6)
          (pullData (var 2) (var 3) (var 7)))) :=
  closeUniv 8 (.impI (original_quadrature_dilation F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureDilation
