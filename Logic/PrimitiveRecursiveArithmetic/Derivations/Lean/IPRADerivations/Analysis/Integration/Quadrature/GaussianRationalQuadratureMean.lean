import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentCosineLaplace
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Exact finite quadrature of the mean of two panel programs

The two panel programs use different data on a common mesh. The
encoded mean of the two original finite sums is the finite sum of
pointwise means and keeps the actual quadrature weight.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureMean

open_ipra
open GaussianBinetArctangentCosineLaplace (mean)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def firstBody (f : PTm 2) : PTm 2 := inst2 f (var 0) (fstT (var 1))
def secondBody (g : PTm 2) : PTm 2 := inst2 g (var 0) (sndT (var 1))
def body (f g : PTm 2) : PTm 2 := multiplyBody (GaussianRationalFiniteSum.addBody (firstBody f) (secondBody g))
def data (x y : PTm n) : PTm n := pairT (fraction one two) (pairT x y)

ipra_subst data [one, two]

private theorem first_entry (f : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    inst2 (firstBody f) i (pairT x y) ≐ inst2 f i x := by
  have e : inst2 (firstBody f) i (pairT x y) = inst2 f i (fstT (pairT x y)) := by
    simp only [firstBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  rw [e]
  exact congrInst2 f (.eqRefl _) (fst_pair _ _)

private theorem second_entry (g : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    inst2 (secondBody g) i (pairT x y) ≐ inst2 g i y := by
  have e : inst2 (secondBody g) i (pairT x y) = inst2 g i (sndT (pairT x y)) := by
    simp only [secondBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  rw [e]
  exact congrInst2 g (.eqRefl _) (snd_pair _ _)

theorem entry (f g : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    inst2 (body f g) i (data x y) ≐ mean (inst2 f i x) (inst2 g i y) := by
  refine (multiply_body_at (GaussianRationalFiniteSum.addBody (firstBody f) (secondBody g)) (fraction one two) i (pairT x y)).eqTrans ?_
  rw [GaussianRationalFiniteSum.inst2_addBody]
  exact qmul_congr (.eqRefl _) (qadd_congr (first_entry f i x y) (second_entry g i x y))

theorem mean_sum (f g : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx]
    sum (body f g) N (data x y) ≐ mean (sum f N x) (sum g N y) := by
  have hf : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (firstBody f) f N (pairT x y) x := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,subst_pairT] using first_entry f (var 0) (Syn.shift x) (Syn.shift y)
  have hg : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (secondBody g) g N (pairT x y) y := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,subst_pairT] using second_entry g (var 0) (Syn.shift x) (Syn.shift y)
  exact (sum_multiply (GaussianRationalFiniteSum.addBody (firstBody f) (secondBody g)) (fraction one two) N (pairT x y)).eqTrans
    (qmul_congr (.eqRefl _) ((GaussianRationalFiniteSum.sum_add (firstBody f) (secondBody g) N (pairT x y)).eqTrans
      (qadd_congr (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ hf) (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ hg))))

theorem mean_product (w x y : PTm n) : Γ ⊢[PRAAx] mean (qmul w x) (qmul w y) ≐ qmul w (mean x y) :=
  (qmul_congr (.eqRefl _) (qmul_add w x y).eqSymm).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative _ _) (.eqRefl _)).eqTrans (qmul_associative _ _ _)))

theorem left_mean (f g : PTm 2) (N x y C E : PTm n) : Γ ⊢[PRAAx]
    mean (leftSum f N x C E) (leftSum g N y C E) ≐ leftSum (body f g) N (data x y) C E :=
  (mean_product (weight C E N) (sum f N x) (sum g N y)).eqTrans
    (qmul_congr (.eqRefl _) (mean_sum f g N x y).eqSymm)

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureMean
