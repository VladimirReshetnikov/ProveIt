import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadShift
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale

/-!
# The unnormalized Euler denominator

The product of the original factors (z/B+j) for (0leq jleq N)
equals (N!) times the maintained Euler head. The equation holds
at poles as well, since it uses no cancellation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerDenominator

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianGammaEulerHead (factor head head_zero head_succ run program_at)
open GaussianGammaEulerHeadLower (translated translated_zero factor_represents)
open GaussianGammaEulerHeadShift (linear)
open GaussianRationalFiniteProduct (qprod product_succ)
open GaussianRationalHorner (canonical_unique represents_congr represents_rescale positive_product
  ofGaussian ofGaussian_canonical ofGaussian_represents qmul qmul_canonical)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natScale_represents natScale_canonical
  natScale_as_product)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRootAlgebra (equal_of_values re_scale im_scale)
open Products (fact)
export GaussianGammaEulerHeadShift (linear_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linearBody : PTm 2 := linear (fstT (var 1)) (sndT (var 1)) (var 0)
def denominator (z B K : PTm n) : PTm n := qprod linearBody K (pairT z B)

ipra_subst denominator

theorem linear_at (i z B : PTm n) : Γ ⊢[PRAAx] inst2 linearBody i (pairT z B) ≐ linear z B i := by
  simpa [linearBody,inst2,inst3] using
    congrInst3 (linear (var 0) (var 1) (var 2)) (Γ := Γ) (fst_pair z B) (snd_pair z B) (.eqRefl i)

theorem denominator_succ (z B K : PTm n) : Γ ⊢[PRAAx]
    denominator z B (succ K) ≐ qmul (denominator z B K) (linear z B K) :=
  (product_succ _ _ _).eqTrans (qmul_congr (.eqRefl _) (linear_at K z B))

theorem natural_one : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ qone :=
  GaussianRationalNaturalScale.natural_point_one

theorem natural_multiply (a b : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a*b) :=
  GaussianRationalNaturalScale.natural_point_mul a b

theorem factor_scaled (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (naturalPoint (succ i)) (factor i z B) ≐ linear z B (succ i) := by
  let t := succ i
  let a := translated z B t
  have ht := zero_lt_succ (Γ := Γ) i
  have hD := positive_product B t hB ht
  have left := natScale_represents t (factor i z B) a (B*t) hD (factor_represents i z B hB)
  have right := represents_rescale (linear z B t) a B t (ofGaussian_represents a B hB)
  exact (natScale_as_product t (factor i z B)).eqSymm.eqTrans
    (canonical_unique _ _ _ _ (natScale_canonical _ _) (ofGaussian_canonical _ _ hB) hD left right)

theorem natural_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] naturalPoint a ≐ naturalPoint b :=
  GaussianRationalHorner.real_fraction_congr h (.eqRefl _)

def normalization (z B N : PTm n) : Fm PTm n :=
  denominator z B (succ N) ≐ qmul (naturalPoint (fact N)) (head z B N)

ipra_subst normalization [fact]

theorem normalization_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] normalization z B zero := by
  have h : Γ ⊢[PRAAx] naturalPoint (fact (zero : PTm n)) ≐ qone :=
    (natural_congr (fact_zero zero)).eqTrans natural_one
  have drop : Γ ⊢[PRAAx] qmul qone (ofGaussian z B) ≐ ofGaussian z B :=
    (qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ (ofGaussian_canonical _ _ hB))
  have left := (denominator_succ z B zero).eqTrans
    ((qmul_congr (GaussianRationalFiniteProduct.product_zero _ _) (linear_zero z B hB)).eqTrans drop)
  have right := (qmul_congr h (head_zero z B hB)).eqTrans drop
  exact left.eqTrans right.eqSymm

theorem normalization_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] normalization z B N) : Γ ⊢[PRAAx] normalization z B (succ N) := by
  have index : Γ ⊢[PRAAx] naturalPoint (fact N*succ N) ≐ naturalPoint (fact (succ N)) :=
    natural_congr (fact_succ N zero).eqSymm
  exact (denominator_succ z B (succ N)).eqTrans
    ((qmul_congr ih (factor_scaled z B N hB).eqSymm).eqTrans
      ((qmul_shuffle _ _ _ _).eqTrans
        (qmul_congr ((natural_multiply _ _).eqTrans index) (head_succ z B N).eqSymm)))

theorem denominator_normalization (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] normalization z B N := by
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift,one] using hB.shift
  have all : Γ ⊢[PRAAx] .all (normalization (Syn.shift z) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_normalization]
    · exact normalization_zero z B hB
    · exact normalization_step _ _ _ hb.wk Prf.hyp0
  simpa only [subst_normalization,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem original_euler_denominator_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ denominator (var 0) (var 1) (succ (var 2)) ≐
      qmul (naturalPoint (fact (var 2))) (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI ((denominator_normalization _ _ _ Prf.hyp0).eqTrans
    (qmul_congr (.eqRefl _) (program_at _ _ _).eqSymm)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerDenominator
