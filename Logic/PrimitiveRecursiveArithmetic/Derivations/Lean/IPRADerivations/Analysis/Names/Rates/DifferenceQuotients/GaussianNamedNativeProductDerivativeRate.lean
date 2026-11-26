import IPRADerivations.Analysis.Names.Differences.GaussianNamedIncrementProductRule
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Quantitative product rule for actual native divided differences

The exact product split evaluates the first factor at the shifted
input in one summand. Its continuation to the derivative uses an
independent continuity rate for that factor. All errors have the
same supplied denominator and preserve two observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianNamedNativeProductDerivativeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

def derivativeF (I G DI DG : PR 2) : PR 2 := addF (multiplyF DG I) (multiplyF G DI)
def derivativeData (I G DI DG : PR 2) (i g u v : PTm n) : PTm n :=
  addData (multiplyData DG I v i) (multiplyData G DI g u)

def numerator (A C L P M N : PTm n) : PTm n := M*A+P*L+N*C

private theorem sample_bound_regular (F : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] sampleBound F x (U F x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN F (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  simpa only [sampleBound,Syn.shift,GaussianNameBounds.subst_U] using
    GaussianNameBounds.sample_bound F (Syn.shift x) (var 0) hs

theorem rate (I G DI DG : PR 2) (i1 i0 g1 g0 u v h B A C L E P M N : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I i1) (hi0 : Γ ⊢[PRAAx] pointCN I i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G g1) (hg0 : Γ ⊢[PRAAx] pointCN G g0)
    (hu : Γ ⊢[PRAAx] pointCN DI u) (hv : Γ ⊢[PRAAx] pointCN DG v)
    (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B)
    (hE : Γ ⊢[PRAAx] le one E)
    (hp : Γ ⊢[PRAAx] sampleBound DG v P) (hm : Γ ⊢[PRAAx] sampleBound I i1 M)
    (hn : Γ ⊢[PRAAx] sampleBound G g0 N)
    (hqg : Γ ⊢[PRAAx] independentRate (QF G G) DG (qd G G g1 g0 h B) v A E)
    (hqi : Γ ⊢[PRAAx] independentRate (QF I I) DI (qd I I i1 i0 h B) u C E)
    (hi : Γ ⊢[PRAAx] independentRate I I i1 i0 L E) :
    Γ ⊢[PRAAx] independentRate (QF (multiplyF I G) (multiplyF I G)) (derivativeF I G DI DG)
      (qd (multiplyF I G) (multiplyF I G) (multiplyData I G i1 g1) (multiplyData I G i0 g0) h B)
      (derivativeData I G DI DG i0 g0 u v) (numerator A C L P M N) E := by
  let F := QF G G
  let H := QF I I
  let x := qd G G g1 g0 h B
  let y := qd I I i1 i0 h B
  let W := U H y
  have hx := GaussianNamedDifferenceQuotient.name_regular G G g1 g0 h B (.andI hg1 (.andI hg0 hs))
  have hy := GaussianNamedDifferenceQuotient.name_regular I I i1 i0 h B (.andI hi1 (.andI hi0 hs))
  have left := GaussianNamedMultiplyRate.independent_rate F I DG I x i1 v i0
    A E L E M P hE hE hx hi1 hv hi0 hm hp hqg hi
  have right := GaussianNamedMultiplyRate.independent_rate G H G DI g0 y g0 u
    zero one C E W N (le_refl one) hE hg0 hy hg0 hu (sample_bound_regular H y hy)
    hn (GaussianNamedAddRate.self_rate G g0 hg0) hqi
  have joined := GaussianNamedAddRate.independent_rate (multiplyF F I) (multiplyF G H)
    (multiplyF DG I) (multiplyF G DI) (multiplyData F I x i1) (multiplyData G H g0 y)
    (multiplyData DG I v i0) (multiplyData G DI g0 u)
    _ _ _ _ (positive_product _ _ hE hE) (positive_product _ _ (le_refl one) hE) left right
  have narrow := GaussianNamedRateRadius.weaken _ _ _ _ _ _ (numerator A C L P M N) E
    (positive_product _ _ (positive_product _ _ hE hE) (positive_product _ _ (le_refl one) hE)) hE
    (by
      apply le_of_eq_add (d := zero)
      change Γ ⊢[PRAAx] (M*A+P*L+N*C)*(E*E*(one*E)) ≐
        ((M*A*E+P*L*E)*(one*E)+(W*zero*E+N*C*one)*(E*E))*E+zero
      ipra_ring) joined
  have rule := GaussianNamedIncrementProductRule.native_product_rule I I G G i1 i0 g1 g0 h B hi1 hi0 hg1 hg0
  have reorder := GaussianNamedGammaHalfShift.add_cross (multiplyF I F) (multiplyF F I)
    (multiplyF G H) (multiplyF G H) (multiplyData I F i1 x) (multiplyData F I x i1)
    (multiplyData G H g0 y) (multiplyData G H g0 y) (multiply_fast I F i1 x hi1 hx)
    (multiply_fast F I x i1 hx hi1) (multiply_fast G H g0 y hg0 hy) (multiply_fast G H g0 y hg0 hy)
    (GaussianNameRingLaws.multiply_commutative I F i1 x hi1 hx)
    (cross_refl _ _ (multiply_fast G H g0 y hg0 hy))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hE narrow
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ rule reorder)
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (multiply_fast DG I v i0 hv hi0)
      (multiply_fast G DI g0 u hg0 hu)))

end LeanProofs.IPRA.Analysis.GaussianNamedNativeProductDerivativeRate
