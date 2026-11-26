import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalRealSamples
import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentWholeLineValue
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedBoundedProductObservation

/-!
# Halving a regular Gaussian name

Use the exact rational coefficient (1/2) and the existing multiplication
of names. Two copies add to the original name, with no shared-clock
assumption. Halving also preserves literal real samples.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedHalf

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left right_distributive)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianRationalHorner (qmul_canonical canonical_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalGaussianEmbedding (axis_multiply axis_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianEulerSquareFactorInverse.half

def nameF (f : PR 2) : PR 2 := multiplyF constantF f
def data (f : PR 2) (x : PTm n) : PTm n := multiplyData constantF f H x

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (data f x) = data f (Syn.subst σ x) := by
  simp [data,GaussianEulerSquareFactorInverse.half,GaussianPositiveRationalLogarithm.fraction]

theorem regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x) :=
  multiply_fast constantF f H x (constant_regular _) hf

theorem proper (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (e : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x) (data g y) := by
  have h := constant_regular (Γ := Γ) (H : PTm n)
  exact multiply_cross constantF constantF f g H H x y h h hf hg (cross_refl _ _ h) e

theorem double (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF (nameF f) (nameF f)) f (addData (data f x) (data f x)) x := by
  have hh := constant_regular (Γ := Γ) (H : PTm n)
  have split := right_distributive constantF constantF f H H x hh hh hf
  have replace := multiply_cross (addF constantF constantF) oneF f f (addData H H) x x x
    (add_fast _ _ _ _ hh hh) (one_fast x) hf hf
    (GaussianEvenMomentWholeLineValue.half_sum_cross x) (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ replace (multiply_one_left f x hf))

theorem real (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] realSamples (nameF f) (data f x) := by
  let Δ := Γ.map Fm.shift
  let y := Syn.shift x
  let p : PTm (n + 1) := var 0
  let k := GaussianNamedBoundedProductObservation.clock constantF f p H y
  have hs : Δ ⊢[PRAAx] realSamples f y := by simpa [Δ,y,Fm.shift,Syn.shift] using hf.shift
  have e := (GaussianNamedBoundedProductObservation.name_at (Γ := Δ) constantF f p H y).eqTrans
    (qmul_congr (constant_at k H) (.eqRefl _))
  have h := axis_multiply H (ap2 f k y)
    (axis_congr (GaussianEulerDecayOrder.fraction_embedding (Γ := Δ) one two RationalAlgebra.two_positive)
      (RationalGaussianEmbedding.embed_axis _))
    (real_sample_at f y k hs).andE₂
  refine .allI ?_
  have ed : Syn.shift (data f x) = data f y := subst_data _ f x
  rw [ed]
  exact .andI (canonical_congr e (qmul_canonical _ _)) (axis_congr e.eqSymm h)

theorem conjugate_fixed (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF f) f x x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular f x hf) hf
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  exact .allI ((GaussianNameConjugation.sample_at f (var 0) (Syn.shift x)).eqTrans
    (GaussianEulerVerticalRealSamples.real_input_fixed f (var 0) (Syn.shift x) hs))

theorem actual_named_halves_sum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN f (var 0) ⟶ crossEquivalent (addF (nameF f) (nameF f)) f
        (addData (data f (var 0)) (data f (var 0))) (var 0)) :=
  closeUniv 1 (.impI (double f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedHalf
