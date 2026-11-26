import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate

/-!
# Uniform bound for the original Dirichlet sampler

The cutoff at one has a single original row. Its norm and the checked
cofinal truncation rate bound all observations by a constant depending
only on the real-part margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletUniformBound

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerPositiveScalingConstant (inverseF inverseData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletFiniteRate (prefixData budget)
open GaussianGammaZetaDirichletRowDecay (block row_decay)
open GaussianGammaZetaMellinDampedImproper (dirichletF dirichletBody parameters dirichlet_at)
open GaussianNamedFiniteSumFamily (body term_at)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (canonical canonical_congr)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bounded_sum bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianGammaZetaDirichletCofinal.nameF
local notation "cd" => GaussianGammaZetaDirichletCofinal.data

def cap (A : PTm n) : PTm n := budget A+num 6

ipra_subst cap

private theorem block_zero (A : PTm n) : Γ ⊢[PRAAx] block A zero ≐ one :=
  (congrAp2 powF (.eqRefl A) (pw_zero two)).eqTrans (GaussianPolynomialPerturbation.one_power A)

private theorem prefix_at_one (p z R B A : PTm n) :
    Γ ⊢[PRAAx] ap2 dirichletF p (prefixData one z R B A) ≐
      ap2 inverseF (GaussianFastValueCut.exponent one p) (inverseData (shifted z B) B one one) := by
  let t := body inverseF dirichletBody
  let x := parameters (shifted z B) (R+one) B A
  let k := GaussianFastValueCut.exponent one p
  let row := ap2 inverseF k (inverseData (shifted z B) B one one)
  have read := (term_at (Γ := Γ) inverseF dirichletBody zero k x).eqTrans
    (congrAp2 inverseF (.eqRefl _) (dirichlet_at zero (shifted z B) (R+one) B A))
  have first := (GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) inverseF dirichletBody p one x).eqTrans
    ((GaussianRationalFiniteSum.sum_succ t zero (pairT k x)).eqTrans
      (qadd_congr (GaussianRationalFiniteSum.sum_zero t (pairT k x)) read))
  exact first.eqTrans (qzero_add row (GaussianRadiusExponentialName.sample_canonical _ _ _ _))

private theorem canonical_at (p z R B A : PTm n) : Γ ⊢[PRAAx] canonical (ap2 C p (cd z R B A)) := by
  let N := GaussianGammaZetaDirichletCofinal.cutoff A p
  let q := succ p
  let x := parameters (shifted z B) (R+one) B A
  let k := GaussianFastValueCut.exponent N q
  have e := (GaussianGammaZetaDirichletCofinal.sample_at (Γ := Γ) p z R B A).eqTrans
    (GaussianNamedFiniteSumFamily.sample_at inverseF dirichletBody q N x)
  exact canonical_congr e (GaussianRationalFiniteSum.sum_canonical (body inverseF dirichletBody) N (pairT k x))

theorem original_bound (p z R B A : PTm n) (hz : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] bounded (ap2 C p (cd z R B A)) (cap A) one := by
  let k := GaussianFastValueCut.exponent one (zero : PTm n)
  let c := ap2 C p (cd z R B A)
  let x := ap2 dirichletF zero (prefixData one z R B A)
  have b := block_zero (Γ := Γ) A
  have start : Γ ⊢[PRAAx] le (block A zero) one := le_congr b.eqSymm (.eqRefl _) (le_refl one)
  have row := row_decay k z R B A zero one hz start
  have e : Groth.ι (Q.mk Γ (unit (zero : PTm n))) = Groth.ι (Q.mk Γ one) :=
    natEq (pw_zero (Γ := Γ) (two : PTm n))
  have hk := unit_positive (Γ := Γ) k
  have first : Γ ⊢[PRAAx] bounded x (num 4) one := by
    apply bound_congr (prefix_at_one zero z R B A).eqSymm (.eqRefl _) (.eqRefl _)
    apply bounded_radius_mono _ _ _ _ _ ?_ (le_refl one) ?_ row
    · exact GaussianRationalHorner.positive_product _ _
        (GaussianRationalHorner.positive_product _ _ (le_refl one) (unit_positive zero)) hk
    · ipra_le 3*sl hk using
        rw [e]
        ring
  have h := GaussianGammaZetaDirichletCofinal.cutoff_rate one z R B A zero hz start
  have raw := rate_at dirichletF C (prefixData one z R B A) (cd z R B A) (budget A) (unit zero) zero p h
  have hp := unit_positive (Γ := Γ) p
  have hD := denominator_positive (unit zero) zero p (unit_positive (Γ := Γ) (zero : PTm n))
  have near : Γ ⊢[PRAAx] bounded (qsub c x) (budget A+two) one := by
    apply bounded_radius_mono _ _ _ _ _ hD (le_refl one) ?_
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hD raw)
    dsimp only [rateNumerator,rateDenominator]
    ipra_le sl hp using
      rw [e]
      ring
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right x c (canonical_at p z R B A))
    (by unfold cap; ipra_ring) (by ipra_ring)
    (bounded_sum x (qsub c x) (num 4) one (budget A+two) one (le_refl one) (le_refl one) first near)

theorem samples (z R B A : PTm n) (hz : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] sampleBound C (cd z R B A) (cap A) := by
  let sh (x : PTm n) := Syn.shift x
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh] using hz.shift
  refine .allI ?_
  simpa only [sampleBound,Syn.shift,sh,GaussianGammaZetaDirichletCofinal.data,
    GaussianGammaZetaMellinDampedImproper.subst_parameters,subst_cap] using
    original_bound (var 0) (sh z) (sh R) (sh B) (sh A) h

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletUniformBound
