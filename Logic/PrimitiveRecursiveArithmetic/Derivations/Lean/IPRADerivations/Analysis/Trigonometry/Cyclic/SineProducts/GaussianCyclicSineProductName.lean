import IPRADerivations.Analysis.Trigonometry.Cyclic.SineProducts.GaussianCyclicSineProductRatio
import IPRADerivations.Foundations.DyadicGain

/-!
# The named finite cyclic sine normalization

The primitive-recursive product of the original named samples
`sin(πr/m)` for `1 ≤ r < m` is regular under its explicit clock
and cross-equivalent to the literal constant `m/2^(m-1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSineProductName

open_ipra
open GaussianCyclicOriginalSineProduct (originalF budget)
open GaussianCyclicSineProductRatio (ratio original_product_error)
open GaussianCyclicSineProductNormalization (clock clock_later)
open GaussianNamedFiniteProduct (sample)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open LeanProofs.IPRA.Foundations.DyadicGain (amplitude_absorb)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N C x : PTm n) : PTm n := pairT N (pairT C x)
def observation (p N C x : PTm n) : PTm n :=
  sample originalF (clock (p+C) (succ N)) N (GaussianCyclicSineProductSquare.data N x)
def body : PTm 2 := observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def nameF : PR 2 := PTm.toPR body
def productData (N x : PTm n) : PTm n := data N (budget N) x

ipra_subst data

ipra_subst observation [clock]

ipra_subst budget [GaussianCyclicOriginalSineProduct.radius, GaussianCyclicSineProductSquare.normBudget, GaussianCyclicSineProductSquare.radius, GaussianCyclicChordSquare.chordRadius, GaussianCyclicChordSquare.sineSquareRadius, GaussianCyclicChordSquare.twiceSineRadius, GaussianCyclicChordSquare.squareError, GaussianCyclicChordSquare.compareRadius, GaussianCyclicChordSquare.chordError, GaussianCyclicChordSquare.unitError]

ipra_subst productData

theorem name_at (p N C x : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data N C x) ≐ observation p N C x := by
  let d := data N C x
  have first : Γ ⊢[PRAAx] ap2 nameF p d ≐ observation p (fstT d) (fstT (sndT d)) (sndT (sndT d)) := by
    simpa [nameF,body,ap2] using toPR_eq (Γ := Γ) body ![p,d]
  have next := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT d,fstT (sndT d),sndT (sndT d)]) (σ' := ![p,N,C,x]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE)
  exact first.eqTrans (by simpa using next)

private theorem absorb (p N : PTm n) :
    Γ ⊢[PRAAx] le (budget N*unit p) (unit (clock (p+budget N) (succ N))) := by
  let C := budget N
  have a := le_mul_mono (amplitude_absorb (Γ := Γ) C) (le_refl (unit p))
  have b : Γ ⊢[PRAAx] unit (p+C) ≐ unit C*unit p :=
    (pw_add two p C).eqTrans (mul_comm _ _)
  exact le_trans (le_congr (.eqRefl _) b.eqSymm a) (unit_monotone (clock_later (p+C) (succ N)))

theorem envelope (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (productData N x)) (ratio N) one (unit p) := by
  let C := budget N
  let t := clock (p+C) (succ N)
  have h := distance_symmetric (Γ := Γ) _ _ _ _ (unit_positive t) (original_product_error (p+C) N x)
  exact distance_congr (name_at p N C x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive t) (unit_positive p)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (absorb p N)) h)

private theorem cross_query (p q N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (productData N x)) (ap2 constantF q (ratio N))
      (unit p+unit q) (unit p*unit q) := by
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have rate : Γ ⊢[PRAAx] le (one*(unit p*unit q)) ((unit p+unit q)*unit p) := by
    have h := le_mul_mono (le_add_left (Γ := Γ) (unit q) (unit p)) (le_refl (unit p))
    exact le_congr (by ipra_ring) (.eqRefl _) h
  exact distance_congr (.eqRefl _) (constant_at q _).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hP (positive_product _ _ hP hQ) rate (envelope p N x))

theorem normalization (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF (productData N x) (ratio N) := by
  refine .allI (.allI ?_)
  simpa [crossEquivalent,Syn.shift,ratio] using
    cross_query (var 1) (var 0) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x))

theorem name_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN nameF (productData N x) :=
  cross_trans nameF constantF nameF _ _ _
    (normalization N x) (cross_symm _ _ _ _ (normalization N x))

theorem actual_original_cyclic_sine_product_name_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent nameF constantF (productData (var 1) (var 0)) (ratio (var 1))) :=
  closeUniv 2 (normalization _ _)

end LeanProofs.IPRA.Analysis.GaussianCyclicSineProductName
