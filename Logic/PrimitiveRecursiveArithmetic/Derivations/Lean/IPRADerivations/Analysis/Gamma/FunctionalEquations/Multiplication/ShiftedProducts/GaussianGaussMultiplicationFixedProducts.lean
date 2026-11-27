import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Cutoffs.GaussianGaussEulerCutoffUniform
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Limits.GaussianGaussMultiplicationCofinalRows

/-!
# Fixed-cutoff Gauss products and their literal observations

The same fixed Euler programs used in the finite identity admit regular
product names with uniform row radii. Their normalized observations
are close to the literal fixed-cutoff products at the requested clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationFixedProducts

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGaussEulerCutoffUniform (euler_regular uniform_succ_error retimed_distance)
open GaussianNamedFiniteProduct (sample rowDistance rowBoundsAt radius amplification)
open GaussianNamedFiniteProductName (rowBounds rowRegular)
open GaussianRootApproximationWitness (pointBounds)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "SE" => GaussianGammaGaussEulerProduct.rowF
local notation "RE" => GaussianGammaGaussReferenceEulerProduct.rowF
local notation "SData" => GaussianGammaGaussEulerProduct.rowData
local notation "RData" => GaussianGammaGaussReferenceEulerProduct.rowData
local notation "SRadius" => GaussianGammaGaussEulerProduct.rowRadius
local notation "RRadius" => GaussianGammaGaussReferenceEulerProduct.rowRadius
local notation "SGuard" => GaussianGammaGaussEulerProduct.threshold
local notation "RGuard" => GaussianGammaGaussReferenceEulerProduct.threshold

abbrev shiftedF : PR 2 := GaussianNamedFiniteProductName.nameF SE
abbrev referenceF : PR 2 := GaussianNamedFiniteProductName.nameF RE
def shiftedData (z R B m d N : PTm n) : PTm n := GaussianNamedFiniteProductName.data m (SRadius R m d) one (SData z R B m d N)
def referenceData (m N : PTm n) : PTm n := GaussianNamedFiniteProductName.data m (RRadius m) one (RData m N)

ipra_subst shiftedData [one]
ipra_subst referenceData [one]

private theorem shifted_row_bound_at (s p r z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) (hn : Γ ⊢[PRAAx] le (SGuard s R m a d) N) :
    Γ ⊢[PRAAx] bounded (ap3 SE p r (SData z R B m d N)) (SRadius R m d) one := by
  have gamma := GaussianGammaGaussShiftedProduct.row_bound_at p r z R B m a d h hr
  have dist := uniform_succ_error s p (GaussianGammaEulerDenominatorGrouping.shiftedNumerator z B m r) (R+one) (B*m) a (d*m) N
    (GaussianGammaGaussShiftedProduct.row_source z R B m r a d h hr) hn
  have exactDist := distance_congr (GaussianGammaGaussEulerProduct.row_at p r z R B m d N).eqSymm
    (GaussianGammaGaussShiftedProduct.row_at p r z R B m d).eqSymm (.eqRefl _) (.eqRefl _) dist
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold GaussianGammaGaussEulerProduct.rowRadius; ipra_ring)
    (one_mul _) (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) exactDist gamma)

private theorem reference_row_bound_at (s p r m N : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hn : Γ ⊢[PRAAx] le (RGuard s m) N) :
    Γ ⊢[PRAAx] bounded (ap3 RE p r (RData m N)) (RRadius m) one := by
  have gamma := GaussianGammaGaussReferenceProduct.row_bound_at p r m hr
  have dist := uniform_succ_error s p (GaussianGammaGaussReferenceProduct.argument r) one m one m N
    (GaussianGammaGaussReferenceProduct.row_source r m hr) hn
  have exactDist := distance_congr (GaussianGammaGaussReferenceEulerProduct.row_at p r m N).eqSymm
    (GaussianGammaGaussReferenceProduct.row_at p r m).eqSymm (.eqRefl _) (.eqRefl _) dist
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold GaussianGammaGaussReferenceEulerProduct.rowRadius; ipra_ring)
    (one_mul _) (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) exactDist gamma)

theorem shifted_row_bounds (s z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le (SGuard s R m a d) N) : Γ ⊢[PRAAx] rowBounds SE m (SRadius R m d) (SData z R B m d N) := by
  refine .allI (.allI (.impI ?_))
  let lift (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := lt (var 0) (lift m) :: (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using h.shift.shift.wk
  have hsN : Δ ⊢[PRAAx] le (SGuard (lift s) (lift R) (lift m) (lift a) (lift d)) (lift N) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using hn.shift.shift.wk
  simpa [Δ,lift,rowBounds,rowBoundsAt,Syn.shift] using shifted_row_bound_at
    (lift s) (var 1) (var 0) (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) (lift N)
    hs (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (lift m)) hsN

theorem reference_row_bounds (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (RGuard s m) N) :
    Γ ⊢[PRAAx] rowBounds RE m (RRadius m) (RData m N) := by
  refine .allI (.allI (.impI ?_))
  let lift (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := lt (var 0) (lift m) :: (Γ.map Fm.shift).map Fm.shift
  have hsN : Δ ⊢[PRAAx] le (RGuard (lift s) (lift m)) (lift N) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using hn.shift.shift.wk
  simpa [Δ,lift,rowBounds,rowBoundsAt,Syn.shift] using reference_row_bound_at
    (lift s) (var 1) (var 0) (lift m) (lift N) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (lift m)) hsN

private theorem shifted_row_distance (s p q r z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) (hn : Γ ⊢[PRAAx] le (SGuard s R m a d) N) :
    Γ ⊢[PRAAx] distanceBounded (ap3 SE p r (SData z R B m d N)) (ap3 SE q r (SData z R B m d N))
      (one*(unit p+unit q)) (unit p*unit q) := by
  have base := euler_regular s (GaussianGammaEulerDenominatorGrouping.shiftedNumerator z B m r) (R+one) (B*m) a (d*m) N
    (GaussianGammaGaussShiftedProduct.row_source z R B m r a d h hr) hn
  exact distance_congr (GaussianGammaGaussEulerProduct.row_at p r z R B m d N).eqSymm
    (GaussianGammaGaussEulerProduct.row_at q r z R B m d N).eqSymm (.eqRefl _) (.eqRefl _)
    (retimed_distance eulerF p q _ base)

private theorem reference_row_distance (s p q r m N : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hn : Γ ⊢[PRAAx] le (RGuard s m) N) :
    Γ ⊢[PRAAx] distanceBounded (ap3 RE p r (RData m N)) (ap3 RE q r (RData m N))
      (one*(unit p+unit q)) (unit p*unit q) := by
  have base := euler_regular s (GaussianGammaGaussReferenceProduct.argument r) one m one m N
    (GaussianGammaGaussReferenceProduct.row_source r m hr) hn
  exact distance_congr (GaussianGammaGaussReferenceEulerProduct.row_at p r m N).eqSymm
    (GaussianGammaGaussReferenceEulerProduct.row_at q r m N).eqSymm (.eqRefl _) (.eqRefl _)
    (retimed_distance eulerF p q _ base)

theorem shifted_row_regular (s z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le (SGuard s R m a d) N) : Γ ⊢[PRAAx] rowRegular SE m one (SData z R B m d N) := by
  refine .allI (.allI (.allI (.impI ?_)))
  let lift (u : PTm n) := Syn.shift (Syn.shift (Syn.shift u))
  let Δ := lt (var 0) (lift m) :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using h.shift.shift.shift.wk
  have hsN : Δ ⊢[PRAAx] le (SGuard (lift s) (lift R) (lift m) (lift a) (lift d)) (lift N) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using hn.shift.shift.shift.wk
  simpa [Δ,lift,rowRegular,rowDistance,Syn.shift,one] using shifted_row_distance
    (lift s) (var 2) (var 1) (var 0) (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) (lift N)
    hs (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (lift m)) hsN

theorem reference_row_regular (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (RGuard s m) N) :
    Γ ⊢[PRAAx] rowRegular RE m one (RData m N) := by
  refine .allI (.allI (.allI (.impI ?_)))
  let lift (u : PTm n) := Syn.shift (Syn.shift (Syn.shift u))
  let Δ := lt (var 0) (lift m) :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hsN : Δ ⊢[PRAAx] le (RGuard (lift s) (lift m)) (lift N) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using hn.shift.shift.shift.wk
  simpa [Δ,lift,rowRegular,rowDistance,Syn.shift,one] using reference_row_distance
    (lift s) (var 2) (var 1) (var 0) (lift m) (lift N) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (lift m)) hsN

theorem shifted_regular (s z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le (SGuard s R m a d) N) : Γ ⊢[PRAAx] pointCN shiftedF (shiftedData z R B m d N) :=
  GaussianNamedFiniteProductName.name_regular _ _ _ _ _
    (shifted_row_bounds s z R B m a d N h hn) (shifted_row_regular s z R B m a d N h hn)

theorem reference_regular (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (RGuard s m) N) :
    Γ ⊢[PRAAx] pointCN referenceF (referenceData m N) :=
  GaussianNamedFiniteProductName.name_regular _ _ _ _ _ (reference_row_bounds s m N hn) (reference_row_regular s m N hn)

theorem normalized_bounds (f : PR 3) (m R L x : PTm n) (h : Γ ⊢[PRAAx] rowBounds f m R x) :
    Γ ⊢[PRAAx] pointBounds (GaussianNamedFiniteProductName.nameF f) (radius R m) (GaussianNamedFiniteProductName.data m R L x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowBounds f (Syn.shift m) (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [pointBounds,Syn.shift] using
    GaussianNamedFiniteProductName.name_bound f (var 0) (Syn.shift m) (Syn.shift R) (Syn.shift L) (Syn.shift x) hs

theorem normalized_error (f : PR 3) (p m R x : PTm n) (hb : Γ ⊢[PRAAx] rowBounds f m R x)
    (hr : Γ ⊢[PRAAx] rowRegular f m one x) :
    Γ ⊢[PRAAx] distanceBounded (sample f p m x)
      (ap2 (GaussianNamedFiniteProductName.nameF f) p (GaussianNamedFiniteProductName.data m R one x))
      (two*amplification R m) (unit p) := by
  let t := GaussianNamedFiniteProductName.clock m R one p
  let A := amplification R m
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have both := positive_product _ _ hp ht
  have grow := GaussianExponentialReference.unit_monotone (GaussianNamedFiniteProductName.clock_later (Γ := Γ) m R one p)
  have raw := GaussianNamedFiniteProduct.sample_distance f f p t m R (one*(unit p+unit t)) (unit p*unit t) x x both
    (GaussianNamedFiniteProductName.bounds_at f p m R x hb) (GaussianNamedFiniteProductName.bounds_at f t m R x hb)
    (GaussianNamedFiniteProductName.regular_rows_at f p t m one x hr)
  have budget : Γ ⊢[PRAAx] le ((A*(one*(unit p+unit t)))*unit p) ((two*A)*(unit p*unit t)) := by
    ipra_le 𝔞 A*𝔞 (unit p)*sl grow
  exact distance_congr (.eqRefl _) (GaussianNamedFiniteProductName.name_at f p m R one x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ both hp budget raw)

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationFixedProducts
