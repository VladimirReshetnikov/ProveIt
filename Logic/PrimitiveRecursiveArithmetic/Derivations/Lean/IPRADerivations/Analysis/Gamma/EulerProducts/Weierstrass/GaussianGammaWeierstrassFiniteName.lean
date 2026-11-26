import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassFactors
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference

/-!
# Regular name for the factor-by-factor Weierstrass prefix

The original finite program evaluates each `(1+z/k) exp(-z/k)` separately
and folds the resulting rational samples. Its computed precision modulus
comes from the literal finite comparison. The normalized program agrees
at independent precisions with the original Euler head multiplied by a
single exponential of the exact negative harmonic argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassFiniteName

open_ipra
open GaussianGammaWeierstrassFactors
  (width errorBudget literalPrefix foldedPrefix harmonicArgument harmonic_argument_bound prefix_comparison scaled_distance)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianScalarExponentialProductTail (rectangleCutoff)
open GaussianExponentialReference (finite_reference index_below_rectangle)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z R B N : PTm n) : PTm n := pairT z (pairT R (pairT B N))

def rawPoint (p z R B N : PTm n) : PTm n := literalPrefix z B (rectangleCutoff (width R N) p) N

def rawF : PR 2 := PTm.toPR (rawPoint (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))))

def exponentF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def exponentData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data (width R N) (harmonicArgument z B N)
def foldedF : PR 2 := GaussianNameArithmetic.multiplyF constantF exponentF
def foldedData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF exponentF
  (GaussianGammaEulerHead.head z B N) (exponentData z R B N)
def foldedRawF : PR 2 := GaussianNameArithmetic.multiplyRawF constantF exponentF
def foldedRawData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.data (GaussianGammaEulerHead.head z B N)
  (exponentData z R B N)
def foldedModulus (z R B N : PTm n) : PTm n := GaussianNameArithmetic.multiplyModulus constantF exponentF
  (GaussianGammaEulerHead.head z B N) (exponentData z R B N)
def comparisonBudget (R N : PTm n) : PTm n := errorBudget R N+R*pw (one+R) N
def modulus (z R B N : PTm n) : PTm n := foldedModulus z R B N+comparisonBudget R N
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def nameData (z R B N : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus z R B N) (data z R B N)

ipra_subst data

ipra_subst rawPoint [rectangleCutoff, GaussianScalarExponentialProductTail.reserve, GaussianScalarExponentialProductTail.growthExponent]

ipra_subst exponentData

ipra_subst foldedRawData

ipra_subst comparisonBudget

ipra_subst modulus [foldedModulus]

theorem raw_at (p z R B N : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (data z R B N) ≐ rawPoint p z R B N := by
  let x := data z R B N
  let read : PTm 2 := rawPoint (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
  have ep : Γ ⊢[PRAAx] ap2 rawF p x ≐ rawPoint p (fstT x) (fstT (sndT x))
      (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) := by
    simpa [ap2,rawF,read] using toPR_eq (Γ := Γ) read ![p,x]
  have s1 : Γ ⊢[PRAAx] sndT x ≐ pairT R (pairT B N) := snd_pair _ _
  have s2 := s1.sndE
  have er := s1.fstE
  have eb := s2.fstE
  have en := s2.sndE
  exact ep.eqTrans (by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawPoint (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))])
      (σ' := ![p,z,R,B,N])
      (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact er; exact eb; exact en))

theorem exponent_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (width R N) (harmonicArgument z B N) := by
  let w := harmonicArgument z B N
  have hn : Γ ⊢[PRAAx] le (N*R) (width R N) :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have disk := GaussianCoefficientNameBounds.bounded_radius_mono w (N*R) one (width R N) one
    (le_refl _) (le_refl _) (le_congr (by ipra_ring) (by ipra_ring) hn)
    (harmonic_argument_bound z R B N h.andE₂.andE₁ h.andE₂.andE₂)
  apply Prf.andI (constant_regular w)
  apply Prf.allI
  have ds : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift (width R N)) one := by
    simpa [Fm.shift,Syn.shift] using disk.shift
  have d := bound_congr (constant_at (var 0) (Syn.shift w)).eqSymm (.eqRefl _) (.eqRefl _) ds
  simpa [w,Fm.shift,Syn.shift,GaussianRationalMetric.subst_bounded,GaussianRadiusExponentialName.boundedSamples] using d

theorem exponent_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN exponentF (exponentData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponent_input z R B N h)

theorem folded_raw_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular foldedRawF (foldedModulus z R B N) (foldedRawData z R B N) :=
  GaussianNameArithmetic.multiply_regular _ _ _ _ (constant_regular _) (exponent_regular z R B N h)

theorem same_precision (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 rawF p (data z R B N)) (ap2 foldedRawF p (foldedRawData z R B N))
      (comparisonBudget R N) (unit p) := by
  let W := width R N
  let x := harmonicArgument z B N
  let H := GaussianGammaEulerHead.head z B N
  let K := rectangleCutoff W p
  let j := GaussianRadiusExponentialName.inputPrecision W p
  let e := GaussianRadiusExponentialName.sample constantF W p x
  let M := R*pw (one+R) N
  have first := prefix_comparison z R B N p N h.andE₂.andE₁ h.andE₂.andE₂ (le_refl _)
  have d := finite_reference constantF W x p j K (exponent_input z R B N h) (le_refl _)
    (index_below_rectangle W W p p (le_add_right _ _) (le_refl _))
  have src : Γ ⊢[PRAAx] distanceBounded (GaussianRationalPolynomialExponential.scalarSum x K) e one (unit p) :=
    distance_congr (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (constant_at j x))
      (.eqRefl _) (.eqRefl _) (.eqRefl _) d
  have last := scaled_distance H _ _ one M (unit p) (unit_positive p)
    (GaussianGammaEulerHead.prefix_bound z R B N h.andE₂.andE₁ h.andE₂.andE₂) src
  have ht : Γ ⊢[PRAAx] ap2 foldedRawF p (foldedRawData z R B N) ≐ GaussianRationalHorner.qmul H e :=
    (GaussianNameArithmetic.multiply_raw_at constantF exponentF p H (exponentData z R B N)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (constant_at p H) (.eqRefl _))
  exact distance_congr (raw_at p z R B N).eqSymm ht.eqSymm (by unfold comparisonBudget M; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first last)

theorem raw_regular_at (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 rawF p (data z R B N)) (ap2 rawF q (data z R B N))
      (modulus z R B N*(unit p+unit q)) (unit p*unit q) := by
  let E := unit p*unit q
  let C := comparisonBudget R N
  have hE := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have a := distance_radius_mono _ _ C (unit p) (C*unit q) E (unit_positive p) hE
    (le_of_eq_add (d := zero) (by unfold E; ipra_ring)) (same_precision p z R B N h)
  have b := GaussianFastValueCut.regular_at foldedRawF (foldedModulus z R B N) (foldedRawData z R B N)
    p q (folded_raw_regular z R B N h)
  have c := distance_radius_mono _ _ C (unit q) (C*unit p) E (unit_positive q) hE
    (le_of_eq_add (d := zero) (by unfold E; ipra_ring))
    (distance_symmetric _ _ _ _ (unit_positive q) (same_precision q z R B N h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold modulus C; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE (distance_triangle_same _ _ _ _ _ _ hE a b) c)

theorem raw_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (modulus z R B N) (data z R B N) := by
  apply Prf.allI
  apply Prf.allI
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa [GaussianFastValueCut.regular,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
    raw_regular_at (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) hs

theorem name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN nameF (nameData z R B N) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular z R B N h)

theorem name_equivalent (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent nameF foldedF (nameData z R B N) (foldedData z R B N) := by
  apply GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ (comparisonBudget R N)
    (raw_regular z R B N h) (folded_raw_regular z R B N h)
  apply Prf.allI
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
    same_precision (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem original_literal_weierstrass_prefix_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (nameData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))

theorem original_literal_weierstrass_prefix_equivalent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF foldedF
      (nameData (var 0) (var 1) (var 2) (var 3)) (foldedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_equivalent _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassFiniteName
