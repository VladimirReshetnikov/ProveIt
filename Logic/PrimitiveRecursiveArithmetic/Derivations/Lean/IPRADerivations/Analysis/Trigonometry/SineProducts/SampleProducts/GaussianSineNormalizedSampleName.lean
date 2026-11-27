import IPRADerivations.Analysis.Trigonometry.MultipleAngles.GaussianSinePolynomialVariation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# Named normalized sine product and polynomial

A single precision shift turns both the literal rational root-product
stream and the normalized Horner stream into regular names. Their
samples use the same input sine observation. The root-product error
then supplies exact equivalence of the two regular names.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleName

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalHorner (canonical positive_product qmul_canonical)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_radius_scale distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianSineNormalizedSampleProduct (normalizedProduct canonical_product)
open GaussianSineNormalizedSampleReconstruction (normalizedValue normalizedBudget cofinal_normalized_distance)
open GaussianSinePolynomialVariation (variationBudget normalized_value_distance)
open GaussianSineSquaredTrace (fromSine)
open GaussianRootApproximationWitness (pointBounds)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev bound (f : PR 2) (B x : PTm n) : Fm PTm n := pointBounds f B x

def rawData (J x z : PTm n) : PTm n := pairT J (pairT x z)
def budget (J B : PTm n) : PTm n := normalizedBudget J B+variationBudget J B
def precision (J B p : PTm n) : PTm n := GaussianFastValueCut.exponent (budget J B) p
def data (J B x z : PTm n) : PTm n := GaussianFastValueCut.nameData (budget J B) (rawData J x z)

def productSample (f : PR 2) (p J x z : PTm n) : PTm n :=
  normalizedProduct (GaussianSineSampleRootGuards.clock p J) J z (ap2 f p x)
def polynomialSample (f : PR 2) (p J x : PTm n) : PTm n :=
  normalizedValue J (fromSine (ap2 f p x))
def productBody (f : PR 2) : PTm 2 :=
  productSample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def polynomialBody (f : PR 2) : PTm 2 := polynomialSample f (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
def rawProductF (f : PR 2) : PR 2 := PTm.toPR (productBody f)
def rawPolynomialF (f : PR 2) : PR 2 := PTm.toPR (polynomialBody f)
def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawProductF f)
def polynomialF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawPolynomialF f)

ipra_subst budget
ipra_subst precision
ipra_subst rawData
ipra_subst data
ipra_subst productSample
ipra_subst polynomialSample [fromSine]

theorem raw_product_at (f : PR 2) (p J x z : PTm n) :
    Γ ⊢[PRAAx] ap2 (rawProductF f) p (rawData J x z) ≐ productSample f p J x z := by
  simpa [rawProductF, productBody, rawData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (productSample f (var 0) (var 1) (var 2) (var 3)) p ![J, x, z])

theorem raw_polynomial_at (f : PR 2) (p J x z : PTm n) :
    Γ ⊢[PRAAx] ap2 (rawPolynomialF f) p (rawData J x z) ≐ polynomialSample f p J x := by
  simpa [rawPolynomialF, polynomialBody, rawData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (polynomialSample f (var 0) (var 1) (var 2)) p ![J, x, z])

private theorem readback (g : PR 2) (p L x s : PTm n)
    (hs : Γ ⊢[PRAAx] ap2 g (GaussianFastValueCut.exponent L p) x ≐ s) (hc : Γ ⊢[PRAAx] canonical s) :
    Γ ⊢[PRAAx] ap2 (GaussianFastValueCut.nameF g) p (GaussianFastValueCut.nameData L x) ≐ s := by
  have e := Prf.eqCongr (Γ := Γ) (GaussianFastValueCut.recode (var 0) : PTm 1)
    (σ := ![ap2 g (GaussianFastValueCut.exponent L p) x]) (σ' := ![s]) (fun i => by fin_cases i; exact hs)
  exact (GaussianFastValueCut.name_at g L x p).eqTrans
    ((by simpa using e : Γ ⊢[PRAAx] GaussianFastValueCut.recode (ap2 g (GaussianFastValueCut.exponent L p) x) ≐
      GaussianFastValueCut.recode s).eqTrans (GaussianExponentialReference.recode_fixed _ hc))

theorem product_at (f : PR 2) (p J B x z : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data J B x z) ≐ productSample f (precision J B p) J x z :=
  readback _ p (budget J B) (rawData J x z) _ (raw_product_at f _ J x z) (canonical_product _ _ _ _)

theorem polynomial_at (f : PR 2) (p J B x z : PTm n) :
    Γ ⊢[PRAAx] ap2 (polynomialF f) p (data J B x z) ≐ polynomialSample f (precision J B p) J x :=
  readback _ p (budget J B) (rawData J x z) _ (raw_polynomial_at f _ J x z) (qmul_canonical _ _)

theorem sample_distance (f : PR 2) (p J B x z : PTm n) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] distanceBounded (productSample f p J x z) (polynomialSample f p J x) (normalizedBudget J B) (unit p) :=
  cofinal_normalized_distance _ _ _ _ _ (GaussianRootApproximationWitness.point_at f B x p hb)

theorem polynomial_pair (f : PR 2) (p q J B x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] distanceBounded (polynomialSample f p J x) (polynomialSample f q J x)
      (variationBudget J B*(unit p+unit q)) (unit p*unit q) :=
  normalized_value_distance _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
    (GaussianRootApproximationWitness.point_at f B x p hb) (GaussianRootApproximationWitness.point_at f B x q hb)
    (point_at f x p q hf)

theorem product_pair (f : PR 2) (p q J B x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] distanceBounded (productSample f p J x z) (productSample f q J x z)
      (budget J B*(unit p+unit q)) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let E := normalizedBudget J B
  let d := positive_product (Γ := Γ) P Q (unit_positive p) (unit_positive q)
  have nearP := distance_radius_scale (unit_positive p) (unit_positive q) (sample_distance f p J B x z hb)
  have nearQ := distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm Q P)
    (distance_radius_scale (unit_positive q) (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive q) (sample_distance f q J B x z hb)))
  have e := distance_triangle_same _ _ _ _ _ _ d (distance_triangle_same _ _ _ _ _ _ d nearP
    (polynomial_pair f p q J B x hf hb)) nearQ
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P,Q,E]; unfold budget; ipra_ring) (.eqRefl _) e

theorem raw_product_regular (f : PR 2) (J B x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawProductF f) (budget J B) (rawData J x z) := by
  refine .allI (.allI ?_)
  let L := fun t : PTm n => Syn.shift (Syn.shift t)
  have hf' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (L x) := by simpa [L,Fm.shift,Syn.shift] using hf.shift.shift
  have hb' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] bound f (L B) (L x) :=
    by simpa [L,Fm.shift,Syn.shift] using hb.shift.shift
  simpa [GaussianFastValueCut.regular,Syn.shift,L] using distance_congr
    (raw_product_at f (var 1) (L J) (L x) (L z)).eqSymm (raw_product_at f (var 0) (L J) (L x) (L z)).eqSymm
    (.eqRefl _) (.eqRefl _) (product_pair f (var 1) (var 0) (L J) (L B) (L x) (L z) hf' hb')

theorem raw_polynomial_regular (f : PR 2) (J B x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawPolynomialF f) (budget J B) (rawData J x z) := by
  refine .allI (.allI ?_)
  let L := fun t : PTm n => Syn.shift (Syn.shift t)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let H := unit p+unit q
  let K := unit p*unit q
  have hf' : Δ ⊢[PRAAx] pointCN f (L x) := by simpa [L,Δ,Fm.shift,Syn.shift] using hf.shift.shift
  have hb' : Δ ⊢[PRAAx] bound f (L B) (L x) := by simpa [L,Δ,Fm.shift,Syn.shift] using hb.shift.shift
  have hK : Δ ⊢[PRAAx] le one K := positive_product _ _ (unit_positive p) (unit_positive q)
  have hB : Δ ⊢[PRAAx] le (variationBudget (L J) (L B)) (budget (L J) (L B)) := le_add_left _ _
  have e := distance_radius_mono _ _ _ K (budget (L J) (L B)*H) K hK hK
    (le_mul_mono (le_mul_mono hB (le_refl H)) (le_refl K)) (polynomial_pair f p q (L J) (L B) (L x) hf' hb')
  simpa [GaussianFastValueCut.regular,Syn.shift,L,p,q,H,K,Δ] using distance_congr
    (raw_polynomial_at f p (L J) (L x) (L z)).eqSymm (raw_polynomial_at f q (L J) (L x) (L z)).eqSymm
    (.eqRefl _) (.eqRefl _) e

theorem product_regular (f : PR 2) (J B x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data J B x z) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_product_regular f J B x z hf hb)

theorem polynomial_regular (f : PR 2) (J B x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] pointCN (polynomialF f) (data J B x z) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_polynomial_regular f J B x z hf hb)

theorem polynomial_cross (f : PR 2) (J B x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] bound f B x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (polynomialF f) (data J B x z) (data J B x z) := by
  apply cross_of_diagonal_rate _ _ _ _ (normalizedBudget J B)
    (product_regular f J B x z hf hb) (polynomial_regular f J B x z hf hb)
  refine .allI ?_
  let p : PTm (n+1) := var 0
  let t := precision (Syn.shift J) (Syn.shift B) p
  have hb' : Γ.map Fm.shift ⊢[PRAAx] bound f (Syn.shift B) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using hb.shift
  have e := GaussianExponentialReference.dyadic_weaken _ _ _ p t (le_add_right _ _)
    (sample_distance f t (Syn.shift J) (Syn.shift B) (Syn.shift x) (Syn.shift z) hb')
  simpa [diagonalRate,Syn.shift,p] using distance_congr
    (product_at f p (Syn.shift J) (Syn.shift B) (Syn.shift x) (Syn.shift z)).eqSymm
    (polynomial_at f p (Syn.shift J) (Syn.shift B) (Syn.shift x) (Syn.shift z)).eqSymm
    (.eqRefl _) (.eqRefl _) e

theorem actual_normalized_sine_product_polynomial_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((pointCN f (var 2) ⋏ bound f (var 1) (var 2)) ⟶
      crossEquivalent (nameF f) (polynomialF f) (data (var 0) (var 1) (var 2) (var 3))
        (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (polynomial_cross f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleName
