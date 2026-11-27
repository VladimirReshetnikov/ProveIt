import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferenceProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.Reflection.GaussianGammaGaussReflectionDomain
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling

/-!
# Removing the unit Γ(m/m) from the original reference product

The original reference loop of length `m` and its literal prefix of
length `m-1` name the same value. The final reference row is the
original Gamma reciprocal at the positive encoding `m/m`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReferencePrefix

open_ipra
open GaussianGammaGaussReferenceProduct (rowF rowRadius row_at row_bounds row_regular nameF)
open GaussianGammaGaussReflectionDomain (referenceData)
open GaussianGammaGaussReference (reference_source)
open GaussianGammaReciprocalInverse (gammaF gammaHeight original_gamma_inverse)
open GaussianGammaEncodingRescaling (original_encoded_one_at_radius)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameRingLaws (oneF one_fast multiply_one)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_diagonal_at)
open GaussianNamedFiniteProduct (sample sample_succ sample_bound sample_canonical)
open GaussianNamedFiniteProductName (rowBounds rowRegular bounds_at raw_regular rawF rawData raw_at)
open GaussianValueNormalizerExtensionality (rawDiagonal normalized_names_equivalent)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalReciprocal (qone)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N : PTm n) : PTm n :=
  GaussianNamedFiniteProductName.data N (rowRadius (succ N)) one (succ N)
def rate (N : PTm n) : PTm n := GaussianNamedFiniteProduct.radius (rowRadius (succ N)) N*two

ipra_subst data [one]
ipra_subst rate [two, one]

theorem terminal_one (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent gammaF constantF (referenceData m m) qone := by
  let z := GaussianGammaGaussReflectionDomain.argument m
  let x := GaussianGammaC7Name.data z one m
  let P := GaussianGammaC7Name.nameF
  have hs := reference_source m m hm (le_refl m)
  have hP : Γ ⊢[PRAAx] pointCN P x := GaussianGammaC7Name.name_regular z one m hs.andE₁
  have h1 := original_encoded_one_at_radius one m (le_refl one) hm
  have inv := (original_gamma_inverse z one m one m hs).andE₁
  have unitAt : Γ ⊢[PRAAx] crossEquivalent P oneF x x :=
    cross_trans P oneF oneF x zero x h1 (GaussianBoundedInverseApartness.ones_equivalent zero x)
  have prod : Γ ⊢[PRAAx] crossEquivalent (multiplyF P oneF) oneF (multiplyData P oneF x x) x :=
    cross_trans (multiplyF P oneF) P oneF _ x x (multiply_one P x hP) unitAt
  have gammaOne : Γ ⊢[PRAAx] crossEquivalent gammaF oneF (referenceData m m) x :=
    GaussianBoundedInverseApartness.reciprocal_matches_inverse P oneF (gammaHeight z one m m) x x
      hP (one_fast x) inv.andE₂ prod
  have constantOne : Γ ⊢[PRAAx] crossEquivalent oneF constantF x qone :=
    GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianNameRingLaws.constant_one_cross x)
  exact cross_trans gammaF oneF constantF (referenceData m m) x qone gammaOne constantOne

theorem terminal_at (p N : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap3 rowF p N (succ N)) qone two (unit p) := by
  have h := terminal_one (Γ := Γ) (succ N) (zero_lt_succ N)
  exact distance_congr (row_at p N (succ N)).eqSymm (constant_at p qone) (.eqRefl _) (.eqRefl _)
    (cross_diagonal_at p h)

theorem prefix_bounds (N : PTm n) :
    Γ ⊢[PRAAx] rowBounds rowF N (rowRadius (succ N)) (succ N) :=
  GaussianNamedFiniteProductName.row_bounds_mono rowF N (succ N) _ _ _ (row_bounds (succ N))
    (le_succ_self N) (le_refl _)

theorem prefix_regular (N : PTm n) :
    Γ ⊢[PRAAx] rowRegular rowF N one (succ N) :=
  GaussianNamedFiniteProductName.row_regular_restrict rowF N (succ N) _ _ (row_regular (succ N))
    (le_succ_self N)

theorem name_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data N) :=
  GaussianNamedFiniteProductName.name_regular rowF N (rowRadius (succ N)) one (succ N) (prefix_bounds N) (prefix_regular N)

theorem prefix_error (p N : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (sample rowF p (succ N) (succ N)) (sample rowF p N (succ N)) (rate N) (unit p) := by
  let R := rowRadius (succ N)
  let u := sample rowF p N (succ N)
  have h := sample_bound rowF p N R (succ N) (bounds_at _ _ _ _ _ (prefix_bounds (Γ := Γ) N))
  exact distance_congr (sample_succ rowF p N (succ N)).eqSymm
    (qmul_one_right u (sample_canonical _ _ _ _)) (.eqRefl _) (.eqRefl _)
    (multiply_distance u _ _ (GaussianNamedFiniteProduct.radius R N) two (unit p) (unit_positive p) h (terminal_at p N))

private theorem diagonal (N : PTm n) :
    Γ ⊢[PRAAx] rawDiagonal (rawF rowF) (rawF rowF)
      (rawData (succ N) (succ N)) (rawData N (succ N)) (rate N) := by
  refine .allI ?_
  let K := Syn.shift N
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have near := prefix_error (Γ := Δ) p K
  simpa [rawDiagonal,Syn.shift,K,p,Δ] using
    distance_congr (raw_at rowF p (succ K) (succ K)).eqSymm (raw_at rowF p K (succ K)).eqSymm
      (.eqRefl _) (.eqRefl _) near

theorem full_prefix_cross (N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (GaussianGammaGaussReferenceProduct.data (succ N)) (data N) := by
  let m := succ N
  have full := raw_regular rowF m (rowRadius m) one m (row_bounds (Γ := Γ) m) (row_regular m)
  have pref := raw_regular rowF N (rowRadius m) one m (prefix_bounds (Γ := Γ) N) (prefix_regular N)
  exact normalized_names_equivalent _ _ _ _ _ _ _ full pref (diagonal N)

theorem actual_Gauss_reference_terminal_unit_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent nameF nameF (GaussianGammaGaussReferenceProduct.data (succ (var 0))) (data (var 0))) :=
  closeUniv 1 (full_prefix_cross _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReferencePrefix
