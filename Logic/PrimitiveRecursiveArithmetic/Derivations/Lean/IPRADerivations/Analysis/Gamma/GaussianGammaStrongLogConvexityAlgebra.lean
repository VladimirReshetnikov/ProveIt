import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogShift
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalLogOrder

/-!
# Named addition and recurrence for the strong Gamma chord

Translation by a regular name reflects real order. The original
log-Gamma recurrence is stable under an arbitrary natural weight,
so it can be applied directly to each part of the weighted chord.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaStrongLogConvexityAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianHarmonicLogarithmName (nameF data)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws
  (negativeF negativeData negative_fast add_negative add_zero_left add_associative add_commutative zeroF zero_at zero_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular source_shift)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => productF nameF
local notation "G" => productF logGammaF

theorem swap_first (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (addF H J)) (addF H (addF F J))
      (addData x (addData y z)) (addData y (addData x z)) := by
  have a := cross_symm _ _ _ _ (add_associative F H J x y z hf hh hj)
  have b := add_cross (addF F H) (addF H F) J J _ _ z z
    (add_fast _ _ _ _ hf hh) (add_fast _ _ _ _ hh hf) hj hj
    (add_commutative F H x y hf hh) (cross_refl _ _ hj)
  have c := add_associative H F J y x z hh hf hj
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

private theorem zero_data_cross (u x : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF u x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (zero_fast _)
  refine .allI ?_
  exact (zero_at _ (Syn.shift u)).eqTrans (zero_at _ (Syn.shift x)).eqSymm

theorem add_negative_front (F H : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (negativeF F) (addF F H)) H
      (addData (negativeData x) (addData x y)) y := by
  let N := negativeF F
  let z := negativeData x
  have hz := negative_fast F x hf
  have a := swap_first N F H z x y hz hf hh
  have b := cross_symm _ _ _ _ (add_associative F N H x z y hf hz hh)
  have c := add_cross (addF F N) zeroF H H (addData x z) y y y
    (add_fast _ _ _ _ hf hz) (zero_fast _) hh hh
    (cross_trans _ _ _ _ _ _ (add_negative F x hf) (zero_data_cross x y)) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b
    (cross_trans _ _ _ _ _ _ c (add_zero_left H y hh)))

theorem cancel_common (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z)
    (h : Γ ⊢[PRAAx] realOrder (addF F H) (addF F J) (addData x y) (addData x z)) :
    Γ ⊢[PRAAx] realOrder H J y z := by
  have a := add_order (negativeF F) (negativeF F) (addF F H) (addF F J)
    (negativeData x) (negativeData x) (addData x y) (addData x z)
    (order_refl _ _ (negative_fast F x hf)) h
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (add_negative_front F H x y hf hh)) (add_negative_front F J x z hf hj) a

theorem harmonic_rescale (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (k*a) (k*b)) (data a b) := by
  let F := GaussianPositiveRationalLogarithm.logF
  let d (u v : PTm n) := GaussianPositiveRationalLogarithm.data u v
  have hX : Γ ⊢[PRAAx] source (k*a) (k*b) :=
    .andI (positive_product _ _ hk hs.andE₁) (positive_product _ _ hk hs.andE₂)
  have same := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper (k*a) (k*b) a b hX hs (by ipra_ring)
  exact cross_trans nameF F nameF (data (k*a) (k*b)) (d (k*a) (k*b)) (data a b)
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original _ _ hX))
    (cross_trans _ _ _ _ _ _ same (GaussianHarmonicLogarithmName.cross_original a b hs))

theorem scaled_harmonic_rescale (a b k i : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent L L (productData nameF i (data (k*a) (k*b))) (productData nameF i (data a b)) := by
  let p := naturalPoint i
  have hc := constant_regular (Γ := Γ) p
  have hX : Γ ⊢[PRAAx] source (k*a) (k*b) :=
    .andI (positive_product _ _ hk hs.andE₁) (positive_product _ _ hk hs.andE₂)
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF nameF nameF p p (data (k*a) (k*b)) (data a b)
    hc hc (GaussianHarmonicLogarithmName.name_regular _ _ hX) (GaussianHarmonicLogarithmName.name_regular _ _ hs)
    (cross_refl _ _ hc) (harmonic_rescale a b k hs hk)

theorem weighted_recurrence (a b w : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent G (addF L G) (productData logGammaF w (logGammaData (a+b) b))
      (addData (productData nameF w (data a b)) (productData logGammaF w (logGammaData a b))) := by
  let q := naturalPoint w
  let U := data a b
  let V := logGammaData a b
  let W := logGammaData (a+b) b
  have hq := constant_regular (Γ := Γ) q
  have hU := GaussianHarmonicLogarithmName.name_regular a b hs
  have hV := log_gamma_regular a b hs
  have hW := log_gamma_regular (a+b) b (source_shift a b hs)
  have law := GaussianStirlingGammaLogShift.log_gamma_increment a b hs
  have prod := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logGammaF (addF nameF logGammaF)
    q q W (addData U V) hq hq hW (add_fast _ _ _ _ hU hV) (cross_refl _ _ hq) law
  exact cross_trans _ _ _ _ _ _ prod (GaussianNameRingLaws.distributive _ _ _ _ _ _ hq hU hV)

end LeanProofs.IPRA.Analysis.GaussianGammaStrongLogConvexityAlgebra
