import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductScaledArgumentIdentity
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleResidual
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.NamedValues.GaussianArctangentNamedCayleyTrig

/-!
# Synchronized error for the sampled divided sine

The actual finite Cayley sine observations used by the root product
approximate the original exponential-defined divided sine with a
fixed distance budget. The observation clock may be shifted later
without changing the argument or the sampling program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineRawRootBinding

open_ipra
open GaussianArctangentDivisionAngleResidual (inverseF inverseData sineSample mesh mesh_positive index)
open GaussianArctangentDivisionAngles (modulus odd_source)
open GaussianArctangentDivisionSinePositive (exactSineData)
open GaussianArctangentInverseCorrectness (roundTripF imaginary_right_inverse)
open GaussianArctangentCayleyProjections (sineProjectionF sine_projection)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_proper)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_diagonal_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (dyadic_weaken)
open GaussianNamedSincSamples (common_late_distance)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open RationalGaussianNameEmbedding (distance_from_radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem inverse_regular (k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] pointCN inverseF (inverseData k J z) :=
  GaussianArctangentNamedInverse.name_regular _ _ _ (GaussianArctangentDivisionAngles.interval_input k (modulus J) z (odd_source k J hk))

theorem original_sine_projection_cross (k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] crossEquivalent (sineF GaussianArctangentDivisionAngles.nameF) (sineProjectionF inverseF)
      (exactSineData k (modulus J) z) (GaussianArctangentNamedCayley.data (inverseData k J z)) := by
  let f := GaussianArctangentDivisionAngles.nameF
  let g := roundTripF f
  let inv := GaussianArctangentNamedInverse.nameF f
  let m := modulus J
  let x := GaussianArctangentDivisionAngles.data k m z
  let y := GaussianArctangentNamedInverse.data x
  have hs := odd_source k J hk
  have interval := GaussianArctangentDivisionAngles.interval_input k m z hs
  have hi : Γ ⊢[PRAAx] pointCN inv y := GaussianArctangentNamedInverse.name_regular f x z interval
  have e := imaginary_right_inverse f x z interval
    (GaussianArctangentDivisionAngles.imaginary_samples k m z hs.andE₁)
  have first := sine_proper f g two two x y (GaussianArctangentDivisionAngles.exponential_input k m z hs)
    (GaussianArctangentNamedCayley.exp_input inv y hi) (cross_symm g f y x e)
  exact cross_trans _ _ _ _ _ _ first (GaussianArctangentNamedCayleyTrig.sine_cross inv y hi)

private theorem projection_raw_error (p k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (sineProjectionF inverseF) p (GaussianArctangentNamedCayley.data (inverseData k J z)))
      (sineSample p k J z) (num 5) (unit p) := by
  let y := inverseData k J z
  let c := GaussianArctangentNamedCayley.nameF inverseF
  let d := GaussianArctangentNamedCayley.data y
  let raw := GaussianArctangentNamedCayley.raw inverseF p y
  have hU := unit_positive (Γ := Γ) p
  have read := GaussianNameRingLaws.normalized_to_sample (GaussianArctangentNamedCayley.rawF inverseF)
    GaussianArctangentNamedCayley.modulus y p
    (GaussianArctangentNamedCayley.raw_regularity inverseF y (inverse_regular k J z hk))
  have rawError : Γ ⊢[PRAAx] distanceBounded (ap2 c p d) raw (num 5) (unit p) :=
    distance_congr (.eqRefl _) (GaussianArctangentNamedCayley.raw_at inverseF p y)
      (by unfold GaussianArctangentNamedCayley.modulus; ipra_ring) (.eqRefl _) read
  have scalar := imaginary_coordinate_radius _ _ _ _ hU rawError
  exact distance_congr (GaussianImaginaryCoordinateName.sample_at c p d).eqSymm
    (sine_projection (mesh p k J z) (index p k J z) (mesh_positive p k J z)) (.eqRefl _) (.eqRefl _)
    (distance_from_radius _ _ _ _ hU scalar)

theorem raw_root_error_at (p k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (sineF GaussianArctangentDivisionAngles.nameF) p (exactSineData k (modulus J) z))
      (sineSample p k J z) (num 7) (unit p) := by
  let f := sineF GaussianArctangentDivisionAngles.nameF
  let g := sineProjectionF inverseF
  let x := exactSineData k (modulus J) z
  let y := GaussianArctangentNamedCayley.data (inverseData k J z)
  have eq := original_sine_projection_cross k J z hk
  have same := cross_diagonal_at p eq
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) same (projection_raw_error p k J z hk))

theorem raw_root_error_later (p q k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (sineF GaussianArctangentDivisionAngles.nameF) p (exactSineData k (modulus J) z))
      (sineSample q k J z) (num 9) (unit p) := by
  let f := GaussianArctangentDivisionAngles.nameF
  let x := exactSineData k (modulus J) z
  have regular := sine_regular f two _ (GaussianArctangentDivisionAngles.exponential_input k (modulus J) z (odd_source k J hk))
  have begin := common_late_distance (sineF f) x p p q regular (le_refl p) h
  have last := dyadic_weaken _ _ _ p q h (raw_root_error_at q k J z hk)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) begin last)

theorem actual_divided_raw_sine_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 2) (var 1) ⟶ le (var 4) (var 3) ⟶
      distanceBounded (ap2 (sineF GaussianArctangentDivisionAngles.nameF) (var 4) (exactSineData (var 2) (modulus (var 1)) (var 0)))
        (sineSample (var 3) (var 2) (var 1) (var 0)) (num 9) (unit (var 4))) :=
  closeUniv 5 (.impI (.impI (raw_root_error_later _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineRawRootBinding
