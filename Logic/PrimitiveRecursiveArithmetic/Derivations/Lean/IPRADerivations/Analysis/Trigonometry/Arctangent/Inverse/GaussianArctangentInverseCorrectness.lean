import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedExtension
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentNamedInverse
import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentExtensionAxis
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianImaginaryAxisMetric
import IPRADerivations.Analysis.Names.ImaginaryParts.GaussianImaginaryCoordinateName

/-!
# Exact right inverse on the certified arctangent angle interval

The forward name reads the normalized inverse's actual rational
observation. Representation independence allows its denominator to be
normalized without changing the arctangent. A vanishing diagonal error
gives the exact identity for the two original angle coordinate names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseCorrectness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentInverseForward (input)
open GaussianArctangentInverseSampler (ordinate index mesh index_le mesh_positive)
open GaussianArctangentNamedInverse (data precision precision_later forward_sample_later forwardSample modulus name_represents)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open RationalValueBounds (radius radius_triangle radius_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def roundTripF (f : PR 2) : PR 2 := GaussianArctangentNamedExtension.nameF (GaussianArctangentNamedInverse.nameF f)

def imaginarySamples (f : PR 2) (x : PTm n) : Fm PTm n :=
  .all (fstT (ap2 f (var 0) (Syn.shift x)) ≐ RationalGaussianEmbedding.scalarZero)

@[simp] theorem subst_imaginarySamples {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    (imaginarySamples f x).subst σ = imaginarySamples f (Syn.subst σ x) := by
  simp [imaginarySamples,Syn.subst_shift,Syn.shift_subst]

theorem imaginary_sample_at (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] fstT (ap2 f p x) ≐ RationalGaussianEmbedding.scalarZero := by
  simpa [imaginarySamples] using h.allE p

theorem ordinate_error (f : PR 2) (p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] radius (sndT (ap2 (roundTripF f) p (data x))) (ordinate f p x) (num 12) (unit p) := by
  let c := GaussianArctangentNamedExtension.clock p
  let t := precision c
  let g := GaussianArctangentNamedInverse.nameF f
  let K := index f t x
  let M := mesh t
  let U := unit p
  let left := sndT (ap2 (roundTripF f) p (data x))
  let right := forwardSample f c t x
  have hc : Γ ⊢[PRAAx] le p c := le_add_right _ _
  have ht : Γ ⊢[PRAAx] le p t := le_trans hc (precision_later c)
  have hU := unit_positive (Γ := Γ) p
  have stage := GaussianArctangentNamedExtension.partial_distance (Γ := Γ) g p (data x) K M
    (mesh_positive t) (index_le f t x) (name_represents f c x)
  have raw : Γ ⊢[PRAAx] radius left right two (unit c) :=
    imaginary_coordinate_radius _ _ _ _ (unit_positive c) stage
  have first : Γ ⊢[PRAAx] radius left right two U :=
    radius_mono _ _ _ _ _ _ (unit_positive c) raw
      (le_mul_mono (le_refl two) (GaussianGammaHalfPiName.unit_mono p c hc))
  have next := forward_sample_later f c t p x z h ht
  exact radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU)
    (radius_triangle left right (ordinate f p x) two U modulus U first next)
    (le_congr (by unfold modulus; ipra_ring) (.eqRefl _) (le_refl _))

theorem right_inverse (f : PR 2) (x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianImaginaryCoordinateName.nameF (roundTripF f))
      (GaussianImaginaryCoordinateName.nameF f) (data x) x := by
  have hInverse := GaussianArctangentNamedInverse.name_regular f x z h
  have hTrip := GaussianArctangentNamedExtension.name_regular _ _ hInverse
  apply cross_of_diagonal_rate _ _ _ _ (num 12)
    (GaussianImaginaryCoordinateName.name_regular (roundTripF f) (data x) hTrip)
    (GaussianImaginaryCoordinateName.name_regular f x h.andE₁)
  refine .allI ?_
  let X := Syn.shift x
  let Z := Syn.shift z
  let p : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f X Z := by
    simpa only [Fm.shift,GaussianArctangentInverseForward.subst_input,Syn.shift,X,Z] using h.shift
  simpa only [diagonalRate,GaussianArctangentNamedInverse.subst_data,PTm.subst_num,Syn.shift,X,p] using
    distance_congr (GaussianImaginaryCoordinateName.sample_at (roundTripF f) p (data X)).eqSymm
      (GaussianImaginaryCoordinateName.sample_at f p X).eqSymm (.eqRefl _) (.eqRefl _)
      (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (unit_positive p) (ordinate_error f p X Z hs))

theorem imaginary_right_inverse (f : PR 2) (x z : PTm n)
    (h : Γ ⊢[PRAAx] input f x z) (hi : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (roundTripF f) f (data x) x := by
  have ht := GaussianArctangentNamedExtension.name_regular _ _ (GaussianArctangentNamedInverse.name_regular f x z h)
  apply cross_of_diagonal_rate _ _ _ _ (num 12) ht h.andE₁
  refine .allI ?_
  let X := Syn.shift x
  let Z := Syn.shift z
  let p : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f X Z := by
    simpa only [Fm.shift,GaussianArctangentInverseForward.subst_input,Syn.shift,X,Z] using h.shift
  have hi' : Γ.map Fm.shift ⊢[PRAAx] imaginarySamples f X := by
    simpa only [Fm.shift,subst_imaginarySamples,Syn.shift,X] using hi.shift
  simpa only [diagonalRate,GaussianArctangentNamedInverse.subst_data,PTm.subst_num,Syn.shift,X,p] using
    GaussianImaginaryAxisMetric.axis_distance_from_radius _ _ _ _ (unit_positive p)
      (GaussianArctangentExtensionAxis.extension_axis_at _ p (data X)) (imaginary_sample_at f p X hi')
      (ordinate_error f p X Z hs)

theorem actual_arctangent_right_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ crossEquivalent (GaussianImaginaryCoordinateName.nameF (roundTripF f))
      (GaussianImaginaryCoordinateName.nameF f) (data (var 0)) (var 0)) :=
  closeUniv 2 (.impI (right_inverse f _ _ Prf.hyp0))

theorem actual_arctangent_imaginary_right_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ imaginarySamples f (var 0) ⟶ crossEquivalent (roundTripF f) f (data (var 0)) (var 0)) :=
  closeUniv 2 (.impI (.impI (imaginary_right_inverse f _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseCorrectness
