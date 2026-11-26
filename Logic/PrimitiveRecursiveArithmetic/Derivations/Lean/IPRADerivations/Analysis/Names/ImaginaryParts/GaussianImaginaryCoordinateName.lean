import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedChord

/-!
# A regular real name for the imaginary coordinate

The program returns the canonical real-axis embedding of the original
imaginary coordinate. Its regularity and equivalence laws follow from
the exact projection of Euclidean errors to scalar radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianImaginaryCoordinateName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observation (f : PR 2) (p x : PTm n) : PTm n := embed (sndT (ap2 f p x))
def nameF (f : PR 2) : PR 2 := PTm.toPR (observation f (var 0) (var 1) : PTm 2)

theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p x ≐ observation f p x := by
  have e := toPR_eq (Γ := Γ) (observation f (var 0) (var 1) : PTm 2) ![p,x]
  simp only [observation,RationalGaussianEmbedding.subst_embed,subst_sndT,subst_ap2,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] at e
  exact e

theorem distance_at (f g : PR 2) (p q x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g q y) A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p x) (ap2 (nameF g) q y) A D :=
  distance_congr (sample_at f p x).eqSymm (sample_at g q y).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hD (imaginary_coordinate_radius _ _ _ _ hD h))

theorem name_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (nameF f) x := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f X := by
    simpa [Fm.shift,Syn.shift,X] using h.shift.shift
  exact distance_at f f (var 1) (var 0) X X _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianNameEquivalence.point_at f X (var 1) (var 0) hs)

theorem cross (f g : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) x y := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let Y := Syn.shift (Syn.shift y)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f g X Y := by
    simpa [Fm.shift,Syn.shift,X,Y] using h.shift.shift
  exact distance_at f g (var 1) (var 0) X Y _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianNameEquivalence.cross_at f g X Y (var 1) (var 0) hs)

theorem actual_imaginary_coordinate_name_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ pointCN (nameF f) (var 0)) :=
  closeUniv 1 (.impI (name_regular f _ Prf.hyp0))

theorem actual_imaginary_coordinate_equivalence_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent f g (var 0) (var 1) ⟶ crossEquivalent (nameF f) (nameF g) (var 0) (var 1)) :=
  closeUniv 2 (.impI (cross f g _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianImaginaryCoordinateName
