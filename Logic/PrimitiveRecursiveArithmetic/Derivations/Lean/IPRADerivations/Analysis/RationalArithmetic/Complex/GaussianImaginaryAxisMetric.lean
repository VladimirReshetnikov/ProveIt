import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding

/-!
# The scalar metric on the original imaginary axis

For points whose real coordinate is zero, the scalar radius of their
imaginary coordinates gives the same radius in the original Euclidean
metric. The calculation uses both original rational representations at
a common positive denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianImaginaryAxisMetric

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code scale normSq normSq_eval eval_re_code eval_im_code)
open GaussianRationalHorner (represents positive_product scalar_congr represents_rescale)
open GaussianRationalMetric (bounded_difference_iff distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (re_sub im_sub re_scale im_scale)
open RationalGaussianEmbedding (scalarZero embed native)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def imaginary (a : ZT n) : PTm n := code (ZT.ofNat zero) a

theorem axis_represents (q E : PTm n) (a : ZT n) (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents (sndT q) a E) : Γ ⊢[PRAAx] represents q (imaginary a) E := by
  refine .andI (scalar_congr hq.eqSymm ?_ (.eqRefl _) (RationalGaussianEmbedding.scalar_zero_represents E))
    (scalar_congr (.eqRefl _) ?_ (.eqRefl _) h)
  all_goals
    apply ZT.derive
    simp only [imaginary,eval_re_code,eval_im_code]

private theorem norm_swap (a b : ZT n) (E F : PTm n) : Γ ⊢[PRAAx]
    normSq (GaussianRootAlgebra.sub (scale F (imaginary a)) (scale E (imaginary b))) ≐
      normSq (GaussianRootAlgebra.sub (scale F (native a)) (scale E (native b))) := by
  apply deriveNat
  simp only [normSq_eval,re_sub,im_sub,re_scale,im_scale,imaginary,native,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem axis_distance_from_radius (q r A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero) (hr : Γ ⊢[PRAAx] fstT r ≐ scalarZero)
    (h : Γ ⊢[PRAAx] radius (sndT q) (sndT r) A D) : Γ ⊢[PRAAx] distanceBounded q r A D := by
  let a := sndT q
  let b := sndT r
  let E := denominatorOf a
  let F := denominatorOf b
  let G := E*F
  let u := numeratorOf a
  let v := numeratorOf b
  have hG := positive_product (Γ := Γ) E F (RationalArgmin.denominator_positive _) (RationalArgmin.denominator_positive _)
  have eu := represents_rescale (embed a) (native u) E F (RationalGaussianEmbedding.embed_represents (Γ := Γ) a)
  have ev := rescale_to (embed b) (native v) F E G (RationalGaussianEmbedding.embed_represents (Γ := Γ) b) (mul_comm F E)
  have qu := represents_rescale q (imaginary u) E F (axis_represents q E u hq (RationalRepresentations.represents_self a))
  have rv := rescale_to r (imaginary v) F E G (axis_represents r F v hr (RationalRepresentations.represents_self b)) (mul_comm F E)
  have real := (bounded_difference_iff _ _ _ _ G A D hG hD eu ev).iffMp
    (RationalGaussianNameEmbedding.distance_from_radius a b A D hD h)
  exact (bounded_difference_iff _ _ _ _ G A D hG hD qu rv).iffMpr
    (le_congr (congrMul (.eqRefl _) (norm_swap u v E F).eqSymm) (.eqRefl _) real)

theorem actual_imaginary_axis_scalar_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (var 0) ≐ scalarZero ⋏ fstT (var 1) ≐ scalarZero) ⟶
      (le one (var 3) ⋏ radius (sndT (var 0)) (sndT (var 1)) (var 2) (var 3)) ⟶
      distanceBounded (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (axis_distance_from_radius _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianImaginaryAxisMetric
