import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedExtension
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseUniqueness
import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentExtensionRange

/-!
# Injectivity and the left inverse of the named arctangent

Exact unit-interval representations bind the extension's late rational
queries to their original parameter names. The finite lower slope
recovers the parameters from equal forward names and identifies the
actual inverse of the forward extension with the original parameter.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedExtensionUniqueness

open_ipra
open GaussianArctangentInverseForward (input)
open GaussianArctangentInverseSampler (index mesh mesh_positive index_le raw)
open GaussianArctangentInverseUniqueness (selected selected_at retimed_parameter_distance)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentNamedExtension (clock nameF partial_distance parameter_represents_of_embedding)
open GaussianArctangentNamedInverse (forward_sample_error)
open GaussianArctangentNamedSlope (ordinate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone dyadic_weaken)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open RationalValueBounds (radius radius_mono radius_symmetric radius_triangle)
open GaussianRobinMeshLogDecomposition renaming later_sample → observation_retime

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (clock p) := le_add_right _ _

private theorem selected_phase_radius (f a b : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] selected f a b x) : Γ ⊢[PRAAx]
    radius (GaussianArctangentInverseSampler.ordinate (nameF f) p x)
      (ordinate (clock p) (ap2 a (clock p) x) (ap2 b (clock p) x)) two (unit p) := by
  have s := selected_at f a b (clock p) x h
  have rep := parameter_represents_of_embedding f p x _ _ s.andE₁ s.andE₂.andE₂
  have d := partial_distance f p x _ _ s.andE₁ s.andE₂.andE₁ rep
  exact imaginary_coordinate_radius _ _ _ _ (unit_positive p)
    (dyadic_weaken _ _ _ p (clock p) (clock_later p) d)

private theorem injectivity_bound (f g a b c d : PR 2) (p x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hF : Γ ⊢[PRAAx] selected f a b x) (hG : Γ ⊢[PRAAx] selected g c d y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) (num 12) (unit p) := by
  let r := clock p
  let A := ap2 a r x
  let B := ap2 b r x
  let C := ap2 c r y
  let D := ap2 d r y
  let u := ordinate r A B
  let v := ordinate r C D
  let i := GaussianArctangentInverseSampler.ordinate (nameF f) p x
  let j := GaussianArctangentInverseSampler.ordinate (nameF g) p y
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have s := selected_at f a b r x hF
  have t := selected_at g c d r y hG
  have mid : Γ ⊢[PRAAx] radius i j two U :=
    radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU)
      (imaginary_coordinate_radius _ _ _ _ (positive_product _ _ hU hU) (cross_at _ _ _ _ p p he))
      (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring))
  have ru := radius_symmetric i u two U (selected_phase_radius f a b p x hF)
  have rv := selected_phase_radius g c d p y hG
  have ruv : Γ ⊢[PRAAx] radius u v (num 6) U := by
    have h := RationalValueBounds.radius_triangle_same hU (RationalValueBounds.radius_triangle_same hU ru mid) rv
    exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) h
  have slide := retimed_parameter_distance p r A B C D (num 6) (clock_later p)
    s.andE₁ t.andE₁ s.andE₂.andE₁ t.andE₂.andE₁ ruv
  have shifted_pair : Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 g r y) (num 8) U :=
    distance_congr s.andE₂.andE₂.eqSymm t.andE₂.andE₂.eqSymm (by ipra_ring) (.eqRefl _) slide
  have left := observation_retime f p r x hf (clock_later p)
  have right := distance_symmetric _ _ _ _ hU (observation_retime g p r y hg (clock_later p))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU left shifted_pair) right)

theorem original_extension_injective (f g a b c d : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hF : Γ ⊢[PRAAx] selected f a b x) (hG : Γ ⊢[PRAAx] selected g c d y)
    (h : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  apply cross_of_diagonal_rate _ _ _ _ (num 12) hf hg
  refine .allI ?_
  let X := Syn.shift x
  let Y := Syn.shift y
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f X := by simpa [Fm.shift,Syn.shift,X] using hf.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] pointCN g Y := by simpa [Fm.shift,Syn.shift,Y] using hg.shift
  have hu : Γ.map Fm.shift ⊢[PRAAx] selected f a b X := by simpa [Fm.shift,Syn.shift,X] using hF.shift
  have hv : Γ.map Fm.shift ⊢[PRAAx] selected g c d Y := by simpa [Fm.shift,Syn.shift,Y] using hG.shift
  have e : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) X Y := by simpa [Fm.shift,Syn.shift,X,Y] using h.shift
  simpa only [diagonalRate,Syn.shift,PTm.subst_num,X,Y] using
    injectivity_bound f g a b c d (var 0) X Y hs ht hu hv e

private theorem raw_left_inverse_error (f a b : PR 2) (p x z : PTm n)
    (hs : Γ ⊢[PRAAx] selected f a b x) (hi : Γ ⊢[PRAAx] input (nameF f) x z) :
    Γ ⊢[PRAAx] distanceBounded (raw (nameF f) p x) (ap2 f (clock p) x) (num 12) (unit p) := by
  let r := clock p
  let U := unit p
  let F := nameF f
  let A := index F p x
  let B := mesh p
  let C := ap2 a r x
  let D := ap2 b r x
  let u := ordinate r A B
  let v := ordinate r C D
  have s := selected_at f a b r x hs
  have first := forward_sample_error F r p x z hi
  have second := selected_phase_radius f a b p x hs
  have summed : Γ ⊢[PRAAx] radius u v (num 10) U :=
    RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (RationalValueBounds.radius_triangle_same (unit_positive p) first second)
  have d := retimed_parameter_distance p r A B C D (num 10) (clock_later p)
    (mesh_positive p) s.andE₁ (index_le F p x) s.andE₂.andE₁ summed
  exact distance_congr (.eqRefl _) s.andE₂.andE₂.eqSymm (by ipra_ring) (.eqRefl _) d

private theorem left_inverse_bound (f a b : PR 2) (p x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hs : Γ ⊢[PRAAx] selected f a b x) (hi : Γ ⊢[PRAAx] input (nameF f) x z) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianArctangentNamedInverse.nameF (nameF f)) p (GaussianArctangentNamedInverse.data x))
      (ap2 f p x) (num 14) (unit p) := by
  let q := GaussianArctangentNamedInverse.precision p
  let r := clock q
  have hq : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have hr := le_trans hq (clock_later q)
  have hU := unit_positive (Γ := Γ) p
  have first := dyadic_weaken _ _ _ p q hq (raw_left_inverse_error f a b q x z hs hi)
  have second := distance_symmetric _ _ _ _ hU (observation_retime f p r x hf hr)
  exact distance_congr (GaussianArctangentNamedInverse.name_at (nameF f) p x).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hU first second)

theorem original_left_inverse (f a b : PR 2) (x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hs : Γ ⊢[PRAAx] selected f a b x) (hi : Γ ⊢[PRAAx] input (nameF f) x z) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianArctangentNamedInverse.nameF (nameF f)) f
      (GaussianArctangentNamedInverse.data x) x := by
  apply cross_of_diagonal_rate _ _ _ _ (num 14) (GaussianArctangentNamedInverse.name_regular _ _ _ hi) hf
  refine .allI ?_
  let X := Syn.shift x
  let Z := Syn.shift z
  have hf' : Γ.map Fm.shift ⊢[PRAAx] pointCN f X := by simpa [Fm.shift,Syn.shift,X] using hf.shift
  have hs' : Γ.map Fm.shift ⊢[PRAAx] selected f a b X := by simpa [Fm.shift,Syn.shift,X] using hs.shift
  have hi' : Γ.map Fm.shift ⊢[PRAAx] input (nameF f) X Z := by simpa [Fm.shift,Syn.shift,X,Z] using hi.shift
  simpa only [diagonalRate,Syn.shift,GaussianArctangentNamedInverse.subst_data,PTm.subst_num,X] using
    left_inverse_bound f a b (var 0) X Z hf' hs' hi'

theorem original_extension_left_inverse (f a b : PR 2) (x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hs : Γ ⊢[PRAAx] selected f a b x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianArctangentNamedInverse.nameF (nameF f)) f
      (GaussianArctangentNamedInverse.data x) x :=
  original_left_inverse f a b x zero hf hs (GaussianArctangentExtensionRange.inverse_input f x zero hf)

theorem actual_arctangent_named_extension_injective_closed (f g a b c d : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (((pointCN f (var 0) ⋏ pointCN g (var 1)) ⋏ (selected f a b (var 0) ⋏ selected g c d (var 1))) ⟶
        crossEquivalent (nameF f) (nameF g) (var 0) (var 1) ⟶ crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (original_extension_injective f g a b c d _ _
    Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

theorem actual_arctangent_named_extension_left_inverse_closed (f a b : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      ((pointCN f (var 0) ⋏ selected f a b (var 0)) ⟶
        crossEquivalent (GaussianArctangentNamedInverse.nameF (nameF f)) f
          (GaussianArctangentNamedInverse.data (var 0)) (var 0)) :=
  closeUniv 1 (.impI (original_extension_left_inverse f a b _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedExtensionUniqueness
