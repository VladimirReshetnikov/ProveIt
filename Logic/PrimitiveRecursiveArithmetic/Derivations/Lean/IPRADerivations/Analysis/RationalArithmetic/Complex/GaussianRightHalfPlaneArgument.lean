import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentOriginalExponential
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialExponential
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverse
import IPRADerivations.Analysis.Names.Branches.GaussianNameBranch

/-!
# The argument on the certified rational right half-plane

The arguments are encoded by a positive real numerator, an absolute
imaginary numerator, and its sign bit. A common positive denominator
is immaterial. The two charts use the original rational arctangent
quadrature on the unit interval, and the second chart subtracts the
reciprocal argument from the original quarter turn.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgument

open_ipra
open LeanProofs.IPRA.Probability.MedianCounts (congrSg)
open ComplexLogarithmRemainder (oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRadiusExponentialName (boundedSamples bounded_samples_at input)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "atanF" => GaussianArctangentPartialQuadrature.nameF
local notation "atData" => GaussianArctangentPartialQuadrature.data

/-- A real numerator `A>0`, the absolute imaginary numerator `B`, and
an exact sign bit `neg` suffice to define the argument. -/
def source (A neg : PTm n) : Fm PTm n := le one A ⋏ (neg ≐ zero ⋎ neg ≐ one)

def half : PTm n := ofGaussian oneCode two
def smallF : PR 2 := GaussianBoundedConstantProductName.nameF atanF
def smallData (A B : PTm n) : PTm n := GaussianBoundedConstantProductName.data one half (atData B A)
def largeF : PR 2 := GaussianNameArithmetic.addF quarterF (GaussianNameRingLaws.negativeF smallF)
def largeData (A B : PTm n) : PTm n :=
  GaussianNameArithmetic.addData zero (GaussianNameRingLaws.negativeData (smallData B A))

def wide (A B : PTm n) : PTm n := LeanProofs.IPRA.Signum.sg (monus B A)
def unsignedF : PR 2 := GaussianNameBranch.nameF smallF largeF
def unsignedData (A B : PTm n) : PTm n :=
  GaussianNameBranch.data (wide A B) (smallData A B) (largeData A B)

def nameF : PR 2 := GaussianNameBranch.nameF unsignedF (GaussianNameConjugation.nameF unsignedF)
def data (A B neg : PTm n) : PTm n := GaussianNameBranch.data neg (unsignedData A B) (unsignedData A B)
def radius : PTm n := two+two

ipra_subst source

ipra_subst smallData [half, GaussianArctangentPartialQuadrature.data]

ipra_subst largeData

ipra_subst unsignedData [wide]

ipra_subst data

theorem half_bounded : Γ ⊢[PRAAx] bounded (half : PTm n) one one := by
  have hd : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] normSq (oneCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [oneCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ two one one hd (le_refl _) (ofGaussian_represents _ _ hd)
  have h : Γ ⊢[PRAAx] le (normSq (oneCode : PTm n)) (two*two) :=
    le_congr hn.eqSymm (.eqRefl _) (le_of_eq_add (d := num 3) (by ipra_ring))
  exact le_congr (by ipra_ring) (by ipra_ring) h

theorem small_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] pointCN smallF (smallData A B) :=
  GaussianBoundedConstantProductName.name_regular atanF one half (atData B A)
    (.andI (GaussianArctangentPartialQuadrature.name_regular B A hA hB) half_bounded)

theorem small_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (ap2 smallF p (smallData A B)) two one := by
  let j := GaussianBoundedConstantProductName.clock p one
  have h := bounded_product half (ap2 atanF j (atData B A)) one one two one
    (le_refl _) (le_refl _) half_bounded (GaussianArctangentPartialExponential.argument_bound j B A hA hB)
  exact bound_congr (GaussianBoundedConstantProductName.sample_at atanF p one half (atData B A)).eqSymm
    (one_mul _) (one_mul _) h

theorem small_input (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] input smallF two (smallData A B) := by
  refine .andI (small_regular A B hA hB) (.allI ?_)
  have a : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift B) (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hB.shift
  simpa [boundedSamples,Syn.shift] using small_bound (var 0) (Syn.shift A) (Syn.shift B) a b

theorem large_input (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] input largeF radius (largeData A B) :=
  GaussianExponentialReference.add_input _ _ two zero _
    (GaussianArctangentQuarterExponential.quarter_input zero
      (GaussianArctangentQuarterExponential.original_bounded_arguments zero))
    (GaussianExponentialInverse.negative_input _ _ _ (small_input B A hB hA))

theorem wide_zero (A B : PTm n) (h : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx] wide A B ≐ zero :=
  (congrSg h).eqTrans LeanProofs.IPRA.Signum.sg_zero

theorem wide_one (A B : PTm n) (h : Γ ⊢[PRAAx] lt A B) : Γ ⊢[PRAAx] wide A B ≐ one :=
  Foundations.IntervalPacking.sg_one_of_lt h

theorem unsigned_small (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] crossEquivalent unsignedF smallF (unsignedData A B) (smallData A B) :=
  GaussianNameBranch.select_left _ _ _ _ _ (wide_zero A B hB) (small_regular A B hA hB)

theorem unsigned_large (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] lt A B) :
    Γ ⊢[PRAAx] crossEquivalent unsignedF largeF (unsignedData A B) (largeData A B) :=
  GaussianNameBranch.select_right _ _ _ _ _ (wide_one A B hB)
    (large_input A B (le_trans hA (le_of_lt hB)) (le_of_lt hB)).andE₁

theorem unsigned_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] bounded (ap2 unsignedF p (unsignedData A B)) radius one := by
  refine .orE (lt_or_le A B) ?_ ?_
  · have h := large_input A B (le_trans hA.wk (le_of_lt Prf.hyp0)) (le_of_lt Prf.hyp0)
    exact bound_congr ((GaussianNameBranch.sample_at _ _ p _ _ _).eqTrans
      (RationalArithmetic.select_one _ _ _ (wide_one A B Prf.hyp0))).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_samples_at largeF radius (largeData A B) p h.andE₂)
  · have h := (GaussianNameBranch.sample_at (Γ := le B A :: Γ) smallF largeF p
      (wide A B) (smallData A B) (largeData A B)).eqTrans
      (RationalArithmetic.select_zero _ _ _ (wide_zero A B Prf.hyp0))
    exact bound_congr h.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _)
        (le_congr (by ipra_ring) (by unfold radius; ipra_ring) (le_add_right two two)) (small_bound p A B hA.wk Prf.hyp0))

theorem unsigned_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] pointCN unsignedF (unsignedData A B) := by
  refine .orE (lt_or_le A B) ?_ ?_
  · have h := unsigned_large A B hA.wk Prf.hyp0
    exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ h (GaussianNameEquivalence.cross_symm _ _ _ _ h)
  · have h := unsigned_small A B hA.wk Prf.hyp0
    exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ h (GaussianNameEquivalence.cross_symm _ _ _ _ h)

theorem unsigned_input (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] input unsignedF radius (unsignedData A B) := by
  refine .andI (unsigned_regular A B hA) (.allI ?_)
  have a : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
  simpa [boundedSamples,Syn.shift,radius] using unsigned_bound (var 0) (Syn.shift A) (Syn.shift B) a

theorem positive_sign (A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] neg ≐ zero) :
    Γ ⊢[PRAAx] crossEquivalent nameF unsignedF (data A B neg) (unsignedData A B) :=
  GaussianNameBranch.select_left _ _ _ _ _ h (unsigned_regular A B hA)

theorem negative_sign (A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] neg ≐ one) :
    Γ ⊢[PRAAx] crossEquivalent nameF (GaussianNameConjugation.nameF unsignedF) (data A B neg) (unsignedData A B) :=
  GaussianNameBranch.select_right _ _ _ _ _ h
    (GaussianNameConjugation.regular _ _ (unsigned_regular A B hA))

theorem name_bound (p A B neg : PTm n) (h : Γ ⊢[PRAAx] source A neg) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data A B neg)) radius one := by
  refine .orE h.andE₂ ?_ ?_
  · have e := (GaussianNameBranch.sample_at (Γ := (neg ≐ zero) :: Γ) unsignedF
      (GaussianNameConjugation.nameF unsignedF) p neg (unsignedData A B) (unsignedData A B)).eqTrans
      (RationalArithmetic.select_zero _ _ _ Prf.hyp0)
    exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (unsigned_bound p A B h.andE₁.wk)
  · have e := (GaussianNameBranch.sample_at (Γ := (neg ≐ one) :: Γ) unsignedF
      (GaussianNameConjugation.nameF unsignedF) p neg (unsignedData A B) (unsignedData A B)).eqTrans
      (RationalArithmetic.select_one _ _ _ Prf.hyp0)
    have hq := GaussianRationalConjugation.point_bound (Γ := (neg ≐ one) :: Γ) _ _ _ (le_refl one) (unsigned_bound p A B h.andE₁.wk)
    exact bound_congr (e.eqTrans (GaussianNameConjugation.sample_at _ _ _)).eqSymm (.eqRefl _) (.eqRefl _) hq

theorem name_regular (A B neg : PTm n) (h : Γ ⊢[PRAAx] source A neg) :
    Γ ⊢[PRAAx] pointCN nameF (data A B neg) := by
  refine .orE h.andE₂ ?_ ?_
  · have e := positive_sign A B neg h.andE₁.wk Prf.hyp0
    exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ e (GaussianNameEquivalence.cross_symm _ _ _ _ e)
  · have e := negative_sign A B neg h.andE₁.wk Prf.hyp0
    exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ e (GaussianNameEquivalence.cross_symm _ _ _ _ e)

theorem exponential_input (A B neg : PTm n) (h : Γ ⊢[PRAAx] source A neg) :
    Γ ⊢[PRAAx] input nameF radius (data A B neg) := by
  refine .andI (name_regular A B neg h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift A) (Syn.shift neg) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [boundedSamples,Syn.shift,radius] using name_bound (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift neg) hs

theorem actual_right_half_plane_argument_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 2) ⟶ input nameF radius (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (exponential_input _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgument
