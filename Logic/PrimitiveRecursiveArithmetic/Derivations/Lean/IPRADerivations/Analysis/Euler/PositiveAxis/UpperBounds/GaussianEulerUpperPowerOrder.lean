import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCoefficients
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName

/-!
# Same-clock signed-real exponential comparison above time one

Both actual exponent input names multiply the same ordered harmonic-log
observation at the same supplied numerical clock. The original native
input disk therefore yields exponential order without an assumed
logarithm sign or an output-order premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerOrder

open_ipra
open GaussianEulerUpperPowerCoefficients (realMultiplier upperMultiplier amplification)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open GaussianSignedNameExponentialOrder (realSamples)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianHarmonicLogarithmName.nameF
abbrev inputF : PR 2 := GaussianBoundedConstantProductName.nameF logarithmF
abbrev expF : PR 2 := GaussianRadiusExponentialName.nameF inputF

def source (z R B a b : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏
    (GaussianPositiveRationalLogarithm.source a b ⋏ le b a)
def leftData (z R B a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b)
def rightData (R a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) (upperMultiplier R) (GaussianHarmonicLogarithmName.data a b)
def radius (R a : PTm n) : PTm n := amplification R*GaussianHarmonicLogarithmName.radius one a
def leftExpData (z R B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R a) (leftData z R B a b)
def rightExpData (R a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R a) (rightData R a b)

ipra_subst source
ipra_subst leftData
ipra_subst rightData
ipra_subst radius
ipra_subst leftExpData
ipra_subst rightExpData

theorem actual_time_domain (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain a b one a :=
  .andI h.andE₁ (.andI (le_congr (.eqRefl _) (one_mul _).eqSymm h.andE₂)
    (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl a) h.andE₁.andE₂)))

theorem product_sample_real (p A c a b : PTm n) (hc : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis c) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (GaussianBoundedConstantProductName.sample logarithmF p A c (GaussianHarmonicLogarithmName.data a b)) ⋏
      RationalGaussianEmbedding.axis (GaussianBoundedConstantProductName.sample logarithmF p A c (GaussianHarmonicLogarithmName.data a b)) := by
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) logarithmF p A c (GaussianHarmonicLogarithmName.data a b)
  exact .andI (GaussianRationalHorner.canonical_congr e (GaussianRationalHorner.qmul_canonical _ _))
    (RationalGaussianEmbedding.axis_congr e.eqSymm (RationalGaussianEmbedding.axis_multiply _ _ hc
      (GaussianHarmonicLogarithmName.sample_real (GaussianBoundedConstantProductName.clock p A) a b).andE₂))

theorem product_real_samples (A c a b : PTm n) (hc : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis c) : Γ ⊢[PRAAx]
    realSamples inputF (GaussianBoundedConstantProductName.data A c (GaussianHarmonicLogarithmName.data a b)) := by
  refine .allI ?_
  have cs : Γ.map Fm.shift ⊢[PRAAx] RationalGaussianEmbedding.axis (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hc.shift
  simpa only [realSamples,Syn.shift,GaussianBoundedConstantProductName.subst_data,GaussianHarmonicLogarithmName.subst_data,
    GaussianBoundedConstantProductName.sample] using
    product_sample_real (var 0) (Syn.shift A) (Syn.shift c) (Syn.shift a) (Syn.shift b) cs

theorem product_input (A c a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a)
    (hc : Γ ⊢[PRAAx] bounded c A one) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input inputF (A*GaussianHarmonicLogarithmName.radius one a)
      (GaussianBoundedConstantProductName.data A c (GaussianHarmonicLogarithmName.data a b)) := by
  refine .andI (GaussianBoundedConstantProductName.name_regular logarithmF A c _
    (.andI (GaussianHarmonicLogarithmName.name_regular a b h.andE₁) hc)) (.allI ?_)
  have ts : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) ⋏ le (Syn.shift b) (Syn.shift a) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift c) (Syn.shift A) one := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hs := GaussianHarmonicLogarithmName.compact_sample_bound
    (GaussianBoundedConstantProductName.clock (var 0) (Syn.shift A)) (Syn.shift a) (Syn.shift b) one (Syn.shift a)
    (le_refl one) (actual_time_domain _ _ ts)
  have hb := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) cs hs
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ.map Fm.shift) logarithmF (var 0) (Syn.shift A) (Syn.shift c) (GaussianHarmonicLogarithmName.data (Syn.shift a) (Syn.shift b))
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,GaussianBoundedConstantProductName.sample] using
    GaussianRationalReciprocal.bound_congr e.eqSymm (.eqRefl _) (one_mul _) hb

theorem sample_order_at (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 inputF p (leftData z R B a b))) (fstT (ap2 inputF p (rightData R a b))) := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let l := GaussianHarmonicLogarithmName.sample s a b
  have hr := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) s a b).andE₂
  have order := RationalArithmetic.multiply_monotone (fstT l) (fstT (realMultiplier z B)) (fstT (upperMultiplier R))
    (GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative s a b h.andE₂.andE₂).andE₂
    (GaussianEulerUpperPowerCoefficients.multiplier_order z R B h.andE₁)
  have left := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) logarithmF p (amplification R) (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have right := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) logarithmF p (amplification R) (upperMultiplier R) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  exact RationalArgmin.rationalLE_congr left.eqSymm right.eqSymm order

theorem sample_order (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    sampleOrder inputF inputF (leftData z R B a b) (rightData R a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleOrder,Syn.shift,subst_leftData,subst_rightData] using
    sample_order_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs

theorem ordered_exponentials (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    realOrder expF expF (leftExpData z R B a b) (rightExpData R a b) :=
  GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF (radius R a) _ _
    (product_input _ _ _ _ h.andE₂ (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁))
    (product_input _ _ _ _ h.andE₂ (GaussianEulerUpperPowerCoefficients.upper_multiplier_bound R))
    (product_real_samples _ _ _ _ (GaussianEulerUpperPowerCoefficients.real_multiplier_axis z B))
    (product_real_samples _ _ _ _ (RationalGaussianEmbedding.axis_congr
      (GaussianExponentialRealPartMajorant.embed_natural (two*R)) (RationalGaussianEmbedding.embed_axis _)))
    (sample_order z R B a b h)

theorem actual_upper_time_ordered_exponentials_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      realOrder expF expF (leftExpData (var 0) (var 1) (var 2) (var 3) (var 4)) (rightExpData (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (ordered_exponentials _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerOrder
