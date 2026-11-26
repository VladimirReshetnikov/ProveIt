import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicInputProperness
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCertificateOverlap

/-!
# Equal encoded inputs give the same original logarithmic integral

Keep both original numerator/denominator encodings, radius bounds and
positive-margin certificates. Equal physical lower endpoints and one
common upper endpoint give actual compact programs at both parameters.
Their checked input properness joins the two original improper names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicImproperInputProperness

open_ipra
open GaussianEulerLogarithmicCertificateGeometry
open GaussianEulerLogarithmicCertificateOverlap (observation_at_common_top)
open LeanProofs.IPRA.Common (lt_succ_of_le)
open GaussianGammaIntegralCutoffs (etaDen tailCoefficient)
open GaussianEulerLogarithmicCommonCutoff (cutoff)
open GaussianEulerLogarithmicImproperName (nameF data name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "compactF" => GaussianEulerLogarithmicIntervalName.nameF
local notation "interval" => GaussianEulerLogarithmicTopExtension.fullData

def source (z w R S B D A V : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (GaussianEulerLowerPowerCoefficients.source w S D V ⋏ ofGaussian z B ≐ ofGaussian w D)

ipra_subst source

theorem original_diagonal (t j z w R S B D A V : PTm n) (h : Γ ⊢[PRAAx] source z w R S B D A V) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 nameF t (data j w S D V)) (num 24) (unit t) := by
  let M := tailCoefficient (R+j)+tailCoefficient (S+j)
  let r := GaussianFastValueCut.exponent M t
  let k := leftIndex r r j R A S V
  let l := rightIndex r r j R A S V
  let E := etaDen k (two*A) (R+j)
  let T := succ (commonTop r r j R A S V)
  let middleLeft := ap2 compactF t (interval j z R B E T)
  let middleRight := ap2 compactF t (interval j w S D E T)
  have hLeft := h.andE₁
  have hRight := h.andE₂.andE₁
  have hA := hLeft.andE₁
  have hV := hRight.andE₁
  have lr : Γ ⊢[PRAAx] le t r := le_add_right _ _
  have lp : Γ ⊢[PRAAx] le (cutoff r j A) k := left_index_late r r j R A S V hV
  have rp : Γ ⊢[PRAAx] le (cutoff r j V) l := right_index_late r r j R A S V hA
  have topL := lt_succ_of_le (left_top_bound r r j R A S V hV)
  have topR := lt_succ_of_le (right_top_bound r r j R A S V hA)
  have hE : Γ ⊢[PRAAx] le one E := GaussianGammaIntegralCutoffs.eta_den_positive k (two*A) (R+j)
  have hT : Γ ⊢[PRAAx] le one T := le_trans (GaussianGammaIntegralCutoffs.top_positive k (two*A) (R+j)) (le_of_lt topL)
  have pay := GaussianFastValueCut.query_budget (Γ := Γ) M t
  have payLeft : Γ ⊢[PRAAx] le (tailCoefficient (R+j)*unit t) (unit r) :=
    le_trans (mul_le_mul_right (unit t) (le_add_right (tailCoefficient (R+j)) (tailCoefficient (S+j)))) pay
  have payRight : Γ ⊢[PRAAx] le (tailCoefficient (S+j)*unit t) (unit r) :=
    le_trans (mul_le_mul_right (unit t) (le_add_left (tailCoefficient (S+j)) (tailCoefficient (R+j)))) pay
  have first := observation_at_common_top t r j z R R B A k E T hLeft hLeft.andE₂.andE₁ lr lp (.eqRefl E) topL payLeft
  have last := observation_at_common_top t r j w S S D V l E T hRight hRight.andE₂.andE₁
    lr rp (same_eta r r j R A S V hA hV).eqSymm topR payRight
  have compact := cross_at _ _ _ _ t t (GaussianEulerLogarithmicInputProperness.original_compact_proper
    j z w R S B D one (GaussianEulerLogarithmicTopExtension.width E T) E T
    (.andI (GaussianEulerLogarithmicTopExtension.full_interval_source z R B E T hLeft.andE₂.andE₁ hE hT)
      (.andI (GaussianEulerLogarithmicTopExtension.full_interval_source w S D E T hRight.andE₂.andE₁ hE hT) h.andE₂.andE₂)))
  have center : Γ ⊢[PRAAx] distanceBounded middleLeft middleRight two (unit t) :=
    distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) compact
  have hU := unit_positive (Γ := Γ) t
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first
      (distance_triangle_same _ _ _ _ _ _ hU center (distance_symmetric _ _ _ _ hU last)))

theorem original_improper_proper (j z w R S B D A V : PTm n) (h : Γ ⊢[PRAAx] source z w R S B D A V) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data j z R B A) (data j w S D V) := by
  apply GaussianNameRingLaws.equivalent_of_envelope nameF nameF _ _ (num 24)
    (name_regular j z R B A h.andE₁) (name_regular j w S D V h.andE₂.andE₁)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh w) (sh R) (sh S) (sh B) (sh D) (sh A) (sh V) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianEulerLogarithmicImproperName.subst_data,PTm.subst_num,sh] using
    original_diagonal (var 0) (sh j) (sh z) (sh w) (sh R) (sh S) (sh B) (sh D) (sh A) (sh V) hs

theorem original_observations (p q j z w R S B D A V : PTm n) (h : Γ ⊢[PRAAx] source z w R S B D A V) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B A)) (ap2 nameF q (data j w S D V))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_improper_proper j z w R S B D A V h)

theorem actual_original_logarithmic_improper_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 3) (var 5) (var 7))
        (data (var 0) (var 2) (var 4) (var 6) (var 8))) :=
  closeUniv 9 (.impI (original_improper_proper _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicImproperInputProperness
