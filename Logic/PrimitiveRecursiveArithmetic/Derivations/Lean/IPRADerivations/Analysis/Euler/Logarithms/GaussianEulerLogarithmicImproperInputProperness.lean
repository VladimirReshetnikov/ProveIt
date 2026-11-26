import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicInputProperness
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicCertificateGeometry
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicTopExtension
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicFixedCutoff

/-!
# Equal encoded inputs give the same original logarithmic integral

Keep both original numerator/denominator encodings, radius bounds and
positive-margin certificates. Equal physical lower endpoints and one
common upper endpoint give actual compact programs at both parameters.
Their checked input properness joins the two original improper names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicImproperInputProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCertificateGeometry
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianEulerLogarithmicCommonCutoff (cutoff cutoff_later)
open GaussianEulerLogarithmicImproperName (nameF data name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "compactF" => GaussianEulerLogarithmicIntervalName.nameF
local notation "full" => GaussianEulerLogarithmicCutoffSplit.fullData
local notation "interval" => GaussianEulerLogarithmicTopExtension.fullData

def source (z w R S B D A V : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (GaussianEulerLowerPowerCoefficients.source w S D V ⋏ ofGaussian z B ≐ ofGaussian w D)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z w R S B D A V : PTm n) :
    (source z w R S B D A V).subst σ = source (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R)
      (Syn.subst σ S) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ V) := by simp [source]

private theorem fixed_diagonal (t r j z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (later : Γ ⊢[PRAAx] le t r) (hk : Γ ⊢[PRAAx] le (cutoff r j A) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 compactF t (full j z R B A k)) (num 4) (unit t) := by
  let K := unit (r+num 6)
  have query : Γ ⊢[PRAAx] le (unit t) K := GaussianExponentialReference.unit_monotone (le_trans later (le_add_right _ _))
  have fixed := rate_at _ _ _ _ two K t t
    (GaussianEulerLogarithmicFixedCutoff.original_fixed_cutoff_rate r j z R B A k h hk)
  exact distance_radius_mono _ _ _ _ (num 4) (unit t) (denominator_positive K t t (unit_positive _)) (unit_positive t)
    (by dsimp only [rateNumerator,rateDenominator,K]; ipra_le (2*𝔞(unit t)*𝔞(unit t))*sl query) fixed

private theorem extension_diagonal (t j z R B E L T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicTopExtension.source z R R B E L T)
    (strict : Γ ⊢[PRAAx] lt (two*L) T)
    (budget : Γ ⊢[PRAAx] le (tailCoefficient (R+j)*unit t) (unit L)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 compactF t (interval j z R B E T)) (ap2 compactF t (interval j z R B E (two*L)))
      (num 7) (unit t) := by
  have larger := GaussianEulerLogarithmicTopExtension.original_strict_observations t t j z R R B E L T h strict
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicTopExtension.denominator t t L) :=
    positive_product _ _ (positive_product _ _ (unit_positive L) hU) hU
  exact distance_radius_mono _ _ _ _ (num 7) (unit t) hD hU
    (by unfold GaussianEulerLogarithmicTopExtension.numerator GaussianEulerLogarithmicTopExtension.denominator
        ipra_le (𝔞(unit t)*𝔞(unit t))*sl budget) larger

private theorem strictly_below_succ (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  le_congr (succ_eq_add_one a).eqSymm (succ_eq_add_one b).eqSymm (add_le_add_right one h)

theorem original_diagonal (t j z w R S B D A V : PTm n) (h : Γ ⊢[PRAAx] source z w R S B D A V) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 nameF t (data j w S D V)) (num 24) (unit t) := by
  let M := tailCoefficient (R+j)+tailCoefficient (S+j)
  let r := GaussianFastValueCut.exponent M t
  let k := leftIndex r r j R A S V
  let l := rightIndex r r j R A S V
  let L := height k (two*A) (R+j)
  let J := height l (two*V) (S+j)
  let E := etaDen k (two*A) (R+j)
  let F := etaDen l (two*V) (S+j)
  let T := succ (commonTop r r j R A S V)
  let left := ap2 compactF t (full j z R B A k)
  let right := ap2 compactF t (full j w S D V l)
  let middleLeft := ap2 compactF t (interval j z R B E T)
  let middleRight := ap2 compactF t (interval j w S D E T)
  have hLeft := h.andE₁
  have hRight := h.andE₂.andE₁
  have hA := hLeft.andE₁
  have hV := hRight.andE₁
  have lr : Γ ⊢[PRAAx] le t r := le_add_right _ _
  have lp : Γ ⊢[PRAAx] le (cutoff r j A) k := left_index_late r r j R A S V hV
  have rp : Γ ⊢[PRAAx] le (cutoff r j V) l := right_index_late r r j R A S V hA
  have hl : Γ ⊢[PRAAx] le r L := le_trans (cutoff_later r j A)
    (le_trans (le_add_left _ _) (le_congr (.eqRefl _) (left_height r r j R A S V hV).eqSymm (left_height_budget r r j R A S V hV)))
  have hr : Γ ⊢[PRAAx] le r J := le_trans (cutoff_later r j V)
    (le_trans (le_add_left _ _) (le_congr (.eqRefl _) (right_height r r j R A S V hA).eqSymm (right_height_budget r r j R A S V hA)))
  have topL : Γ ⊢[PRAAx] lt (two*L) T := strictly_below_succ _ _ (left_top_bound r r j R A S V hV)
  have topR : Γ ⊢[PRAAx] lt (two*J) T := strictly_below_succ _ _ (right_top_bound r r j R A S V hA)
  have hE : Γ ⊢[PRAAx] le one E := GaussianGammaIntegralCutoffs.eta_den_positive k (two*A) (R+j)
  have hL : Γ ⊢[PRAAx] le one L := GaussianGammaIntegralCutoffs.height_positive k (two*A) (R+j)
  have hJ : Γ ⊢[PRAAx] le one J := GaussianGammaIntegralCutoffs.height_positive l (two*V) (S+j)
  have hT : Γ ⊢[PRAAx] le one T := le_trans (GaussianGammaIntegralCutoffs.top_positive k (two*A) (R+j)) (le_of_lt topL)
  have er : Γ ⊢[PRAAx] E ≐ F := same_eta r r j R A S V hA hV
  have rightData : Γ ⊢[PRAAx] full j w S D V l ≐ interval j w S D E (two*J) :=
    GaussianEulerLogarithmicCutoffSplit.interval_data_congr j w S D one _ _ _ one _ _ _ (.eqRefl one)
      (congrMonus (congrMul er.eqSymm (.eqRefl (two*J))) (.eqRefl one)) er.eqSymm (.eqRefl (two*J))
  have pay := GaussianFastValueCut.query_budget (Γ := Γ) M t
  have payLeft : Γ ⊢[PRAAx] le (tailCoefficient (R+j)*unit t) (unit L) :=
    le_trans (mul_le_mul_right (unit t) (le_add_right (tailCoefficient (R+j)) (tailCoefficient (S+j))))
      (le_trans pay (GaussianExponentialReference.unit_monotone hl))
  have payRight : Γ ⊢[PRAAx] le (tailCoefficient (S+j)*unit t) (unit J) :=
    le_trans (mul_le_mul_right (unit t) (le_add_left (tailCoefficient (S+j)) (tailCoefficient (R+j))))
      (le_trans pay (GaussianExponentialReference.unit_monotone hr))
  have first := fixed_diagonal t r j z R B A k hLeft lr lp
  have second : Γ ⊢[PRAAx] distanceBounded middleLeft left (num 7) (unit t) :=
    extension_diagonal t j z R B E L T
      (.andI hLeft.andE₂.andE₁ (.andI hLeft.andE₂.andE₁ (.andI hE (.andI hL (le_of_lt topL))))) topL payLeft
  have compact := cross_at _ _ _ _ t t (GaussianEulerLogarithmicInputProperness.original_compact_proper
    j z w R S B D one (GaussianEulerLogarithmicTopExtension.width E T) E T
    (.andI (GaussianEulerLogarithmicTopExtension.full_interval_source z R B E T hLeft.andE₂.andE₁ hE hT)
      (.andI (GaussianEulerLogarithmicTopExtension.full_interval_source w S D E T hRight.andE₂.andE₁ hE hT) h.andE₂.andE₂)))
  have center : Γ ⊢[PRAAx] distanceBounded middleLeft middleRight two (unit t) :=
    distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) compact
  have fourth : Γ ⊢[PRAAx] distanceBounded middleRight right (num 7) (unit t) :=
    distance_congr (.eqRefl _) (congrAp2 compactF (.eqRefl t) rightData.eqSymm) (.eqRefl _) (.eqRefl _)
      (extension_diagonal t j w S D E J T
        (.andI hRight.andE₂.andE₁ (.andI hRight.andE₂.andE₁ (.andI hE (.andI hJ (le_of_lt topR))))) topR payRight)
  have last := fixed_diagonal t r j w S D V l hRight lr rp
  have hU := unit_positive (Γ := Γ) t
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first (distance_triangle_same _ _ _ _ _ _ hU
      (distance_symmetric _ _ _ _ hU second) (distance_triangle_same _ _ _ _ _ _ hU center
        (distance_triangle_same _ _ _ _ _ _ hU fourth (distance_symmetric _ _ _ _ hU last)))))

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
