import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.Certificates.GaussianEulerLogarithmicCertificateGeometry
import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicTopExtension
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.FrozenRates.GaussianEulerLogarithmicFixedCutoff

/-!
# Independence of the original logarithmic integral certificates

Two positive margins and disk bounds can be compared at independently
late cutoffs with exactly the same lower endpoint. Extend both upper
endpoints to one common compact interval, bounding each actual upper
tail. The actual regular names then agree at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCertificateOverlap

open_ipra
open GaussianEulerLogarithmicCertificateGeometry
open LeanProofs.IPRA.Common (lt_succ_of_le)
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianEulerLogarithmicCommonCutoff (cutoff cutoff_later)
open GaussianEulerLogarithmicImproperName (nameF data name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "compactF" => GaussianEulerLogarithmicIntervalName.nameF
local notation "full" => GaussianEulerLogarithmicCutoffSplit.fullData
local notation "interval" => GaussianEulerLogarithmicTopExtension.fullData

def source (z R S B A V : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ GaussianEulerLowerPowerCoefficients.source z S B V

ipra_subst source

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

private theorem extension_diagonal (t j z R S B E L T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicTopExtension.source z R S B E L T)
    (strict : Γ ⊢[PRAAx] lt (two*L) T)
    (budget : Γ ⊢[PRAAx] le (tailCoefficient (S+j)*unit t) (unit L)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 compactF t (interval j z S B E T)) (ap2 compactF t (interval j z R B E (two*L)))
      (num 7) (unit t) := by
  have larger := GaussianEulerLogarithmicTopExtension.original_strict_observations t t j z R S B E L T h strict
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicTopExtension.denominator t t L) :=
    positive_product _ _ (positive_product _ _ (unit_positive L) hU) hU
  exact distance_radius_mono _ _ _ _ (num 7) (unit t) hD hU
    (by unfold GaussianEulerLogarithmicTopExtension.numerator GaussianEulerLogarithmicTopExtension.denominator
        ipra_le (𝔞(unit t)*𝔞(unit t))*sl budget) larger

/-- One certified improper observation reaches the common top through its original cutoff. -/
theorem observation_at_common_top (t r j z R S B A k E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hWide : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z S B)
    (later : Γ ⊢[PRAAx] le t r) (hk : Γ ⊢[PRAAx] le (cutoff r j A) k)
    (etaEq : Γ ⊢[PRAAx] etaDen k (two*A) (R+j) ≐ E)
    (hTop : Γ ⊢[PRAAx] lt (top k (two*A) (R+j)) T)
    (pay : Γ ⊢[PRAAx] le (tailCoefficient (S+j)*unit t) (unit r)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 compactF t (interval j z S B E T)) (num 11) (unit t) := by
  let L := height k (two*A) (R+j)
  have hL := GaussianGammaIntegralCutoffs.height_positive (Γ := Γ) k (two*A) (R+j)
  have hE := le_congr (.eqRefl one) etaEq (GaussianGammaIntegralCutoffs.eta_den_positive k (two*A) (R+j))
  have heightLater : Γ ⊢[PRAAx] le k L :=
    le_of_eq_add (d := two*A+tailCoefficient (R+j)+num 10) (by dsimp only [L,height]; ipra_ring)
  have heightBudget := GaussianExponentialReference.unit_monotone (le_trans (cutoff_later r j A) (le_trans hk heightLater))
  have extension := extension_diagonal t j z R S B E L T
    (.andI h.andE₂.andE₁ (.andI hWide (.andI hE (.andI hL (le_of_lt hTop))))) hTop (le_trans pay heightBudget)
  have aligned := GaussianEulerLogarithmicCutoffSplit.interval_data_congr j z R B one _ _ _ one _ _ _ (.eqRefl one)
    (congrMonus (congrMul etaEq (.eqRefl (two*L))) (.eqRefl one)) etaEq (.eqRefl (two*L))
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 compactF t (interval j z S B E T))
      (ap2 compactF t (full j z R B A k)) (num 7) (unit t) :=
    distance_congr (.eqRefl _) (congrAp2 compactF (.eqRefl t) aligned.eqSymm) (.eqRefl _) (.eqRefl _) extension
  have hU := unit_positive (Γ := Γ) t
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (fixed_diagonal t r j z R B A k h later hk)
      (distance_symmetric _ _ _ _ hU near))

theorem original_diagonal (t j z R S B A V : PTm n) (h : Γ ⊢[PRAAx] source z R S B A V) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 nameF t (data j z S B V)) (num 22) (unit t) := by
  let M := tailCoefficient (R+j)
  let r := GaussianFastValueCut.exponent M t
  let k := leftIndex r r j R A S V
  let l := rightIndex r r j R A S V
  let E := etaDen k (two*A) (R+j)
  let T := succ (commonTop r r j R A S V)
  have hA := h.andE₁.andE₁
  have hV := h.andE₂.andE₁
  have lr : Γ ⊢[PRAAx] le t r := le_add_right _ _
  have lp : Γ ⊢[PRAAx] le (cutoff r j A) k := left_index_late r r j R A S V hV
  have rp : Γ ⊢[PRAAx] le (cutoff r j V) l := right_index_late r r j R A S V hA
  have topL := lt_succ_of_le (left_top_bound r r j R A S V hV)
  have topR := lt_succ_of_le (right_top_bound r r j R A S V hA)
  have pay := GaussianFastValueCut.query_budget (Γ := Γ) M t
  have first := observation_at_common_top t r j z R R B A k E T h.andE₁ h.andE₁.andE₂.andE₁
    lr lp (.eqRefl E) topL pay
  have last := observation_at_common_top t r j z S R B V l E T h.andE₂ h.andE₁.andE₂.andE₁
    lr rp (same_eta r r j R A S V hA hV).eqSymm topR pay
  have hU := unit_positive (Γ := Γ) t
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first (distance_symmetric _ _ _ _ hU last))

theorem original_certificate_overlap (j z R S B A V : PTm n) (h : Γ ⊢[PRAAx] source z R S B A V) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data j z R B A) (data j z S B V) := by
  apply GaussianNameRingLaws.equivalent_of_envelope nameF nameF _ _ (num 22)
    (name_regular j z R B A h.andE₁) (name_regular j z S B V h.andE₂)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh S) (sh B) (sh A) (sh V) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh] using
    original_diagonal (var 0) (sh j) (sh z) (sh R) (sh S) (sh B) (sh A) (sh V) hs

theorem actual_original_logarithmic_certificate_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 4) (var 5))
        (data (var 0) (var 1) (var 3) (var 4) (var 6))) :=
  closeUniv 7 (.impI (original_certificate_overlap _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCertificateOverlap
