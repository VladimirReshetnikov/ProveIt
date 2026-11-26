import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseCompactBound
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactIntervalRescaling
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Names.Rates.GaussianNamedSmallAddendRate

/-!
# Alignment and initial-strip bounds for the original Bose quadrature

A common physical panel is independent of its positive denominator
and of the numerical horizon used to select observations. Additivity
and a uniform width bound control removal of a positive initial strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 560000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseCompactAlignment

open_ipra
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseCompact (nameF data subst_data evaluatorF gain source subst_source compact_input sampled_modulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_data_congr crossEquivalent cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem data_congr (X Y D sign : PTm n) {T A C E S B J F : PTm n}
    (hT : Γ ⊢[PRAAx] T ≐ S) (hA : Γ ⊢[PRAAx] A ≐ B)
    (hC : Γ ⊢[PRAAx] C ≐ J) (hE : Γ ⊢[PRAAx] E ≐ F) : Γ ⊢[PRAAx]
    data X Y D sign T A C E ≐ data X Y D sign S B J F := by
  have first : Γ ⊢[PRAAx] gain D E T ≐ gain D F T := by
    simpa only [GaussianBinetBoseCompact.subst_gain,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (gain (Syn.shift D) (var 0) (Syn.shift T)) hE
  have second : Γ ⊢[PRAAx] gain D F T ≐ gain D F S := by
    simpa only [GaussianBinetBoseCompact.subst_gain,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (gain (Syn.shift D) (Syn.shift F) (var 0)) hT
  exact congrPairT (congrAdd hE hA)
    (congrPairT hC (congrPairT hE (congrPairT (first.eqTrans second) (congrPairT hT (.eqRefl _)))))

theorem rescale (X Y D sign T S A C E k : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hk : Γ ⊢[PRAAx] le one k)
    (hu : Γ ⊢[PRAAx] le (A+C) (E*S)) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data X Y D sign T A C E)
      (data X Y D sign S (k*A) (k*C) (k*E)) := by
  let F := evaluatorF
  let x := fixedData X Y D sign
  let L := gain D E T
  let M := gain D (k*E) S
  let a := E+A
  let b := k*E+k*A
  have hs : Γ ⊢[PRAAx] source X D sign S (k*A) (k*C) (k*E) :=
    .andI h.andE₁ (.andI (positive_product _ _ hk h.andE₂.andE₁)
      (.andI (positive_product _ _ hk h.andE₂.andE₂.andE₁)
        (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl k) hu))))
  have hi : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input F k a C E L T x :=
    .andI hk (compact_input X Y D sign T A C E h)
  have mid := GaussianCompactIntervalRescaling.scaled_input F k a C E L T x hi
  have target : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F b (k*C) (k*E) M S x :=
    compact_input X Y D sign S (k*A) (k*C) (k*E) hs
  have ea : Γ ⊢[PRAAx] b ≐ k*a := by dsimp only [a,b]; ipra_ring
  let property := GaussianCompactRiemannName.input F (var 0) (Syn.shift (k*C)) (Syn.shift (k*E))
    (Syn.shift M) (Syn.shift S) (Syn.shift x)
  have target' : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F (k*a) (k*C) (k*E) M S x := by
    have initial : Γ ⊢[PRAAx] property.subst (Syn.inst b) := by
      simpa only [property,GaussianCompactRiemannName.subst_input,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using target
    simpa only [property,GaussianCompactRiemannName.subst_input,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqSubst1 property ea initial
  have eg : Γ ⊢[PRAAx] GaussianCompactRiemannName.data (k*a) (k*C) (k*E) M S x ≐
      data X Y D sign S (k*A) (k*C) (k*E) :=
    GaussianCompactRiemannName.data_congr ea.eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  exact cross_data_congr nameF nameF _ _ _ _ (.eqRefl _) eg
    (cross_trans _ _ _ _ _ _ (GaussianCompactIntervalRescaling.name_rescaling F k a C E L T x hi)
      (GaussianCompactMeshIndependence.name_independence F (k*a) (k*C) (k*E) L T M S x (.andI mid target')))

theorem additivity (X Y D sign T A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data X Y D sign T A (C₁+C₂) E)
      (addData (data X Y D sign T A C₁ E) (data X Y D sign T (A+C₁) C₂ E)) := by
  let F := evaluatorF
  let x := fixedData X Y D sign
  let L := gain D E T
  have he := h.andE₂.andE₂.andE₁
  exact GaussianCompactNamedAdditivity.name_additivity_with_offset F E A C₁ C₂ E L T x
    he he h₁ h₂ h.andE₂.andE₂.andE₂ (sampled_modulus X Y D sign T A (C₁+C₂) E h)

theorem width_samples (X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) : Γ ⊢[PRAAx]
    tailSamples nameF (data X Y D sign T A C E) (C*D) (E*(num 4*X)) := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let P := s E*(num 4*s X)
  let q := ap2 nameF p (data (s X) (s Y) (s D) (s sign) (s T) (s A) (s C) (s E))
  have hs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have hp : Δ ⊢[PRAAx] le one P :=
    positive_product _ _ hs.andE₂.andE₂.andE₁ (positive_product _ _ (by ipra_le 3) hs.andE₁.andE₁.andE₁)
  have canon : Δ ⊢[PRAAx] GaussianRationalHorner.canonical q :=
    GaussianCompactRiemannName.name_canonical evaluatorF p (s E+s A) (s C) (s E)
      (gain (s D) (s E) (s T)) (s T) (fixedData (s X) (s Y) (s D) (s sign))
  have majorant : Δ ⊢[PRAAx] bounded q (s C*s D*unit p+P) (P*unit p) := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hp
      (positive_product _ _ hp (unit_positive p)) ?_
      (GaussianBinetBoseCompactBound.name_bound p (s X) (s Y) (s D) (s sign) (s T) (s A) (s C) (s E) hs)
    exact le_of_eq_add (d := P*P) (by ipra_ring)
  simpa only [tailSamples,Δ,s,p,P,q,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num] using Prf.andI canon majorant

theorem left_gap_rate (X Y D sign T A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data X Y D sign T (A+C₁) C₂ E) (data X Y D sign T A (C₁+C₂) E)
      (C₁*D) (E*(num 4*X)) := by
  have zs := h.andE₁
  have ha := h.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₁
  have hi := h.andE₂.andE₂.andE₂
  have widen : Γ ⊢[PRAAx] le (A+C₁) (A+(C₁+C₂)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right (A+C₁) C₂)
  have hl : Γ ⊢[PRAAx] source X D sign T A C₁ E :=
    .andI zs (.andI ha (.andI he (le_trans widen hi)))
  have hr : Γ ⊢[PRAAx] source X D sign T (A+C₁) C₂ E :=
    .andI zs (.andI (le_trans ha (le_add_right A C₁)) (.andI he (le_congr (by ipra_ring) (.eqRefl _) hi)))
  have den := positive_product _ _ he (positive_product (num 4) X (by ipra_le 3) zs.andE₁.andE₁)
  let l := data X Y D sign T A C₁ E
  let r := data X Y D sign T (A+C₁) C₂ E
  let u := data X Y D sign T A (C₁+C₂) E
  have rl := GaussianBinetBoseCompact.regular X Y D sign T A C₁ E hl
  have rr := GaussianBinetBoseCompact.regular X Y D sign T (A+C₁) C₂ E hr
  have ru := GaussianBinetBoseCompact.regular X Y D sign T A (C₁+C₂) E h
  have sum := additivity X Y D sign T A C₁ C₂ E h h₁ h₂
  have commute := GaussianNameRingLaws.add_commutative nameF nameF l r rl rr
  exact GaussianNamedSmallAddendRate.independent_rate nameF nameF nameF r u l (C₁*D) (E*(num 4*X)) den rr ru rl
    (cross_trans _ _ _ _ _ _ sum commute) (width_samples X Y D sign T A C₁ E hl)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseCompactAlignment
