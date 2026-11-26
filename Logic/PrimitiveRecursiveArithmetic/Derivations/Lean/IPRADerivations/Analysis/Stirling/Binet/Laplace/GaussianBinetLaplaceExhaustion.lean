import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceSharpTail
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripHorizon
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Names.Rates.GaussianNamedSmallAddendRate

/-!
# Compact additivity and exhaustion rate for the actual Binet integral

A physical split of the same compact panel is an exact instance of
the translated quadrature additivity theorem. The terminal strip bound
then controls the actual larger and smaller named panels at independent
observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExhaustion

open_ipra
open GaussianBinetLaplaceStrip (Kernel nameF data source evaluatorF fixedData subst_data subst_source)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_data_congr crossEquivalent)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem additivity (K : Kernel) (X Y D sign R T N A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) :
    Γ ⊢[PRAAx] crossEquivalent (nameF K) (addF (nameF K) (nameF K))
      (data X Y D sign R T N A (C₁+C₂) E)
      (addData (data X Y D sign R T N A C₁ E) (data X Y D sign R T N (A+C₁) C₂ E)) := by
  let F := evaluatorF K
  let L := meshGain R T
  let x := fixedData X Y D sign R T N
  have he := h.andE₂.andE₁
  exact GaussianCompactNamedAdditivity.name_additivity_with_offset F E A C₁ C₂ E L T x
    he he h₁ h₂ h.andE₂.andE₂ (GaussianBinetLaplaceStrip.sampled_modulus K X Y D sign R T N A (C₁+C₂) E h)

private theorem tail_samples (X Y D sign R T N L C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T (D*L*E) C E)
    (hL : Γ ⊢[PRAAx] le one L) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] tailSamples (nameF .cofinal) (data X Y D sign R T N (D*L*E) C E)
      D (num 12*X*unit L) := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let a := s D*s L*s E
  let p : PTm (n+1) := var 0
  have ht : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) a (s C) (s E) :=
    by simpa only [Δ,s,a,Fm.shift,Syn.shift,subst_source,PTm.subst_mul] using h.shift
  have hl : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hL.shift
  have hc : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift
  have tail := GaussianBinetLaplaceStripTailEnvelope.integer_cutoff_bound p (s X) (s Y) (s D) (s sign)
    (s R) (s T) (s N) (s L) (s C) (s E) ht hl hc
  have canon : Δ ⊢[PRAAx] GaussianRationalHorner.canonical
      (ap2 (nameF .cofinal) p (data (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) a (s C) (s E))) :=
    GaussianCompactRiemannName.name_canonical (evaluatorF .cofinal) p
      (s E+a) (s C) (s E) (meshGain (s R) (s T)) (s T) (fixedData (s X) (s Y) (s D) (s sign) (s R) (s T) (s N))
  have bound : Δ ⊢[PRAAx] GaussianRationalMetric.bounded
      (ap2 (nameF .cofinal) p (data (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) a (s C) (s E)))
      (s D*unit p+(num 12*s X*unit (s L))) ((num 12*s X*unit (s L))*unit p) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _)
      (by dsimp only [GaussianBinetLaplaceStripTail.tailNumerator]; ipra_ring) (.eqRefl _) tail
  simpa only [tailSamples,Δ,s,p,a,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num,
    GaussianCoefficientNameBounds.subst_unit] using Prf.andI canon bound

theorem prefix_rate (X Y D sign R T N L C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T zero (D*L*E+C) E)
    (hL : Γ ⊢[PRAAx] le one L) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] independentRate (nameF .cofinal) (nameF .cofinal)
      (data X Y D sign R T N zero (D*L*E) E) (data X Y D sign R T N zero (D*L*E+C) E)
      D (num 12*X*unit L) := by
  let w := D*L*E
  let Cn := nameF .cofinal
  have he := h.andE₂.andE₁
  have hx := h.andE₁.andE₁.andE₁.andE₁
  have hd := h.andE₁.andE₁.andE₂
  have hw := positive_product (D*L) E (positive_product D L hd hL) he
  have den := positive_product (num 12*X) (unit L)
    (positive_product (num 12) X (by ipra_le 11) hx)
    (unit_positive L)
  have wide : Γ ⊢[PRAAx] le (w+C) (E*T) := le_congr (zero_add _) (.eqRefl _) h.andE₂.andE₂
  have left : Γ ⊢[PRAAx] source X Y D sign R T zero w E :=
    .andI h.andE₁ (.andI he (le_congr (zero_add w).eqSymm (.eqRefl _) (le_trans (le_add_right w C) wide)))
  have right : Γ ⊢[PRAAx] source X Y D sign R T w C E := .andI h.andE₁ (.andI he wide)
  have hx0 := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N zero w E left
  have hy0 := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N zero (w+C) E h
  have hz0 := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N w C E right
  have tail := tail_samples X Y D sign R T N L C E right hL hC
  have split := additivity .cofinal X Y D sign R T N zero w C E h hw hC
  let a := data X Y D sign R T N w C E
  let b := data X Y D sign R T N (zero+w) C E
  have ea : Γ ⊢[PRAAx] b ≐ a :=
    GaussianCompactRiemannName.data_congr (congrAdd (.eqRefl E) (zero_add w))
      (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  let c := data X Y D sign R T N zero w E
  have es : Γ ⊢[PRAAx] addData c b ≐ addData c a :=
    GaussianNameArithmetic.add_data_congr (.eqRefl c) ea
  exact GaussianNamedSmallAddendRate.independent_rate Cn Cn Cn _ _ _ D (num 12*X*unit L)
    den hx0 hy0 hz0 (cross_data_congr Cn (addF Cn Cn) _ _ _ _ (.eqRefl _) es split) tail

theorem actual_Binet_Laplace_compact_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let T := var 5
     let N := var 6
     let L := var 7
     let C := var 8
     let E := var 9
     source X Y D sign R T zero (D*L*E+C) E ⟶ le one L ⟶ le one C ⟶
       independentRate (nameF .cofinal) (nameF .cofinal)
         (data X Y D sign R T N zero (D*L*E) E) (data X Y D sign R T N zero (D*L*E+C) E)
         D (num 12*X*unit L)) :=
  closeUniv 10 (.impI (.impI (.impI (prefix_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExhaustion
