import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStrip
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Names.Rates.GaussianNamedSmallAddendRate
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment

/-!
# Width bound for the original first Binet compact strip

The original cofinal Laplace integrand has norm at most one half.
Bound the actual left sum by half the physical width, uniformly
over its mesh and observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceLowerWindow

open_ipra
open GaussianBinetLaplaceIntegrand (meshGain cofinal_bound)
open GaussianBinetLaplaceStrip (source evaluator_at tag_inside tagNumerator fixedData subst_source)
open GaussianCompactRiemannName (grid grid_inside sampleBody sampleData sample_body_at quadrature mesh mesh_positive precision)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianNamedInverseRate (independentRate)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance constantBody constant_entry)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LaplaceEvaluator" => GaussianBinetLaplaceStrip.evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "LaplaceName" => GaussianBinetLaplaceStrip.nameF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "panelData" => GaussianBinetLaplaceStrip.data

theorem quadrature_bound (p M X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (quadrature LaplaceEvaluator p M (E+A) C E (fixedData X Y D sign R T N)) (C*one) (E*two) := by
  let f := sampleBody LaplaceEvaluator
  let x := sampleData p M (E+A) C E (fixedData X Y D sign R T N)
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody M x qzero one two := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let t := grid (var 0) (s M) (s E+s A) (s C) (s E)
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.wk
    have he := hs.andE₂.andE₁
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have hi : Δ ⊢[PRAAx] GaussianCompactRiemannName.inside (s E+s A) (s C) (s E) t :=
      grid_inside (var 0) (s M) (s E+s A) (s C) (s E) (le_trans he (le_add_right _ _)) he ms (le_of_lt Prf.hyp0)
    have tag := tag_inside t (s A) (s C) (s E) (s T) he hs.andE₂.andE₂ hi
    have v := cofinal_bound (s p) (s X) (s Y) (s D) (s sign) (s R) (s T) (tagNumerator t) (sndT t)
      (.andI hs.andE₁ (.andI hi.andE₂.andE₁ tag.andE₂))
    have read := (sample_body_at (Γ := Δ) LaplaceEvaluator (var 0) (s p) (s M) (s E+s A) (s C) (s E)
      (fixedData (s X) (s Y) (s D) (s sign) (s R) (s T) (s N))).eqTrans
      (evaluator_at .cofinal (s p) t (s X) (s Y) (s D) (s sign) (s R) (s T) (s N))
    rw [constant_entry]
    simpa only [f,x,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      GaussianRationalHorner.subst_qzero,PTm.subst_add,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_succ_self (Γ := Δ) one)).iffMpr
        (GaussianRationalReciprocal.bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) v)
  have hE := h.andE₂.andE₁
  have hTwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have zeroSum : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have zeroInt : Γ ⊢[PRAAx] leftSum constantBody M qzero C E ≐ qzero :=
    (qmul_congr (.eqRefl _) zeroSum).eqTrans (qmul_zero_right _)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (positive_product _ _ hE hTwo)).iffMp
    (distance_congr (.eqRefl _) zeroInt (.eqRefl _) (.eqRefl _)
      (GaussianCompactScalarMajorant.common_mesh_distance f constantBody M x qzero C E one two hM hE hTwo rows))

theorem name_bound (p X Y D sign R T N A C E : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) :
    Γ ⊢[PRAAx] bounded (ap2 LaplaceName p (panelData X Y D sign R T N A C E)) C (E*two) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianCompactRiemannName.name_at LaplaceEvaluator p (E+A) C E (meshGain R T) T (fixedData X Y D sign R T N)).eqSymm
    ((mul_comm C one).eqTrans (one_mul C)) (.eqRefl _)
    (quadrature_bound (precision p T) (mesh p (meshGain R T) T) X Y D sign R T N A C E h (mesh_positive p (meshGain R T) T))

private theorem width_samples (X Y D sign R T N A C E : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) :
    Γ ⊢[PRAAx] tailSamples LaplaceName (panelData X Y D sign R T N A C E) C (E*two) := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let P := s E*two
  let q := ap2 LaplaceName p (panelData (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C) (s E))
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have hp : Δ ⊢[PRAAx] le one P := positive_product _ _ hs.andE₂.andE₁ (le_succ_self one)
  have canon : Δ ⊢[PRAAx] GaussianRationalHorner.canonical q :=
    GaussianCompactRiemannName.name_canonical LaplaceEvaluator p (s E+s A) (s C) (s E) (meshGain (s R) (s T)) (s T)
      (fixedData (s X) (s Y) (s D) (s sign) (s R) (s T) (s N))
  have bound : Δ ⊢[PRAAx] bounded q (s C*unit p+P) (P*unit p) := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hp (positive_product _ _ hp (unit_positive p)) ?_
      (name_bound p (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C) (s E) hs)
    exact le_of_eq_add (d := P*P) (by ipra_ring)
  simpa only [tailSamples,Δ,s,p,P,q,Syn.shift,GaussianBinetLaplaceStrip.subst_data,PTm.subst_mul,two,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using Prf.andI canon bound

theorem left_gap_rate (X Y D sign R T N A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) :
    Γ ⊢[PRAAx] independentRate LaplaceName LaplaceName
      (panelData X Y D sign R T N (A+C₁) C₂ E) (panelData X Y D sign R T N A (C₁+C₂) E) C₁ (E*two) := by
  let a := E+A
  let L := meshGain R T
  let x := fixedData X Y D sign R T N
  let l := panelData X Y D sign R T N A C₁ E
  let r := panelData X Y D sign R T N (A+C₁) C₂ E
  let u := panelData X Y D sign R T N A (C₁+C₂) E
  let rr := GaussianCompactRiemannName.data (a+C₁) C₂ E L T x
  have he := h.andE₂.andE₁
  have hi := h.andE₂.andE₂
  have hl : Γ ⊢[PRAAx] source X Y D sign R T A C₁ E :=
    .andI h.andE₁ (.andI he (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (A+C₁) C₂)) hi))
  have hr : Γ ⊢[PRAAx] source X Y D sign R T (A+C₁) C₂ E :=
    .andI h.andE₁ (.andI he (le_congr (by ipra_ring) (.eqRefl _) hi))
  have input : Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input LaplaceEvaluator a C₁ C₂ E L T x :=
    .andI (le_trans he (le_add_right E A)) (.andI he (.andI h₁ (.andI h₂
      (.andI (le_trans (le_add_left (C₁+C₂) A) hi)
        (GaussianBinetLaplaceStrip.sampled_modulus .cofinal X Y D sign R T N A (C₁+C₂) E h)))))
  have ea : Γ ⊢[PRAAx] a+C₁ ≐ E+(A+C₁) := by dsimp only [a]; ipra_ring
  have ep : Γ ⊢[PRAAx] rr ≐ r := by
    simpa only [rr,r,GaussianBinetLaplaceStrip.data,GaussianCompactRiemannName.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (GaussianCompactRiemannName.data (var 0) (Syn.shift C₂) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x)) ea
  have addInputs : Γ ⊢[PRAAx] addData l rr ≐ addData l r := by
    simpa only [GaussianNameArithmetic.subst_addData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (addData (Syn.shift l) (var 0)) ep
  have sum : Γ ⊢[PRAAx] crossEquivalent LaplaceName (addF LaplaceName LaplaceName) u (addData l r) :=
    cross_data_congr LaplaceName (addF LaplaceName LaplaceName) _ _ _ _ (.eqRefl _) addInputs
      (GaussianCompactNamedAdditivity.name_additivity LaplaceEvaluator a C₁ C₂ E L T x input)
  have regL := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N A C₁ E hl
  have regR := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N (A+C₁) C₂ E hr
  have regU := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N A (C₁+C₂) E h
  have commute := GaussianNameRingLaws.add_commutative LaplaceName LaplaceName l r regL regR
  exact GaussianNamedSmallAddendRate.independent_rate LaplaceName LaplaceName LaplaceName r u l C₁ (E*two)
    (positive_product _ _ he (le_succ_self one)) regR regU regL
    (cross_trans _ _ _ _ _ _ sum commute) (width_samples X Y D sign R T N A C₁ E hl)

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceLowerWindow
