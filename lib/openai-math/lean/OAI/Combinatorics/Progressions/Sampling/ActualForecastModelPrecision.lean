/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
import OAI.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
import OAI.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral

namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def forecastCoverCutoffInput (period : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  fun a => period • z ⟨a.1, a.2.2⟩

theorem forecastCoverCutoffInput_lipschitz (period : ℕ) :
    LipschitzWith (period : ℝ≥0) (forecastCoverCutoffInput (J := J) period) :=
  torus_nsmul_reindex_lipschitz
    (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J => (⟨a.1, a.2.2⟩ : Σ j, J j)) period

omit [∀ j, Fintype (J j)] in
theorem forecastCoverCutoffInput_physicalGridFactorInput {X : Type*}
    (period : ℕ) [NeZero period]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    forecastCoverCutoffInput period (physicalGridFactorInput period p t) =
      fun a => (eval t (p a.1) a.2.2 : UnitAddCircle) := by
  have hp : (period : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne period)
  funext a
  simp only [forecastCoverCutoffInput, physicalGridFactorInput,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  field_simp

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_forecast_early_approximation_budget (m Dmod d : ℕ)
    {D pcap Pscale Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D) (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hsm : 0 ≤ Psm) (hlip : 0 ≤ Plip) (hbad : 0 ≤ Pbad)
    (hpres : 0 ≤ Ppres) (hE : 0 ≤ E) (hspatial : 0 ≤ Pspatial)
    (hcoord : 0 ≤ Pcoord) (hcut : 0 ≤ Pcut) :
    let W := 4 * (Pscale + 8)
    let Pin := D * (VectorPolynomial.allocatedInactivePointCapLog m D pcap 0 + W)
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let O := VectorPolynomial.allocatedInactiveJointSiteLog m D (pcap + V) V (Esite + D * W) + W
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pin ∧ 0 ≤ V ∧ 0 ≤ Esite ∧ 0 ≤ O ∧ 0 ≤ Pnative ∧
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp Esite ∧
      (∀ (Rbad Qpres : ℕ) (H I : ℝ),
        0 ≤ H → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
        H * (I * ((((Rbad * Qpres : ℕ) : ℝ) ^
          (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
            modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
      (∀ (H C : ℝ), 0 ≤ H → H ≤ Real.exp Psm → 0 ≤ C → C ≤ Real.exp Pdec →
        H * Real.exp Pin * (1 + C) ≤ Real.exp Pcap) ∧
      (∀ (a : ℕ) (H : ℝ), (a : ℝ) ≤ D → 0 ≤ H → H ≤ Real.exp Psm →
        2 * H * ((T : ℝ) ^ d * Real.exp (a * O)) ≤ Real.exp Pmass) ∧
      (∀ (a : ℕ) (q : ℕ) (L Lsp : ℝ≥0), (a : ℝ) ≤ D →
        (q : ℝ) ≤ Real.exp (V + a * O) → (L : ℝ) ≤ Real.exp Plip →
        (Lsp : ℝ) ≤ Real.exp Pspatial →
        (q : ℝ) ≤ Real.exp Pnative ∧
        (((L + a * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lsp : ℝ≥0) : ℝ) ≤
          Real.exp Pnative) ∧
      Real.exp Pcoord ≤ Real.exp Pnative ∧ Real.exp Pcut ≤ Real.exp Pnative := by
  intro W Pin Pdec V Esite O Pperiod Pfactor Pnative Pmass Pcap
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hPin : 0 ≤ Pin := mul_nonneg hD (add_nonneg
    (VectorPolynomial.allocatedInactivePointCapLog_nonneg m hD hpcap (le_refl 0)) hW)
  have hPdec : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hEs : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hO : 0 ≤ O := add_nonneg
    (VectorPolynomial.allocatedInactiveJointLogs_nonneg m hD (add_nonneg hpcap hV) hV
      (add_nonneg hEs (mul_nonneg hD hW))).2 hW
  have hperiod : 0 ≤ Pperiod := add_nonneg hV (mul_nonneg hD hO)
  have hfactor : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hn : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  obtain ⟨T, δ, hT, hTv, hδ, hδ1, hδb, he⟩ :=
    exists_forecast_modular_approximation_parameters m Dmod d hsm hPin hbad hpres hE
  refine ⟨hPin, hV, hEs, hO, hn, T, δ, hT, hTv, hδ, hδ1, hδb, he, ?_, ?_, ?_, ?_, ?_⟩
  · intro H C hH hHb hC hCb
    have hsum : 1 + C ≤ 2 * Real.exp Pdec := by
      have h1 := Real.one_le_exp_iff.mpr hPdec
      linarith
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp Psm * Real.exp Pin * (2 * Real.exp Pdec) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hHb (Real.exp_nonneg _)) hsum
          (by positivity) (by positivity)
      _ ≤ Real.exp Psm * Real.exp Pin * (Real.exp 1 * Real.exp Pdec) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity)
      _ = Real.exp Pcap := by simp only [Pcap, Real.exp_add]; ring
  · intro a H ha hH hHb
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) hTv d
    have hao : Real.exp ((a : ℝ) * O) ≤ Real.exp (D * O) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hO)
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp Psm * ((Real.exp V) ^ d * Real.exp (D * O)) :=
        mul_le_mul (mul_le_mul htwo hHb hH (Real.exp_nonneg _))
          (mul_le_mul hp hao (Real.exp_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = Real.exp Pmass := by rw [← Real.exp_nat_mul]; simp only [Pmass, Real.exp_add]; ring
  · intro a q L Lsp ha hq hL hLsp
    have hpq : V + a * O ≤ Pperiod := by
      dsimp only [Pperiod]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ha hO)
    have hpN : Pperiod ≤ Pnative := by dsimp only [Pnative]; linarith
    refine ⟨hq.trans (Real.exp_le_exp.mpr (hpq.trans hpN)), ?_⟩
    have haexp : (a : ℝ) ≤ Real.exp D := ha.trans (by linarith [Real.add_one_le_exp D])
    have hsum : (L : ℝ) + a * Real.exp O ≤ Real.exp (Plip + D + O + 1) := by
      have h1 : (L : ℝ) ≤ Real.exp (Plip + D + O) :=
        hL.trans (Real.exp_le_exp.mpr (by linarith))
      have h2 : (a : ℝ) * Real.exp O ≤ Real.exp (Plip + D + O) := by
        calc
          _ ≤ Real.exp D * Real.exp O := mul_le_mul_of_nonneg_right haexp (Real.exp_nonneg _)
          _ = Real.exp (D + O) := (Real.exp_add _ _).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        _ ≤ 2 * Real.exp (Plip + D + O) := by linarith
        _ ≤ Real.exp 1 * Real.exp (Plip + D + O) :=
          mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hfactorN : Pfactor ≤ Pnative := by dsimp only [Pnative]; linarith
    simp only [NNReal.coe_mul, NNReal.coe_add]
    calc
      _ ≤ Real.exp (Plip + D + O + 1) * Real.exp Pspatial :=
        mul_le_mul hsum hLsp (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp Pfactor := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfactorN
  · apply Real.exp_le_exp.mpr
    dsimp only [Pnative]
    linarith
  · apply Real.exp_le_exp.mpr
    dsimp only [Pnative]
    linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_forecast_early_native_family_budget
    {X : Type*} [Fintype X]
    (m Dmod d : ℕ) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (localBudget : ℝ)
    {D pcap Pscale Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D) (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hsm : 0 ≤ Psm) (hlip : 0 ≤ Plip) (hbad : 0 ≤ Pbad)
    (hpres : 0 ≤ Ppres) (hE : 0 ≤ E) (hspatial : 0 ≤ Pspatial)
    (hcoord : 0 ≤ Pcoord) (hcut : 0 ≤ Pcut) :
    let W := 4 * (Pscale + 8)
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + W)
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let O := allocatedInactiveJointSiteLog m D (pcap + V) V (Esite + D * W) + W
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    let budget := max localBudget (3 * Pnative + 3)
    0 ≤ Pnative ∧ 2 ≤ budget ∧
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp Esite ∧
      ∀ (H Icap : ℝ) (Rbad Qpres a dactual : ℕ),
        0 ≤ H → H ≤ Real.exp Psm → Icap ≤ Real.exp Pin →
        (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres → (a : ℝ) ≤ D → dactual ≤ d →
        let Cdecay := ((Rbad * Qpres : ℕ) : ℝ) ^
          (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m)
        H * Real.exp Pin * (1 + Cdecay) ≤ Real.exp Pcap ∧
        ∀ {Term Ω : Type*} [Fintype Term],
        ∀ (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
              (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
              ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
          (coeff : Term → ℂ) (N : X → ℕ)
          (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) (target : Ω → ℂ),
          (∑ t, ‖coeff t‖) ≤ 2 * H * ((T : ℝ) ^ dactual * Real.exp (a * O)) →
          (∀ y, ‖target y - ∑ t, coeff t * (twists t).eval N poly (sample y)‖ ≤
            H * (Icap * (Cdecay / T) + (T : ℝ) ^ dactual * δ)) →
          (∀ t, (fun y => (twists t).eval N poly (sample y)) ∈
            twistedNativeSampleFunctions w degree budget sample
              (fun (V : NormalizedPolynomialTwist X (Σ j, J j)
                (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) y =>
                  V.eval N poly (sample y))) ∧
          (twistedNativeSampleFunctions w degree localBudget sample
              (fun (V : NormalizedPolynomialTwist X (Σ j, J j)
                (Real.exp localBudget) (Real.exp localBudget)
                ⟨Real.exp localBudget, Real.exp_nonneg _⟩) y => V.eval N poly (sample y)) ⊆
            twistedNativeSampleFunctions w degree budget sample
              (fun (V : NormalizedPolynomialTwist X (Σ j, J j)
                (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) y =>
                  V.eval N poly (sample y))) ∧
          (∑ t, ‖coeff t‖) ≤ Real.exp Pmass ∧
          ∀ y, ‖target y - ∑ t, coeff t * (twists t).eval N poly (sample y)‖ ≤ Real.exp (-E) := by
  intro W Pin Pdec V Esite O Pperiod Pfactor Pnative Pmass Pcap budget
  obtain ⟨_, _, _, _, hN, T, δ, hT, hTv, hδ, hδ1, hδb,
      herror, hcap, hmass, _, _, _⟩ :=
    exists_forecast_early_approximation_budget m Dmod d hD hpcap hscale hsm hlip
      hbad hpres hE hspatial hcoord hcut
  have hbudget : 2 ≤ budget :=
    (show (2 : ℝ) ≤ 3 * Pnative + 3 by linarith).trans (le_max_right _ _)
  refine ⟨hN, hbudget, T, δ, hT, hTv, hδ, hδ1, hδb, ?_⟩
  intro H Icap Rbad Qpres a dactual hH hHb hI hRbad hQpres ha hdegree Cdecay
  have hdecay : Cdecay ≤ Real.exp Pdec := forecastModularCharge_exp_bound m Dmod Rbad Qpres hRbad hQpres
  refine ⟨hcap H Cdecay hH hHb (Real.rpow_nonneg (Nat.cast_nonneg _) _) hdecay, ?_⟩
  intro Term Ω instTerm twists coeff N poly sample w degree target hcoeff happrox
  have hfamily := forecastFiniteTwists_common_family localBudget Pnative hN twists N poly sample w degree
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  have hpow : (T : ℝ) ^ dactual ≤ (T : ℝ) ^ d := pow_le_pow_right₀ hTone hdegree
  have hcoeff' : (∑ t, ‖coeff t‖) ≤ 2 * H * ((T : ℝ) ^ d * Real.exp (a * O)) :=
    hcoeff.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) (by positivity))
  refine ⟨hfamily.1, hfamily.2, hcoeff'.trans (hmass a H ha hH hHb), ?_⟩
  intro y
  exact ((happrox y).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hpow hδ.le)) hH)).trans
      (herror Rbad Qpres H Icap hH hHb hI hRbad hQpres)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {Y : Type*} [PseudoMetricSpace Y]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

noncomputable def forecastBufferedFullResidue (w : MixedCoveredJetSource I single E n d) :
    ∀ j, Fin (n j) ⊕ E j → ZMod period :=
  fun j => Sum.elim (fun i => ((w.1 j).2 i () : ZMod period))
    (fun i => ((w.2 j () i).val : ZMod period))

noncomputable def forecastBufferedCoveredSiteFactor
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()) *
    F (forecastBufferedFullResidue d period w)
      (s, allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())))

omit [NeZero period] [PseudoMetricSpace Y] in
theorem forecastBufferedCoveredSiteFactor_on_chart
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (w : MixedCoveredJetSource I single E n d) (hw : w ∈ region) :
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s (chart w) =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) (chart w) *
        F (forecastBufferedFullResidue d period w)
          (s, allocatedFullMixedSiteValue (R := R) U b
            (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [forecastBufferedCoveredSiteFactor, allocatedBufferedSiteChartFactor,
    restrictedComplexChartDensity_apply _ _ _ _ hinj hw, Complex.ofReal_one, one_mul]

omit [NeZero period] [PseudoMetricSpace Y] in
theorem forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (y : EuclideanJetLayers U single)
    (hy : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0) :
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s y = 0 := by
  by_cases hmem : y ∈ chart '' region
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr period F s w hw,
      hy, zero_mul]
  · unfold forecastBufferedCoveredSiteFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

theorem exists_forecast_buffered_cover_factor
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hf : ∀ a, LipschitzWith L (F a)) (hf1 : ∀ a z, ‖F a z‖ ≤ 1) :
    ∃ g : Y × ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith
        (max ((L * max 1 (K * ∑ j, Cforward j * Fintype.card (J j))) *
          max 1 (period : ℝ≥0)) (4 * period)) g ∧
      (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ (s : Y) (u : ∀ j, euclideanSubspace (U j)) (y : EuclideanJetLayers U single),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j ()) →
        forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s y =
          2 * (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) *
            g (s, fun a => (((u a.1).val a.2 / period : ℝ) : UnitAddCircle)) := by
  classical
  let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
  let coordinates := fun v : (Σ j, J j) → ℝ =>
    allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v)
  have hcoord : LipschitzWith Lcoord coordinates := by
    simpa only [Lcoord, coordinates, mul_one, Function.comp_def] using
      (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK).comp
        singleSiteFromLayered_lipschitz
  have hprod : LipschitzWith (max 1 Lcoord)
      (fun p : Y × ((Σ j, J j) → ℝ) => (p.1, coordinates p.2)) := by
    simpa only [mul_one, Function.comp_def] using
      (LipschitzWith.prod_fst.prodMk (hcoord.comp LipschitzWith.prod_snd))
  let Fambient := fun a (p : Y × ((Σ j, J j) → ℝ)) => F a (p.1, coordinates p.2)
  have hFl (a) : LipschitzWith (L * max 1 Lcoord) (Fambient a) :=
    (hf a).comp hprod
  have hFb (a) (v) : ‖Fambient a v‖ ≤ (1 : ℝ≥0) := hf1 a _
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_parametric_layered_full_residue_covered_extension
    (fun j => euclideanSubspace (U j)) bW b hb period d hdiv Fambient
      (L * max 1 Lcoord) 1 hFl hFb
  refine ⟨fun z => g₀ z / 2, ?_, ?_, ?_⟩
  · apply lipschitz_complex_div_two
    simpa only [mul_one, Lcoord] using hg₀
  · intro z
    apply complex_div_two_norm_le
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, mul_one] using hgb z
  · intro s u y hu
    have hcut := allocatedBufferedTorusCutoff_eq_siteChart U b o r hr hR C hC hchart hbudget B S hb bW d y
    by_cases hc : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0
    · rw [forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero B U b S o hb bW d r hr period F s y hc,
        hcut, hc, mul_zero, zero_mul]
    have hy : y ∈ chart '' region := by
      by_contra hn
      exact hc (restrictedComplexChartDensity_zero _ _ _ _ hn)
    obtain ⟨w, hw, rfl⟩ := hy
    have hu' (j : Fin m) : (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()), w.2 j ()) := hu j
    have hsmall (j : Fin m) (i : J j) :
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ())) i| ≤ 1 / 4 :=
      (hw j (mem_univ j) () (mem_univ ())).1 i
    have hv := hgv s u (fun j => orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()))
      (fun j => w.2 j ()) hu' hsmall
    dsimp only [Fambient, coordinates] at hv
    rw [allocatedFullAmbientSiteCoordinates_layered_point (R := R) U b o
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())] at hv
    change g₀ _ = F (forecastBufferedFullResidue d period w)
      (s, allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) at hv
    dsimp only
    rw [hv, forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr period F s w hw,
      hcut]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {X : Type*} [Fintype X]

theorem exists_forecast_buffered_normalized_twist
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (mask : (X → ZMod period) → ℂ) (hmask : ∀ a, ‖mask a‖ ≤ 1)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hf : ∀ a, LipschitzWith L (F a)) (hf1 : ∀ a z, ‖F a z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lg := max ((L * max 1 Lcoord) * max 1 (period : ℝ≥0)) (4 * period)
    let Lout := Lcut * period + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) period period Lout,
      twist.modulus = period ∧ twist.cover = period ∧
      ∀ (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hp : ∀ j e, coefficients (p j) e ∈ U j) (u : X → ℤ),
        mask (fun i => (u i : ZMod period)) *
          forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F
            (fun i => (u i : ℝ) / N i)
            (BooleanCubeKernel.physicalSingleSiteValue U d p hp (fun i => (u i : ℝ))) =
          2 * twist.eval N p u := by
  intro Lcoord Lcut Lg Lout
  obtain ⟨g, hg, hgb, hgv⟩ := exists_forecast_buffered_cover_factor B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK F hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  have hχCL : LipschitzWith (Lcut * period)
      (fun z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle) =>
        (χ (forecastCoverCutoffInput period z.2) : ℂ)) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp
        ((hχL.comp (forecastCoverCutoffInput_lipschitz period)).comp LipschitzWith.prod_snd)
  have hχb (z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle)) :
      ‖(χ (forecastCoverCutoffInput period z.2) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  let smooth := fun z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle) =>
    (χ (forecastCoverCutoffInput period z.2) : ℂ) * g z
  have hsmooth : LipschitzWith Lout smooth := by
    simpa only [one_mul, mul_one, add_comm, Function.comp_def, smooth, Lout, Lg] using
      lipschitz_mul_of_bounds _ _ hχCL hg (Bf := 1) (Bg := 1) hχb hgb
  have hsmoothb (z) : ‖smooth z‖ ≤ 1 := by
    dsimp only [smooth]
    rw [norm_mul]
    exact (mul_le_mul (hχb z) (hgb z) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  let twist : NormalizedPolynomialTwist X (Σ j, J j) period period Lout :=
    { modulus := period
      modulus_pos := Nat.pos_of_ne_zero (NeZero.ne period)
      modulus_bound := le_rfl
      cover := period
      cover_pos := Nat.pos_of_ne_zero (NeZero.ne period)
      cover_bound := le_rfl
      mask := mask
      mask_bound := hmask
      smooth := smooth
      smooth_bound := hsmoothb
      smooth_lipschitz := hsmooth }
  refine ⟨twist, rfl, rfl, ?_⟩
  intro N p hp u
  have h := hgv (fun i => (u i : ℝ) / N i)
    (BooleanCubeKernel.physicalEuclideanSitePoint U p hp (fun i => (u i : ℝ)))
    (BooleanCubeKernel.physicalSingleSiteValue U d p hp (fun i => (u i : ℝ)))
    (fun j => (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hp d
      (fun i => (u i : ℝ)) j).symm)
  rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at h
  simp only [BooleanCubeKernel.physicalEuclideanSitePoint_apply] at h
  dsimp only [NormalizedPolynomialTwist.eval, twist, smooth]
  rw [forecastCoverCutoffInput_physicalGridFactorInput]
  rw [h]
  dsimp only [χ]
  unfold physicalGridFactorInput
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem forecast_spatial_coordinate_exp_bound {τ Pτ : ℝ}
    (hτ : 0 < τ) (hPτ : 0 ≤ Pτ) (hτinv : τ⁻¹ ≤ Real.exp Pτ) :
    (max ⟨8 / τ, by positivity⟩ 1 : ℝ≥0) ≤
      ⟨Real.exp (Pτ + 8), Real.exp_nonneg _⟩ := by
  change max (8 / τ) (1 : ℝ) ≤ Real.exp (Pτ + 8)
  apply max_le
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    rw [div_eq_mul_inv, Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hτinv (by norm_num)).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left h8 (Real.exp_nonneg Pτ))
  · exact Real.one_le_exp_iff.mpr (by linarith)

theorem forecast_ambient_coordinate_cutoff_exp_bounds
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {Axis : Type*} [Fintype Axis]
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D PK PF : ℝ} (_hD : 0 ≤ D) (_hPK : 0 ≤ PK) (_hPF : 0 ≤ PF)
    (hdim : (∑ j, Fintype.card (J j) : ℕ) ≤ D)
    (haxes : (Fintype.card Axis : ℝ) ≤ D)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card Axis * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    (Lcoord : ℝ) ≤ Real.exp (PK + PF + D) ∧
    (Lcut : ℝ) ≤ Real.exp (PK + PF + 2 * D + normalizedSiteCutoffBound + 1) := by
  intro Lcoord Lcut
  have hDexp : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hsum : (∑ j, (forward j : ℝ) * Fintype.card (J j)) ≤ Real.exp PF * D := by
    calc
      _ ≤ ∑ j, Real.exp PF * Fintype.card (J j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hforward j) (Nat.cast_nonneg _))
      _ = Real.exp PF * (∑ j, (Fintype.card (J j) : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hdim) (Real.exp_nonneg _)
  have hc : (Lcoord : ℝ) ≤ Real.exp (PK + PF + D) := by
    dsimp only [Lcoord]
    simp only [NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp PK * (Real.exp PF * D) :=
        mul_le_mul hK hsum (by positivity) (Real.exp_nonneg _)
      _ ≤ Real.exp PK * (Real.exp PF * Real.exp D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDexp (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by simp only [Real.exp_add]; ring
  refine ⟨hc, ?_⟩
  have hr' : (1 : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast (show (1 : ℝ≥0) ≤ 2 * r by nlinarith)
  have hq : ((Fintype.card Axis * normalizedSiteCutoffBound / (2 * r) : ℝ≥0) : ℝ) ≤
      Real.exp (D + normalizedSiteCutoffBound + 1) := by
    change (Fintype.card Axis : ℝ) * normalizedSiteCutoffBound / (2 * (r : ℝ)) ≤ _
    have hb : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp (normalizedSiteCutoffBound + 1) := by
      linarith [Real.add_one_le_exp ((normalizedSiteCutoffBound : ℝ) + 1)]
    calc
      _ ≤ (Fintype.card Axis : ℝ) * normalizedSiteCutoffBound :=
        div_le_self (by positivity) hr'
      _ ≤ Real.exp D * Real.exp (normalizedSiteCutoffBound + 1) :=
        mul_le_mul (haxes.trans hDexp) hb (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  change ((Fintype.card Axis * normalizedSiteCutoffBound / (2 * r) : ℝ≥0) : ℝ) * (Lcoord : ℝ) ≤ _
  calc
    _ ≤ Real.exp (D + normalizedSiteCutoffBound + 1) * Real.exp (PK + PF + D) :=
      mul_le_mul hq hc (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_preparedFixedSpatialForecastParameters
    {m : ℕ} (Dmod d : ℕ)
    {X : Type*} [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P δslice : ℝ} (hP : 1 ≤ P) (hδslice : 0 < δslice)
    (hδsliceInv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D pcap Pscale Pbad Ppres E Pτ PK PF τ : ℝ}
    (hD : 0 ≤ D) (hDP : D ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D)
    (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
    (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let Psm := forecastOriginalSmoothBudget m P
    let Pspatial := Pτ + 8
    let Pcoord := PK + PF + D
    let Pcut := PK + PF + 2 * D + normalizedSiteCutoffBound + 1
    let Lsp : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let W := 4 * (Pscale + 8)
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + W)
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let O := allocatedInactiveJointSiteLog m D (pcap + V) V (Esite + D * W) + W
    let Pperiod := V + D * O
    let Pfactor := Psm + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pin ∧ 0 ≤ V ∧ 0 ≤ Esite ∧ 0 ≤ O ∧ 0 ≤ Pnative ∧
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp Esite ∧
      ∀ A₀ A₁ : (X → ℝ) ≃L[ℝ] (X → ℝ),
        inverseJacobian A₁ ≤ Real.exp P → ‖A₀.symm.toContinuousLinearMap‖ ≤ Real.exp P →
        let H := (fixedSpatialOriginalForecastCap B A₁ hδslice : ℝ) + 1
        let L := fixedSpatialOriginalForecastLip B A₀ A₁ hδslice
        H ≤ Real.exp Psm ∧ (L : ℝ) ≤ Real.exp Psm ∧
        (∀ (Rbad Qpres : ℕ) (Icap : ℝ), Icap ≤ Real.exp Pin →
          (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
          H * (Icap * ((((Rbad * Qpres : ℕ) : ℝ) ^
            (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
              modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
        (∀ C : ℝ, 0 ≤ C → C ≤ Real.exp Pdec →
          H * Real.exp Pin * (1 + C) ≤ Real.exp Pcap) ∧
        (∀ a : ℕ, (a : ℝ) ≤ D →
          2 * H * ((T : ℝ) ^ d * Real.exp (a * O)) ≤ Real.exp Pmass) ∧
        (∀ (a q : ℕ), (a : ℝ) ≤ D → (q : ℝ) ≤ Real.exp (V + a * O) →
          (q : ℝ) ≤ Real.exp Pnative ∧
          (((L + a * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lsp : ℝ≥0) : ℝ) ≤ Real.exp Pnative) ∧
        (Lcoord : ℝ) ≤ Real.exp Pnative ∧ (Lcut : ℝ) ≤ Real.exp Pnative := by
  intro Psm Pspatial Pcoord Pcut Lsp Lcoord Lcut W Pin Pdec V Esite O Pperiod Pfactor Pnative Pmass Pcap
  have hsm : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m (zero_le_one.trans hP)).1
  have hspatial : 0 ≤ Pspatial := by dsimp only [Pspatial]; positivity
  have hcoord : 0 ≤ Pcoord := by dsimp only [Pcoord]; positivity
  have hcut : 0 ≤ Pcut := by dsimp only [Pcut]; positivity
  have hparameters := exists_forecast_early_approximation_budget m Dmod d
    hD hpcap hscale hsm hsm hbad hpres hE hspatial hcoord hcut
  obtain ⟨hPin, hV, hEsite, hO, hN, T, δ, hT, hTv, hδ, hδ1, hδb,
    herror, hcap, hmass, hfactor, hcoordN, hcutN⟩ := hparameters
  have hgeometry := forecast_ambient_coordinate_cutoff_exp_bounds
    (J := J) (Axis := LayerSamplerAxis I n) forward K r hD hPK hPF hdim haxes hforward hK hr
  have hspatialBound : (Lsp : ℝ) ≤ Real.exp Pspatial := by
    exact NNReal.coe_le_coe.mpr (forecast_spatial_coordinate_exp_bound hτ hPτ hτinv)
  refine ⟨hPin, hV, hEsite, hO, hN, T, δ, hT, hTv, hδ, hδ1, hδb, ?_⟩
  intro A₀ A₁ hjac hinverse H L
  have hactual := fixedSpatialOriginalForecast_uniform_budget B A₀ A₁ hP hδslice
    hδsliceInv hX (haxes.trans hDP) hblocks hjac hinverse
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨hactual.1, hactual.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Rbad Qpres Icap hI hRbad hQpres
    exact herror Rbad Qpres H Icap hH hactual.1 hI hRbad hQpres
  · intro C hC hCb
    exact hcap H C hH hactual.1 hC hCb
  · intro a ha
    exact hmass a H ha hH hactual.1
  · intro a q ha hq
    exact hfactor a q L Lsp ha hq hactual.2 hspatialBound
  · exact hgeometry.1.trans hcoordN
  · exact hgeometry.2.trans hcutN

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

structure ActualFixedSpatialForecastLogs where
  sm : ℝ
  spatial : ℝ
  coord : ℝ
  cut : ℝ
  W : ℝ
  Pin : ℝ
  Pdec : ℝ
  V : ℝ
  Esite : ℝ
  O : ℝ
  period : ℝ
  factor : ℝ
  native : ℝ
  mass : ℝ
  cap : ℝ

noncomputable def actualFixedSpatialForecastLogs (m Dmod d : ℕ)
    (P D pcap Pscale Pbad Ppres E Pτ PK PF : ℝ) : ActualFixedSpatialForecastLogs :=
  let sm := forecastOriginalSmoothBudget m P
  let spatial := Pτ + 8
  let coord := PK + PF + D
  let cut := PK + PF + 2 * D + normalizedSiteCutoffBound + 1
  let W := 4 * (Pscale + 8)
  let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + W)
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  let V := Pin + Pdec + (E + sm) + 3
  let Esite := E + sm + 1 + d * V
  let O := allocatedInactiveJointSiteLog m D (pcap + V) V (Esite + D * W) + W
  let period := V + D * O
  let factor := sm + D + O + 1 + spatial
  let native := period + factor + coord + cut + 1
  let mass := sm + d * V + D * O + 1
  let cap := sm + Pin + Pdec + 1
  ⟨sm, spatial, coord, cut, W, Pin, Pdec, V, Esite, O, period, factor, native, mass, cap⟩

structure ActualFixedSpatialForecastLogs.Nonnegative (q : ActualFixedSpatialForecastLogs) : Prop where
  sm : 0 ≤ q.sm
  spatial : 0 ≤ q.spatial
  coord : 0 ≤ q.coord
  cut : 0 ≤ q.cut
  W : 0 ≤ q.W
  Pin : 0 ≤ q.Pin
  Pdec : 0 ≤ q.Pdec
  V : 0 ≤ q.V
  Esite : 0 ≤ q.Esite
  O : 0 ≤ q.O
  period : 0 ≤ q.period
  factor : 0 ≤ q.factor
  native : 0 ≤ q.native
  mass : 0 ≤ q.mass
  cap : 0 ≤ q.cap

variable (m Dmod d : ℕ)
variable {P D pcap Pscale Pbad Ppres E Pτ PK PF : ℝ}
variable (hP : 1 ≤ P) (hD : 0 ≤ D) (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
variable (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
variable (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)

include hP hD hpcap hscale hbad hpres hE hPτ hPK hPF

theorem actualFixedSpatialForecastLogs_nonneg :
    (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres E Pτ PK PF).Nonnegative := by
  let q := actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres E Pτ PK PF
  have hsm : 0 ≤ q.sm := (forecastOriginalSmoothBudget_bounds m (zero_le_one.trans hP)).1
  have hspatial : 0 ≤ q.spatial := by change 0 ≤ Pτ + 8; positivity
  have hcoord : 0 ≤ q.coord := by change 0 ≤ PK + PF + D; positivity
  have hcut : 0 ≤ q.cut := by
    change 0 ≤ PK + PF + 2 * D + normalizedSiteCutoffBound + 1
    positivity
  have hW : 0 ≤ q.W := by change 0 ≤ 4 * (Pscale + 8); positivity
  have hPin : 0 ≤ q.Pin := mul_nonneg hD (add_nonneg
    (allocatedInactivePointCapLog_nonneg m hD hpcap (le_refl 0)) hW)
  have hPdec : 0 ≤ q.Pdec := by
    change 0 ≤ (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    positivity
  have hV : 0 ≤ q.V := by change 0 ≤ q.Pin + q.Pdec + (E + q.sm) + 3; positivity
  have hEsite : 0 ≤ q.Esite := by change 0 ≤ E + q.sm + 1 + d * q.V; positivity
  have hO : 0 ≤ q.O := add_nonneg
    (allocatedInactiveJointLogs_nonneg m hD (add_nonneg hpcap hV) hV
      (add_nonneg hEsite (mul_nonneg hD hW))).2 hW
  have hperiod : 0 ≤ q.period := add_nonneg hV (mul_nonneg hD hO)
  have hfactor : 0 ≤ q.factor := by change 0 ≤ q.sm + D + q.O + 1 + q.spatial; positivity
  have hnative : 0 ≤ q.native := by
    change 0 ≤ q.period + q.factor + q.coord + q.cut + 1
    positivity
  have hmass : 0 ≤ q.mass := by change 0 ≤ q.sm + d * q.V + D * q.O + 1; positivity
  have hcap : 0 ≤ q.cap := by change 0 ≤ q.sm + q.Pin + q.Pdec + 1; positivity
  exact ⟨hsm, hspatial, hcoord, hcut, hW, hPin, hPdec, hV, hEsite,
    hO, hperiod, hfactor, hnative, hmass, hcap⟩

include hP hD hpcap hscale hbad hpres hE hPτ hPK hPF

theorem actualFixedSpatialForecastLogs_period_le_native (a : ℕ) (ha : (a : ℝ) ≤ D) :
    let q := actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres E Pτ PK PF
    q.V + a * q.O ≤ q.native := by
  intro q
  have hq := actualFixedSpatialForecastLogs_nonneg m Dmod d
    hP hD hpcap hscale hbad hpres hE hPτ hPK hPF
  have hperiod : q.V + a * q.O ≤ q.period :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right ha hq.O)
  have hnative : q.period ≤ q.native := by
    change q.period ≤ q.period + q.factor + q.coord + q.cut + 1
    linarith [hq.factor, hq.coord, hq.cut]
  exact hperiod.trans hnative

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem actualFixedSpatialForecastLogs_cap_accuracy_independent
    (m Dmod d : ℕ) (P D pcap Pscale Pbad Ppres E E' Pτ PK PF : ℝ) :
    (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres
      E Pτ PK PF).cap =
    (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres
      E' Pτ PK PF).cap := rfl

theorem actualForecastModelPrecision
    (m Dmod d : ℕ) (P D pcap Pscale Pbad Ppres Pτ PK PF Pκ localCap : ℝ) :
    let p := max 0 (max localCap
      (Pκ + (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres
        0 Pτ PK PF).cap))
    0 ≤ p ∧ localCap ≤ p ∧
      ∀ {u : ℝ}, 0 ≤ u →
        let E := 2 * u + 4 * p + 12
        0 ≤ E ∧
        Real.exp (Pκ + (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale
          Pbad Ppres E Pτ PK PF).cap) ≤ Real.exp p ∧
        0 ≤ u + 2 * p + 1 := by
  intro p
  have hp : 0 ≤ p := le_max_left _ _
  have hlocal : localCap ≤ p := (le_max_left _ _).trans (le_max_right _ _)
  have hcap : Pκ + (actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale
      Pbad Ppres 0 Pτ PK PF).cap ≤ p :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hp, hlocal, ?_⟩
  intro u hu E
  refine ⟨by dsimp only [E]; positivity, ?_, by positivity⟩
  exact Real.exp_le_exp.mpr hcap

end Erdos3.VectorPolynomial

end

end OAI
