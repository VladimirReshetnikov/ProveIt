import OAI.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource

namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_forecast_sliced_early_approximation_budget (m Dmod d : ℕ)
    {D ptail psite v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D) (htail : 0 ≤ ptail) (hsite : 0 ≤ psite)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hchild : 0 ≤ vchild)
    (hsm : 0 ≤ Psm) (hlip : 0 ≤ Plip) (hbad : 0 ≤ Pbad)
    (hpres : 0 ≤ Ppres) (hE : 0 ≤ E) (hspatial : 0 ≤ Pspatial)
    (hcoord : 0 ≤ Pcoord) (hcut : 0 ≤ Pcut) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pin ∧ 0 ≤ V ∧ 0 ≤ Esite ∧ 0 ≤ pAll ∧ 0 ≤ Q ∧ 0 ≤ O ∧ 0 ≤ Pnative ∧
    (∀ a : ℕ, (a : ℝ) ≤ D → (Real.exp tailLog) ^ a ≤ Real.exp Pin) ∧
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
      Real.exp Pcoord ≤ Real.exp Pnative ∧ Real.exp Pcut ≤ Real.exp Pnative ∧
      (∀ H I C : ℝ, 0 ≤ H → 0 ≤ C → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        C ≤ Real.exp Pdec →
        H * (I * (C / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) := by
  intro pTailAll tailLog Pin Pdec V Esite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have htailAll : 0 ≤ pTailAll := add_nonneg htail
    (VectorPolynomial.slicedFixedZeroGeometryLog_nonneg hD hv hw (le_refl 0) hchild)
  have htailLog : 0 ≤ tailLog := VectorPolynomial.slicedFixedUniformSiteLog_nonneg m htailAll (le_refl 0)
  have hPin : 0 ≤ Pin := mul_nonneg hD htailLog
  have hPdec : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hEs : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hpAll : 0 ≤ pAll := add_nonneg hsite
    (VectorPolynomial.slicedFixedZeroGeometryLog_nonneg hD hv hw hV hchild)
  have hcap : 0 ≤ VectorPolynomial.slicedFixedUniformSiteLog m pAll 0 :=
    VectorPolynomial.slicedFixedUniformSiteLog_nonneg m hpAll (le_refl 0)
  have hprod : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD hcap hEs) zero_le_one
  have hQ : 0 ≤ Q := VectorPolynomial.slicedFixedUniformSiteLog_nonneg m hpAll hprod
  have hO : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ
  have hperiod : 0 ≤ Pperiod := add_nonneg hV (mul_nonneg hD hO)
  have hfactor : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hn : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  obtain ⟨T, δ, hT, hTv, hδ, hδ1, hδb, heRaw⟩ :=
    exists_forecast_weighted_approximation_parameters d hsm hPin hPdec hE
  have he := fun (Rbad Qpres : ℕ) (H I : ℝ) (hH : 0 ≤ H)
      (hHb : H ≤ Real.exp Psm) (hIb : I ≤ Real.exp Pin)
      (hR : (Rbad : ℝ) ≤ Real.exp Pbad) (hQp : (Qpres : ℝ) ≤ Real.exp Ppres) =>
    heRaw H I _ hH (Real.rpow_nonneg (Nat.cast_nonneg _) _) hHb hIb
      (forecastModularCharge_exp_bound m Dmod Rbad Qpres hR hQp)
  refine ⟨hPin, hV, hEs, hpAll, hQ, hO, hn, ?_, T, δ, hT, hTv, hδ, hδ1, hδb, he, ?_, ?_, ?_, ?_, ?_, heRaw⟩
  · intro a ha
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha htailLog)
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

theorem exists_forecast_sliced_early_native_family_budget
    {X : Type*} [Fintype X]
    (m Dmod d : ℕ) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (localBudget : ℝ)
    {D ptail psite v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D) (htail : 0 ≤ ptail) (hsite : 0 ≤ psite)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hchild : 0 ≤ vchild)
    (hsm : 0 ≤ Psm) (hlip : 0 ≤ Plip) (hbad : 0 ≤ Pbad)
    (hpres : 0 ≤ Ppres) (hE : 0 ≤ E) (hspatial : 0 ≤ Pspatial)
    (hcoord : 0 ≤ Pcoord) (hcut : 0 ≤ Pcut) :
    let pTailAll := ptail + slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let pAll := psite + slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
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
  intro pTailAll tailLog Pin Pdec V Esite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap budget
  obtain ⟨_, _, _, _, _, _, hN, _, T, δ, hT, hTv, hδ, hδ1, hδb,
      herror, hcap, hmass, _, _, _⟩ :=
    exists_forecast_sliced_early_approximation_budget m Dmod d hD htail hsite hv hw hchild hsm hlip
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

namespace Erdos3
open scoped NNReal

theorem forecastSlicedPrimitiveEnvelope_mul_cutoff
    (L : ℝ≥0) {Ptail p V : ℝ} {T : ℕ}
    (hT : 0 < T) (hP : 1 ≤ Ptail)
    (htail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hPexp : Ptail ≤ Real.exp p) (hTexp : (T : ℝ) ≤ Real.exp V) :
    1 ≤ Ptail * T ∧
      scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ Ptail * T ∧
      Ptail * T ≤ Real.exp (p + V) ∧
      ∀ s : ℕ, (s : ℝ) ≤ Ptail → ((s * T : ℕ) : ℝ) ≤ Ptail * T := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  refine ⟨one_le_mul_of_one_le_of_one_le hP hT1, ?_, ?_, ?_⟩
  · have h := scalarCubePrimitiveEnvelope_le_scaled Empty L 1 0 (Nat.succ_le_of_lt hT)
    simpa only [Fintype.card_empty, zero_add, pow_one] using
      h.trans (mul_le_mul_of_nonneg_right htail (by positivity))
  · rw [Real.exp_add]
    exact mul_le_mul hPexp hTexp (Nat.cast_nonneg _) (Real.exp_nonneg _)
  · intro s hs
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)

end Erdos3

end

end OAI
