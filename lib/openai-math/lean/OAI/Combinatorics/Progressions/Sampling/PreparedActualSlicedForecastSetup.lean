import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedPrimitiveGeometry
import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
import OAI.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup

namespace OAI

section

namespace Erdos3

theorem modularInitialRankStrength_eq_forecast (s D : ℕ) :
    modularInitialRankStrength s D = modularForecastRankConstant s D := by
  unfold modularInitialRankStrength modularForecastRankConstant
  rw [show 2 * s = s + s by omega, pow_add]
  ring

theorem modularInitialBlockCount_forecast_threshold {s D d : ℕ}
    (hs : 0 < s) (hd : d ≤ D) :
    ⌈2 * ((modularForecastRankConstant s D : ℝ) + d + 10) /
      modularRankSmallBallExponent s⌉₊ ≤ modularInitialBlockCount s D := by
  apply (Nat.ceil_mono ?_).trans (modularInitialBlockCount_threshold hs D)
  rw [modularInitialRankStrength_eq_forecast]
  apply div_le_div_of_nonneg_right _ (modularRankSmallBallExponent_pos s).le
  have hreal : (d : ℝ) ≤ D := Nat.cast_le.mpr hd
  linarith

theorem modularInitialAllocation_forecast_parameters {s D d : ℕ}
    (hs : 0 < s) (hd : d ≤ D) :
    0 ≤ (modularForecastRankConstant s D : ℝ) ∧
      ⌈2 * ((modularForecastRankConstant s D : ℝ) + d + 10) /
        modularRankSmallBallExponent s⌉₊ ≤ modularInitialBlockCount s D ∧
      ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) :=
  ⟨Nat.cast_nonneg _, modularInitialBlockCount_forecast_threshold hs hd,
    modularForecastRankConstant_dimension s D d hd⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

noncomputable def actualSlicedForecastDensityBudget (v : ℝ) : ℝ :=
  Real.exp (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * v))

noncomputable def actualSlicedForecastDecayBudget : ℝ :=
  Real.exp ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m)

structure ActualFixedSpatialSlicedForecastNumerics where
  T : ℕ
  hT : 0 < T
  δ : ℝ
  hδ : 0 < δ
  Hchild : ℕ
  v : ℝ
  hv : 0 ≤ v
  Ptail : ℝ
  Ctail : ℝ
  hPtail : 1 ≤ Ptail
  hprimitive : s.Pcap ≤ Ptail
  hCtail : 0 ≤ Ctail
  Cactual : ℝ
  δout : ℝ
  Q : ℝ
  Nt : ℝ
  Vt : ℝ
  Ct : ℝ
  Ht : ℝ
  Lt : ℝ≥0
  hCactual : 0 ≤ Cactual
  hδout : 0 < δout
  hQ : 0 ≤ Q
  hCt : 0 ≤ Ct
  hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
    forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
      δ (Ptail * T) Cactual δout Q Nt Vt Ct Ht Lt
  htailactual : ∀ a,
    let degree := (selected a).1.val + 1
    let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := blockTorusFactor (Fintype.card Empty) degree
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
    let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    max (cutoff : ℝ)
      (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail
  Pnative : ℝ
  massLog : ℝ
  capLog : ℝ
  E : ℝ
  hPnative : 0 ≤ Pnative
  hperiod : (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative
  hfactor : (actualSlicedForecastDensityBudget s v + Fintype.card A * (Lt : ℝ)) *
    max (8 / τ) 1 ≤ Real.exp Pnative
  hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
    (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hmass : s.κ * (2 * actualSlicedForecastDensityBudget s v *
    ((T : ℝ) ^ (Dmod + 1) * Ct ^ Fintype.card A)) ≤ Real.exp massLog
  herror : s.κ * (actualSlicedForecastDensityBudget s v *
    (Ctail ^ Fintype.card A * (actualSlicedForecastDecayBudget s / T) +
      (T : ℝ) ^ (Dmod + 1) * δout)) ≤ Real.exp (-E)
  hcap : s.κ * actualSlicedForecastDensityBudget s v * Ctail ^ Fintype.card A *
    (1 + actualSlicedForecastDecayBudget s) ≤ Real.exp capLog

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem exists_actualFixedSpatialSlicedForecastNumerics
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail D p v w vchild E Pspatial Pcoord Pcut : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hD : 1 ≤ D) (hp : 0 ≤ p)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvc : 0 ≤ vchild) (hE : 0 ≤ E)
    (hsp : 0 ≤ Pspatial) (hco : 0 ≤ Pcoord) (hcu : 0 ≤ Pcut)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v)
    (hspatial : max (8 / τ) 1 ≤ Real.exp Pspatial)
    (hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pcoord)
    (hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pcut) :
    let Psm := forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * kernelV)
    let tailLog := slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
    let Pin := D * tailLog
    let Pdec := (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + s.Pκ + Psm) + 3
    let Esite := E + s.Pκ + Psm + 1 + ((Dmod + 1 : ℕ) : ℝ) * V
    let pAll := p + V + slicedFixedZeroGeometryLog D v w V vchild
    let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
    let O := siteExponentialOutputLog 1 Q
    let Pnative := (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1
    let Pmass := Psm + ((Dmod + 1 : ℕ) : ℝ) * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    ∃ nu : ActualFixedSpatialSlicedForecastNumerics s,
      nu.δ = δ ∧ nu.Hchild = Hchild ∧ nu.v = kernelV ∧ nu.Ptail = Ptail ∧ nu.E = E ∧
      nu.Pnative = Pnative ∧ nu.massLog = s.Pκ + Pmass ∧ nu.capLog = s.Pκ + Pcap ∧
      nu.Ctail = Real.exp tailLog ∧ (nu.T : ℝ) ≤ Real.exp V ∧
      0 ≤ nu.massLog ∧ 0 ≤ nu.capLog := by
  let _ : DecidableEq X := inferInstance
  intro Psm tailLog Pin Pdec V Esite pAll Q O Pnative Pmass Pcap
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hPs : 0 ≤ s.P := zero_le_one.trans s.hP
  have hBad := s.hPbad
  have hPres := s.hPpres
  have hsm : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m (by positivity)).1
  have hEtotal : 0 ≤ E + s.Pκ := add_nonneg hE s.hPκ
  have htailLog : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m
    (add_nonneg hp (slicedFixedZeroGeometryLog_nonneg hD0 hv hw (le_refl 0) hvc)) (le_refl 0)
  have hPin : 0 ≤ Pin := mul_nonneg hD0 htailLog
  have hPdec : 0 ≤ Pdec := by dsimp [Pdec]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨_, _, hEs, hpAll, hQ, hO, hN, htailBound, T, δout, hT, hTv,
      hδout, hδout1, hδoutE, _, hcapBound, hmassBound, hfactorBound, hcoordBound,
      hcutBound, herrorBound⟩ :=
    exists_forecast_sliced_early_approximation_budget m Dmod (Dmod + 1)
      hD0 hp (add_nonneg hp hV) hv hw hvc hsm hsm s.hPbad s.hPpres hEtotal hsp hco hcu
  have hPsite := forecastSlicedPrimitiveEnvelope_mul_cutoff s.L hT hPtail
    (s.hprimitiveCap.trans hprimitive) hPp hTv
  have hnum := forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    B selected T Hchild δ (Ptail * T) δout D (p + V) Esite v w V vchild
    hδ hPsite.1 hδout hD (add_nonneg hp hV) hEs hv hw hV hvc hcard hPsite.2.2.1
    hδoutE hδw hTv hchild hR hdegree htail hb hRv hRi hcoeff
  have htailActual := forecastInactiveSlicedTailCap_of_primitive_uniform_budgets
    B selected Hchild δ Ptail D p v w vchild hδ hPtail hD hp hv hw hvc hcard hPp
    hδw hchild hR hdegree htail hb hRv hRi hcoeff
  have hI : (Real.exp tailLog) ^ Fintype.card A ≤ Real.exp Pin := htailBound _ hcard
  have hperiod : (T : ℝ) * (Real.exp O) ^ Fintype.card A ≤ Real.exp Pnative := by
    have hao : (Fintype.card A : ℝ) * O ≤ D * O := mul_le_mul_of_nonneg_right hcard hO
    calc
      _ ≤ Real.exp V * (Real.exp O) ^ Fintype.card A :=
        mul_le_mul_of_nonneg_right hTv (by positivity)
      _ = Real.exp (V + (Fintype.card A : ℝ) * O) := by
        rw [← Real.exp_nat_mul]
        exact (Real.exp_add V _).symm
      _ ≤ Real.exp Pnative := Real.exp_le_exp.mpr (by dsimp [Pnative]; linarith)
  let Hbudget : ℝ := actualSlicedForecastDensityBudget s kernelV
  have hHb : Hbudget = Real.exp Psm := rfl
  have hH : 0 ≤ Hbudget := by rw [hHb]; positivity
  let Lsp : ℝ≥0 := ⟨max (8 / τ) 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hfac := (hfactorBound (Fintype.card A) 0 ⟨Hbudget, hH⟩ Lsp hcard
    (by simpa only [Nat.cast_zero] using Real.exp_nonneg _) (le_of_eq hHb) hspatial).2
  change (Hbudget + (Fintype.card A : ℝ) * Real.exp O) * max (8 / τ) 1 ≤ Real.exp Pnative at hfac
  have hm := hmassBound (Fintype.card A) Hbudget hcard hH (le_of_eq hHb)
  have he := herrorBound Hbudget ((Real.exp tailLog) ^ Fintype.card A) (Real.exp Pdec)
    hH (Real.exp_nonneg _) (le_of_eq hHb) hI le_rfl
  have hc := hcapBound Hbudget (Real.exp Pdec) hH (le_of_eq hHb) (Real.exp_nonneg _) le_rfl
  let nu : ActualFixedSpatialSlicedForecastNumerics s := {
    T := T, hT := hT, δ := δ, hδ := hδ, Hchild := Hchild, v := kernelV, hv := hk,
    Ptail := Ptail, Ctail := Real.exp tailLog, hPtail := hPtail, hprimitive := hprimitive,
    hCtail := Real.exp_nonneg _, Cactual := Real.exp (slicedFixedUniformSiteLog m pAll 0),
    δout := δout, Q := Q, Nt := Real.exp O, Vt := Real.exp O, Ct := Real.exp O,
    Ht := Real.exp pAll, Lt := ⟨Real.exp O, Real.exp_nonneg _⟩,
    hCactual := Real.exp_nonneg _, hδout := hδout, hQ := hQ, hCt := Real.exp_nonneg _,
    hnumerics := hnum.2.2, htailactual := htailActual,
    Pnative := Pnative, massLog := s.Pκ + Pmass, capLog := s.Pκ + Pcap, E := E,
    hPnative := hN, hperiod := hperiod,
    hfactor := hfac,
    hcoord := hcoord.trans hcoordBound, hcut := hcut.trans hcutBound,
    hmass := by
      have hm' : 2 * Hbudget * ((T : ℝ) ^ (Dmod + 1) * (Real.exp O) ^ Fintype.card A) ≤ Real.exp Pmass := by
        simpa only [Real.exp_nat_mul] using hm
      calc
        _ ≤ Real.exp s.Pκ * Real.exp Pmass :=
          mul_le_mul s.hκcap hm' (by positivity) (Real.exp_nonneg _)
        _ = _ := (Real.exp_add _ _).symm,
    herror := by
      change s.κ * (Hbudget * ((Real.exp tailLog) ^ Fintype.card A * (Real.exp Pdec / T) +
        (T : ℝ) ^ (Dmod + 1) * δout)) ≤ Real.exp (-E)
      calc
        _ ≤ Real.exp s.Pκ * Real.exp (-(E + s.Pκ)) :=
          mul_le_mul s.hκcap he (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring,
    hcap := by
      change s.κ * Hbudget * (Real.exp tailLog) ^ Fintype.card A * (1 + Real.exp Pdec) ≤ _
      have hi := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI hH) (by positivity : 0 ≤ 1 + Real.exp Pdec)
      calc
        _ = s.κ * (Hbudget * (Real.exp tailLog) ^ Fintype.card A * (1 + Real.exp Pdec)) := by ring
        _ ≤ Real.exp s.Pκ * Real.exp Pcap :=
          mul_le_mul s.hκcap (hi.trans hc) (by positivity) (Real.exp_nonneg _)
        _ = _ := (Real.exp_add _ _).symm }
  refine ⟨nu, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hTv, ?_, ?_⟩
  · change 0 ≤ s.Pκ + Pmass
    have hκ := s.hPκ
    dsimp only [Pmass]
    positivity
  · change 0 ≤ s.Pκ + Pcap
    have hκ := s.hPκ
    dsimp only [Pcap]
    positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem exists_actualFixedSpatialSlicedForecastNumerics_from_setup
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail p w vchild E : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hvc : 0 ≤ vchild) (hE : 0 ≤ E)
    (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ j, 0 < R j) :
    let D := s.slicedGeometryDimension
    let v := s.slicedGeometryRadiusLog
    let Pspatial := s.Pτ + 8
    let Pcoord := s.PK + s.PF + s.D
    let Pcut := s.PK + s.PF + 2 * s.D + normalizedSiteCutoffBound + 1
    let Psm := forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * kernelV)
    let tailLog := slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
    let Pin := D * tailLog
    let Pdec := (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + s.Pκ + Psm) + 3
    let Esite := E + s.Pκ + Psm + 1 + ((Dmod + 1 : ℕ) : ℝ) * V
    let pAll := p + V + slicedFixedZeroGeometryLog D v w V vchild
    let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
    let O := siteExponentialOutputLog 1 Q
    let Pnative := (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1
    let Pmass := Psm + ((Dmod + 1 : ℕ) : ℝ) * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    ∃ nu : ActualFixedSpatialSlicedForecastNumerics s,
      nu.δ = δ ∧ nu.Hchild = Hchild ∧ nu.v = kernelV ∧ nu.Ptail = Ptail ∧ nu.E = E ∧
      nu.Pnative = Pnative ∧ nu.massLog = s.Pκ + Pmass ∧ nu.capLog = s.Pκ + Pcap ∧
      nu.Ctail = Real.exp tailLog ∧ (nu.T : ℝ) ≤ Real.exp V ∧
      0 ≤ nu.massLog ∧ 0 ≤ nu.capLog := by
  intro D v Pspatial Pcoord Pcut
  obtain ⟨hD, hcard, hdegree, htail, hblocks, hv, hRselected, hRv, hRi, hcoeff⟩ :=
    ActualFixedSpatialForecastSetup.sliced_primitive_geometry_bounds
      (B := B) (U := U) (b := b) (S := S) (X := X) (Eout := Eout) s hR
  have hPK := s.hPK
  have hPF := s.hPF
  have hD0 := s.hD.nonneg
  have hPτ := s.hPτ
  have hsp : 0 ≤ Pspatial := by dsimp [Pspatial]; positivity
  have hco : 0 ≤ Pcoord := by dsimp [Pcoord]; positivity
  have hcu : 0 ≤ Pcut := by dsimp [Pcut]; positivity
  have hspatial : max (8 / τ) 1 ≤ Real.exp Pspatial := by
    exact_mod_cast s.sliced_spatial_coordinate_bound
  obtain ⟨hcoord, hcut⟩ := s.sliced_ambient_coordinate_cutoff_bounds
  exact exists_actualFixedSpatialSlicedForecastNumerics s δ Hchild kernelV Ptail D p v w vchild E
    Pspatial Pcoord Pcut hδ hk hPtail hprimitive hD hp hv hw hvc hE hsp hco hcu
    hcard hPp hδw hchild hRselected hdegree htail hblocks hRv hRi hcoeff hspatial hcoord hcut

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

noncomputable def actualSlicedForecastModelCapLog (m Dmod cardX : ℕ)
    (P Pscale Pbad Ppres Pκ kernelV p w vchild : ℝ) : ℝ :=
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let tailLog := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  Pκ + (Psm + D * tailLog + Pdec + 1)

noncomputable def actualSlicedForecastModelPeriodLog (m Dmod cardX : ℕ)
    (P Pscale Pbad Ppres Pκ kernelV p w vchild E : ℝ) : ℝ :=
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let tailLog := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  D * tailLog + Pdec + (E + Pκ + Psm) + 3

theorem actualSlicedForecastModelPrecision
    {m : ℕ} {G : Type} [Fintype G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {X : Type} [Fintype X] [DecidableEq X]
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    {A : Type} [Fintype A]
    {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
    {τ δslice : ℝ}
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail p w vchild localCap : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hvc : 0 ≤ vchild) (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ j, 0 < R j) :
    let capLog := actualSlicedForecastModelCapLog m Dmod (Fintype.card X)
      s.P s.Pscale s.Pbad s.Ppres s.Pκ kernelV p w vchild
    let pForecast := max 0 (max localCap capLog)
    0 ≤ pForecast ∧ localCap ≤ pForecast ∧
      ∀ {u : ℝ}, 0 ≤ u →
        let E := 2 * u + 4 * pForecast + 12
        0 ≤ E ∧ 0 ≤ u + 2 * pForecast + 1 ∧
        ∃ q : ActualFixedSpatialSlicedForecastNumerics s,
          q.δ = δ ∧ q.Hchild = Hchild ∧ q.v = kernelV ∧ q.Ptail = Ptail ∧
          q.E = E ∧ q.capLog = capLog ∧ q.capLog ≤ pForecast ∧
          0 ≤ q.massLog ∧ 0 ≤ q.capLog ∧
          Real.exp q.capLog ≤ Real.exp pForecast ∧
          (q.T : ℝ) ≤ Real.exp (actualSlicedForecastModelPeriodLog
            m Dmod (Fintype.card X) s.P s.Pscale s.Pbad s.Ppres s.Pκ
            kernelV p w vchild E) := by
  intro capLog pForecast
  have hpf : 0 ≤ pForecast := le_max_left _ _
  have hlocal : localCap ≤ pForecast := (le_max_left _ _).trans (le_max_right _ _)
  have hcap : capLog ≤ pForecast := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hpf, hlocal, ?_⟩
  intro u hu E
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨hE, by positivity, ?_⟩
  obtain ⟨q, hqδ, hqH, hqv, hqP, hqE, _, _, hqcap, _, hqT, hqmass, hqcap0⟩ :=
    exists_actualFixedSpatialSlicedForecastNumerics_from_setup s δ Hchild kernelV Ptail
      p w vchild E hδ hk hPtail hprimitive hp hw hvc hE hPp hδw hchild hR
  have hqcap' : q.capLog = capLog := hqcap
  have hqbound : q.capLog ≤ pForecast := hqcap'.le.trans hcap
  exact ⟨q, hqδ, hqH, hqv, hqP, hqE, hqcap', hqbound, hqmass, hqcap0,
    Real.exp_le_exp.mpr hqbound, hqT⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_actualSlicedForecastModelCapLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Dmod cardX : ℕ)
      {r P Pscale Pbad Ppres Pκ kernelV p w vchild : ℝ},
      0 ≤ r → (Dmod : ℝ) ≤ r → (cardX : ℝ) ≤ r →
      P ∈ Set.Icc 0 r → Pscale ∈ Set.Icc 0 r → Pbad ∈ Set.Icc 0 r →
      Ppres ∈ Set.Icc 0 r → Pκ ∈ Set.Icc 0 r → kernelV ∈ Set.Icc 0 r →
      p ∈ Set.Icc 0 r → w ∈ Set.Icc 0 r → vchild ∈ Set.Icc 0 r →
      actualSlicedForecastModelCapLog m Dmod cardX
        P Pscale Pbad Ppres Pκ kernelV p w vchild ∈ Set.Icc 0 ((r + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let Dpoly := X + Polynomial.C (layerTailDegree m + 1) + 1
  let Spoly := Polynomial.C (10 * m + 30) * (X + (X + 1) * X + 1) ^ 2
  let Tpoly := slicedFixedUniformSitePolynomial m
    (X + slicedFixedZeroGeometryLog Dpoly (X + X) X 0 X) 0
  let Q := X + (Spoly + Dpoly * Tpoly +
    (X + X) * (X + 2) * Polynomial.C (modularRankChargeFactor m) + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro Dmod cardX r P Pscale Pbad Ppres Pκ kernelV p w vchild
    hr hDmod hcard hP hscale hbad hpres hκ hk hp hw hchild
  let D := P + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let Dr := r + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let Rsm := (10 * (m : ℝ) + 30) * (r + (r + 1) * r + 1) ^ 2
  let tail := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Rtail := slicedFixedUniformSiteLog m
    (r + slicedFixedZeroGeometryLog Dr (r + r) r 0 r) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  let Rdec := (r + r) * (r + 2) * modularRankChargeFactor m
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg hP.1 (Nat.cast_nonneg _)) zero_le_one
  have hDr0 : 0 ≤ Dr := by dsimp only [Dr]; positivity
  have hDD : D ≤ Dr := by dsimp only [D, Dr]; linarith only [hP.2]
  have hv0 : 0 ≤ v := add_nonneg hP.1 hscale.1
  have hv : v ≤ r + r := add_le_add hP.2 hscale.2
  have hgeom0 := slicedFixedZeroGeometryLog_nonneg hD0 hv0 hw.1 (le_refl 0) hchild.1
  have htail0 : 0 ≤ tail :=
    slicedFixedUniformSiteLog_nonneg m (add_nonneg hp.1 hgeom0) (le_refl 0)
  have htail : tail ≤ Rtail :=
    slicedFixedUniformSiteLog_mono m (add_nonneg hp.1 hgeom0) (le_refl 0)
      (add_le_add hp.2 (slicedFixedZeroGeometryLog_mono hD0 hv0 hw.1
        (le_refl 0) hchild.1 hDD hv hw.2 le_rfl hchild.2)) le_rfl
  have harg0 : 0 ≤ P + (cardX + 1) * kernelV :=
    add_nonneg hP.1 (mul_nonneg (by positivity) hk.1)
  have harg : P + (cardX + 1) * kernelV ≤ r + (r + 1) * r :=
    add_le_add hP.2 (mul_le_mul (add_le_add hcard le_rfl) hk.2 hk.1 (by linarith))
  have hsm0 : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m harg0).1
  have hsm : Psm ≤ Rsm := by
    dsimp only [Psm, Rsm, forecastOriginalSmoothBudget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [harg0]) (add_le_add harg le_rfl) 2)
      (by positivity)
  have hdec0 : 0 ≤ Pdec :=
    mul_nonneg (mul_nonneg (add_nonneg hbad.1 hpres.1) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hdec : Pdec ≤ Rdec := by
    dsimp only [Pdec, Rdec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add hDmod le_rfl)
        (by positivity) (add_nonneg hr hr)) (Nat.cast_nonneg _)
  have hdiag : r + (Rsm + Dr * Rtail + Rdec + 1) ≤ (r + C) ^ C := by
    simpa [Q, Spoly, Dpoly, Tpoly, X, Rsm, Dr, Rtail, Rdec,
      Polynomial.eval₂_pow, slicedFixedUniformSitePolynomial_eval,
      slicedFixedZeroGeometryLog_eval₂] using hbudget r hr
  change 0 ≤ Pκ + (Psm + D * tail + Pdec + 1) ∧
    Pκ + (Psm + D * tail + Pdec + 1) ≤ (r + C) ^ C
  refine ⟨by linarith only [hκ.1, hsm0, mul_nonneg hD0 htail0, hdec0], ?_⟩
  apply le_trans _ hdiag
  exact add_le_add hκ.2 (add_le_add
    (add_le_add (add_le_add hsm (mul_le_mul hDD htail htail0 hDr0)) hdec) le_rfl)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

noncomputable def preparedSlicedForecastSpatialBudget (m M nX Jalloc : ℕ)
    (Pdim cost : ℝ) : ℝ :=
  max (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8)
    (max (preparedCenteredForecastSpatialLog Pdim) (cost + 1))

noncomputable def preparedSlicedForecastBadLog (m nX : ℕ) (Qstride gainLog : ℝ) : ℝ :=
  2 * nX * Qstride + (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11

noncomputable def preparedSlicedForecastJacobianLog (m M nX : ℕ)
    (pRadius gainLog Pchart : ℝ) : ℝ :=
  ((nX + m + m * M : ℕ) : ℝ) * (pRadius + gainLog + nX + Pchart + 11)

noncomputable def preparedSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart kernelV p w vchild : ℝ) : ℝ :=
  actualSlicedForecastModelCapLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart) kernelV p w vchild

private theorem preparedSliceWidth_inverse (cost : ℝ) :
    (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  nlinarith only [mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg cost)]

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
noncomputable def preparedActualSlicedForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) (X := Fin nX) (Eout := Eout)
      («G» := (EnlargedPreparedCommonKernel m Jalloc)) («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) (A := PreparedActualForecastShortIndex («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M) (preparedActualForecastShortSelection («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let Pbad := preparedSlicedForecastBadLog m nX Qstride gainLog
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let κ := forecastGeometricJacobian (X := Fin nX) («I» := (PreparedSamplerContinuous L)) U b R S.value
    (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8)))
  have hPbad : 0 ≤ Pbad := by dsimp only [Pbad, preparedSlicedForecastBadLog]; positivity
  obtain ⟨hκ, hPκ, hκcap⟩ := preparedActualForecastJacobian_ratio_budget (nX := nX) L
    (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S
    hCoord hpRadius hGain hChart hR hRinv hratio
  let s := preparedActualForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord
    hpRadius hGain hPbad (show 0 ≤ cost + 1 by linarith) hPF hPκ hκ.le hκcap
    hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
    inverse hinverse hchart hsourceBudget
  have hsP : s.P = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8 := by
    simp only [s, preparedActualForecastSetup, and_rec_projection]
  have hP : s.P ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    rw [hsP]
    exact le_max_left _ _
  let s' := s.enlargeP hP
  have hwidth : (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp s'.P :=
    (preparedSliceWidth_inverse cost).trans (Real.exp_le_exp.mpr
      ((le_max_right _ _).trans (le_max_right _ _)))
  exact s'.withSliceWidth (div_pos (Real.exp_pos _) (by norm_num)) hwidth

end Erdos3.VectorPolynomial

end

end OAI
