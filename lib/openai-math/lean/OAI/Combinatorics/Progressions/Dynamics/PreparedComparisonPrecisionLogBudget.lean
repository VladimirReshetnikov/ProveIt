import OAI.Combinatorics.Progressions.Polynomial.ForecastComparisonFloorPolynomialBudget
import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteComparisonGridBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem modularRankChargeFactor_le_preparedComparisonPower (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    (modularRankChargeFactor m : ℝ) ≤ (t + 10) ^ (2 * m + 3) := by
  have hbase : 1 ≤ t + 10 := by linarith
  have hbase0 : 0 ≤ t + 10 := by linarith
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_base : (m : ℝ) ≤ t + 10 := by linarith
  have hfour : (4 : ℝ) ≤ t + 10 := by linarith
  have htwo : (2 : ℝ) ≤ t + 10 := by linarith
  have hfactorial : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hfactorial_base : (m.factorial : ℝ) ≤ (t + 10) ^ m :=
    hfactorial.trans (pow_le_pow_left₀ hm0 hm_base m)
  have htwo_pow : (2 : ℝ) ^ m ≤ (t + 10) ^ m :=
    pow_le_pow_left₀ (by norm_num) htwo m
  calc
    (modularRankChargeFactor m : ℝ) =
        4 * (m : ℝ) * ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
      simp only [modularRankChargeFactor, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    _ ≤ (t + 10) * (t + 10) * ((t + 10) ^ m * (t + 10) ^ m) := by
      gcongr
    _ = (t + 10) ^ (2 * m + 2) := by
      rw [two_mul, pow_add, pow_add, pow_two]
      ring
    _ ≤ (t + 10) ^ (2 * m + 3) :=
      pow_le_pow_right₀ hbase (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedComparisonSourcePolynomial_le_square {t : ℝ} (ht : 1 ≤ t) :
    preparedComparisonSourcePolynomial t ≤ (t + 10) ^ 2 := by
  unfold preparedComparisonSourcePolynomial
  nlinarith

private theorem preparedComparisonSmoothPolynomial_le_six {t : ℝ} (ht : 1 ≤ t) :
    (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 ≤ (t + 10) ^ 6 := by
  have hcoef : 10 * t + 30 ≤ (t + 10) ^ 2 := by nlinarith [sq_nonneg t]
  have hinner : t + (t + 1) * (t + 1) + 1 ≤ (t + 10) ^ 2 := by nlinarith
  have hinner0 : 0 ≤ t + (t + 1) * (t + 1) + 1 := by positivity
  calc
    _ ≤ (t + 10) ^ 2 * ((t + 10) ^ 2) ^ 2 :=
      mul_le_mul hcoef (pow_le_pow_left₀ hinner0 hinner 2) (sq_nonneg _) (sq_nonneg _)
    _ = (t + 10) ^ 6 := by ring

theorem preparedComparisonGridPolynomial_le_power (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    preparedComparisonGridPolynomial m t ≤ (t + 10) ^ (2 * m + 7) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha3 : 3 ≤ a := by dsimp [a]; linarith
  have hsource : preparedComparisonSourcePolynomial t ≤ a ^ (2 * m + 6) :=
    (preparedComparisonSourcePolynomial_le_square ht).trans (pow_le_pow_right₀ ha (by omega))
  have hsmooth : (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 ≤
      a ^ (2 * m + 6) :=
    (preparedComparisonSmoothPolynomial_le_six ht).trans (pow_le_pow_right₀ ha (by omega))
  have hprefix : (2 * t) * (t + 2) ≤ a ^ 3 := by
    have hleft : 2 * t ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
    have hright : t + 2 ≤ a := by dsimp [a]; linarith
    calc
      _ ≤ a ^ 2 * a := mul_le_mul hleft hright (by positivity) (sq_nonneg _)
      _ = a ^ 3 := by ring
  have hfactor : (modularRankChargeFactor m : ℝ) ≤ a ^ (2 * m + 3) :=
    modularRankChargeFactor_le_preparedComparisonPower m ht hm
  have hmodular : (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) ≤
      a ^ (2 * m + 6) := by
    calc
      _ ≤ a ^ 3 * a ^ (2 * m + 3) :=
        mul_le_mul hprefix hfactor (Nat.cast_nonneg _) (pow_nonneg ha0 _)
      _ = a ^ (2 * m + 6) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ 3 * a ^ (2 * m + 6) := by
      unfold preparedComparisonGridPolynomial
      linarith only [hsource, hsmooth, hmodular]
    _ ≤ a * a ^ (2 * m + 6) := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
    _ = a ^ (2 * m + 7) := by rw [← pow_succ']

private theorem forecastComparisonMeshPolynomial_le_power {t grid : ℝ} {e : ℕ}
    (ht : 1 ≤ t) (he : 2 ≤ e) (hgrid0 : 0 ≤ grid)
    (hgrid : grid ≤ (t + 10) ^ e) :
    forecastComparisonMeshPolynomial t grid ≤ (t + 10) ^ (e + 3) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha3 : 3 ≤ a := by dsimp [a]; linarith
  have haE : a ≤ a ^ e := by simpa only [pow_one] using pow_le_pow_right₀ ha (by omega : 1 ≤ e)
  have ha2E : a ^ 2 ≤ a ^ e := pow_le_pow_right₀ ha he
  have hcoef : 2 * t + 1 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hinside : grid + t + 9 ≤ 2 * a ^ e := by
    have : t + 9 ≤ a := by dsimp [a]; linarith
    linarith only [hgrid, this, haE]
  have hleading : (2 * t + 1) * (grid + t + 9) ≤ 2 * a ^ (e + 2) := by
    calc
      _ ≤ a ^ 2 * (2 * a ^ e) :=
        mul_le_mul hcoef hinside (by linarith) (sq_nonneg _)
      _ = 2 * a ^ (e + 2) := by rw [pow_add]; ring
  have hlow : 13 * t + 12 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hrest : 12 * t + 2 * grid + t + 12 ≤ 3 * a ^ e := by
    linarith only [hlow, hgrid, ha2E]
  have hrest' : 12 * t + 2 * grid + t + 12 ≤ a ^ (e + 1) := by
    calc
      _ ≤ 3 * a ^ e := hrest
      _ ≤ a * a ^ e := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
      _ = a ^ (e + 1) := by rw [pow_succ']
  have hpow : a ^ (e + 1) ≤ a ^ (e + 2) := pow_le_pow_right₀ ha (by omega)
  calc
    _ ≤ 3 * a ^ (e + 2) := by
      unfold forecastComparisonMeshPolynomial
      linarith only [hleading, hrest', hpow]
    _ ≤ a * a ^ (e + 2) := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
    _ = a ^ (e + 3) := by rw [← pow_succ']

theorem preparedComparisonFloorPolynomial_le_power (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    forecastComparisonFloorPolynomial t (preparedComparisonSourcePolynomial t)
      (preparedComparisonGridPolynomial m t) ≤ (t + 10) ^ (2 * m + 20) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha5 : 5 ≤ a := by dsimp [a]; linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsource : preparedComparisonSourcePolynomial t ≤ a ^ 2 :=
    preparedComparisonSourcePolynomial_le_square ht
  have hgrid : preparedComparisonGridPolynomial m t ≤ a ^ (2 * m + 7) :=
    preparedComparisonGridPolynomial_le_power m ht hm
  have hmesh : forecastComparisonMeshPolynomial t (preparedComparisonGridPolynomial m t) ≤
      a ^ (2 * m + 10) := by
    have h := forecastComparisonMeshPolynomial_le_power ht (by omega : 2 ≤ 2 * m + 7)
      (preparedComparisonGridPolynomial_nonneg m ht0) hgrid
    exact h
  have hlow : 9 * t + 44 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hpow2 : a ^ 2 ≤ a ^ (2 * m + 10) := pow_le_pow_right₀ ha (by omega)
  have hpowgrid : a ^ (2 * m + 7) ≤ a ^ (2 * m + 10) := pow_le_pow_right₀ ha (by omega)
  calc
    _ ≤ 5 * a ^ (2 * m + 10) := by
      unfold forecastComparisonFloorPolynomial
      linarith only [hsource, hgrid, hmesh, hlow, hpow2, hpowgrid]
    _ ≤ a * a ^ (2 * m + 10) := mul_le_mul_of_nonneg_right ha5 (pow_nonneg ha0 _)
    _ = a ^ (2 * m + 11) := by rw [← pow_succ']
    _ ≤ a ^ (2 * m + 20) := pow_le_pow_right₀ ha (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

def preparedComparisonPrecisionPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  forecastComparisonFloorPolynomial t (preparedComparisonSourcePolynomial t)
    (preparedComparisonGridPolynomial m t)

theorem preparedComparisonPrecisionPolynomial_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ preparedComparisonPrecisionPolynomial m t :=
  forecastComparisonFloorPolynomial_nonneg ht
    (preparedComparisonSourcePolynomial_nonneg ht)
    (preparedComparisonGridPolynomial_nonneg m ht)

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {τ cost : ℝ}

theorem preparedComparisonPrecisionFloor_bounds
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPτ : s.Pτ ≤ t) (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) :
    (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest)
      (2 * Ptest) Ecompare : ℝ) ≤ Real.exp (preparedComparisonPrecisionPolynomial m t) ∧
    forecastJointGridAmbientLog (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ ≤ preparedComparisonPrecisionPolynomial m t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hd : ((Dmod + Fintype.card (Σ j, I j) : ℕ) : ℝ) ≤ 2 * t := by
    rw [Nat.cast_add]
    linarith only [hDmod, hI]
  have hsource := slicedComparisonSourceLog_le_preparedComparisonSourcePolynomial
    s ht hD hpcap hPtest0 hPtest
  have hgrid := comparisonGridLog_le_preparedComparisonGridPolynomial
    s ht hm hDmod (s.hX.trans hP) hD hP hpcap hPbad hPpres hcost0 hcost hPtest0 hPtest
  have hsource0 : 0 ≤ s.slicedComparisonSourceLog Ptest :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (s.slicedComparisonSourceLog_bounds Ptest).1
  have hgrid0 : 0 ≤ ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
      (s.slicedComparisonSourceLog Ptest) := hsource0.trans (le_max_left _ _)
  have hsourcePoly := preparedComparisonSourcePolynomial_nonneg ht0
  have hgridPoly := preparedComparisonGridPolynomial_nonneg m ht0
  have hV : 2 * Ptest ≤ 2 * t := by linarith only [hPtest]
  have hfloorLog := allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial
    (Dmod + Fintype.card (Σ j, I j)) ht0 hd hD hsource hV hcost hE0 hE
      hgrid0 hgrid hPK hsourcePoly hgridPoly
  have hV0 : 0 ≤ 2 * Ptest := mul_nonneg (by norm_num) hPtest0
  have hfloor := ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor_le_exp s
    (Dmod + Fintype.card (Σ j, I j)) hsource0 hV0 hcost0 hE0
  refine ⟨hfloor.trans (Real.exp_le_exp.mpr hfloorLog), ?_⟩
  have hN := forecastJointGridAmbientLog_le_comparisonPolynomial
    (Dmod + Fintype.card (Σ j, I j)) ht0 hd hgrid0 hgrid hE0 hE hV hPτ
  have hfirst : 0 ≤ 5 * t + 2 * preparedComparisonSourcePolynomial t + 32 := by positivity
  exact hN.trans (le_add_of_nonneg_left hfirst)

theorem preparedComparisonPrecisionFloor_of_exp_bounds
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPτ : s.Pτ ≤ t) (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t)
    (hS : ⌈Real.exp (preparedComparisonPrecisionPolynomial m t)⌉₊ ≤ S.value)
    (N : X → ℕ)
    (hN : ∀ i, Real.exp (preparedComparisonPrecisionPolynomial m t) ≤ (N i : ℝ)) :
    ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest)
      (2 * Ptest) Ecompare ≤ S.value ∧
    ∀ i, Real.exp (forecastJointGridAmbientLog (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ) := by
  obtain ⟨hfloor, hgrid⟩ := preparedComparisonPrecisionFloor_bounds s ht hm hDmod hI
    hD hP hpcap hPbad hPpres hPτ hPK hcost0 hcost hPtest0 hPtest hE0 hE
  constructor
  · exact_mod_cast hfloor.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hS))
  · exact fun i => (Real.exp_le_exp.mpr hgrid).trans (hN i)

theorem preparedComparisonPrecisionFloor_power_bounds
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPτ : s.Pτ ≤ t) (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) :
    (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest)
      (2 * Ptest) Ecompare : ℝ) ≤ Real.exp (((t + 10) ^ (2 * m + 20))) ∧
    forecastJointGridAmbientLog (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ ≤ ((t + 10) ^ (2 * m + 20)) := by
  obtain ⟨hfloor, hgrid⟩ := preparedComparisonPrecisionFloor_bounds s ht hm hDmod hI
    hD hP hpcap hPbad hPpres hPτ hPK hcost0 hcost hPtest0 hPtest hE0 hE
  have hpower := preparedComparisonFloorPolynomial_le_power m ht hm
  exact ⟨hfloor.trans (Real.exp_le_exp.mpr hpower), hgrid.trans hpower⟩

theorem preparedComparisonPrecisionFloor_of_power_bounds
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPτ : s.Pτ ≤ t) (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t)
    (hS : ⌈Real.exp (((t + 10) ^ (2 * m + 20)))⌉₊ ≤ S.value)
    (N : X → ℕ)
    (hN : ∀ i, Real.exp (((t + 10) ^ (2 * m + 20))) ≤ (N i : ℝ)) :
    ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest)
      (2 * Ptest) Ecompare ≤ S.value ∧
    ∀ i, Real.exp (forecastJointGridAmbientLog (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ) := by
  obtain ⟨hfloor, hgrid⟩ := preparedComparisonPrecisionFloor_power_bounds s ht hm hDmod hI
    hD hP hpcap hPbad hPpres hPτ hPK hcost0 hcost hPtest0 hPtest hE0 hE
  constructor
  · exact_mod_cast hfloor.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hS))
  · exact fun i => (Real.exp_le_exp.mpr hgrid).trans (hN i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastComparisonFloorLog_le_power
    (m M nX Jalloc d : ℕ)
    {t Pdim cost pRadius gainLog Qstride Ptest Ecompare : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) (hRadius : pRadius ≤ t) :
    preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
      Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare ≤
      (t + 10) ^ (2 * m + 20) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsource := preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    m M Jalloc ht hD hpcap hPtest0 hPtest
  have hgrid := preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    m M nX Jalloc ht hm hDmod hD hP hpcap hPbad hcost0 hcostOne hPtest0 hPtest
  have hgrid0 := preparedSlicedForecastGridLog_nonneg m M nX Jalloc
    Pdim cost gainLog Qstride Ptest
  have hV : 2 * Ptest ≤ 2 * t := mul_le_mul_of_nonneg_left hPtest (by norm_num)
  have hcost : cost ≤ t := by linarith only [hcostOne]
  have hfloor := allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial
    d ht0 hd hD hsource hV hcost hE0 hE hgrid0 hgrid hRadius
    (preparedComparisonSourcePolynomial_nonneg ht0)
    (preparedComparisonGridPolynomial_nonneg m ht0)
  exact hfloor.trans (preparedComparisonFloorPolynomial_le_power m ht hm)

theorem preparedSlicedForecastJointGridAmbientLog_le_power
    (m M nX Jalloc d : ℕ)
    {t Pdim cost gainLog Qstride Ptest Ecompare : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t)
    (hTau : gainLog + (nX : ℝ) + 8 ≤ t) :
    forecastJointGridAmbientLog d
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + (nX : ℝ) + 8) ≤
      (t + 10) ^ (2 * m + 20) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hgrid := preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    m M nX Jalloc ht hm hDmod hD hP hpcap hPbad hcost0 hcostOne hPtest0 hPtest
  have hgrid0 := preparedSlicedForecastGridLog_nonneg m M nX Jalloc
    Pdim cost gainLog Qstride Ptest
  have hV : 2 * Ptest ≤ 2 * t := mul_le_mul_of_nonneg_left hPtest (by norm_num)
  have hN := forecastJointGridAmbientLog_le_comparisonPolynomial d ht0 hd
    hgrid0 hgrid hE0 hE hV hTau
  have hsource0 := preparedComparisonSourcePolynomial_nonneg ht0
  have hfirst : 0 ≤ 5 * t + 2 * preparedComparisonSourcePolynomial t + 32 := by positivity
  exact (hN.trans (le_add_of_nonneg_left hfirst)).trans
    (preparedComparisonFloorPolynomial_le_power m ht hm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {τ cost : ℝ}

theorem preparedComparisonPrecisionLog_le_polynomial
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) :
    allocatedFixedPathSlicedAmbientFloorLog (Dmod + Fintype.card (Σ j, I j))
      s.D (s.slicedComparisonSourceLog Ptest) (2 * Ptest) cost Ecompare
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      s.PK ≤ preparedComparisonPrecisionPolynomial m t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hd : ((Dmod + Fintype.card (Σ j, I j) : ℕ) : ℝ) ≤ 2 * t := by
    rw [Nat.cast_add]
    linarith only [hDmod, hI]
  have hsource := slicedComparisonSourceLog_le_preparedComparisonSourcePolynomial
    s ht hD hpcap hPtest0 hPtest
  have hgrid := comparisonGridLog_le_preparedComparisonGridPolynomial
    s ht hm hDmod (s.hX.trans hP) hD hP hpcap hPbad hPpres hcost0 hcost hPtest0 hPtest
  have hsource0 : 0 ≤ s.slicedComparisonSourceLog Ptest :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (s.slicedComparisonSourceLog_bounds Ptest).1
  have hgrid0 : 0 ≤ ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
      (s.slicedComparisonSourceLog Ptest) := hsource0.trans (le_max_left _ _)
  have hsourcePoly := preparedComparisonSourcePolynomial_nonneg ht0
  have hgridPoly := preparedComparisonGridPolynomial_nonneg m ht0
  have hV : 2 * Ptest ≤ 2 * t := by linarith only [hPtest]
  have hfloorLog := allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial
    (Dmod + Fintype.card (Σ j, I j)) ht0 hd hD hsource hV hcost hE0 hE
      hgrid0 hgrid hPK hsourcePoly hgridPoly
  exact hfloorLog

theorem preparedComparisonPrecisionLog_le_power
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest Ecompare : ℝ} (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hI : (Fintype.card (Σ j, I j) : ℝ) ≤ t)
    (hD : s.D ≤ t) (hP : s.P ≤ t) (hpcap : s.pcap ≤ t)
    (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hPK : s.PK ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) :
    allocatedFixedPathSlicedAmbientFloorLog (Dmod + Fintype.card (Σ j, I j))
      s.D (s.slicedComparisonSourceLog Ptest) (2 * Ptest) cost Ecompare
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      s.PK ≤ (t + 10) ^ (2 * m + 20) := by
  exact (preparedComparisonPrecisionLog_le_polynomial s ht hm hDmod hI
    hD hP hpcap hPbad hPpres hPK hcost0 hcost hPtest0 hPtest hE0 hE).trans
      (preparedComparisonFloorPolynomial_le_power m ht hm)

end Erdos3.VectorPolynomial

end

end OAI
