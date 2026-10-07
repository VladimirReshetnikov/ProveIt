import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog

namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedComparisonSourcePolynomial (t : ℝ) : ℝ :=
  2 + t * t + 2 * t

def preparedComparisonGridPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  preparedComparisonSourcePolynomial t +
    (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 +
    (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ)

theorem preparedComparisonSourcePolynomial_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ preparedComparisonSourcePolynomial t := by
  unfold preparedComparisonSourcePolynomial
  positivity

theorem preparedComparisonGridPolynomial_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ preparedComparisonGridPolynomial m t := by
  unfold preparedComparisonGridPolynomial
  have hsource := preparedComparisonSourcePolynomial_nonneg ht
  positivity

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}

theorem slicedComparisonSourceLog_le_preparedComparisonSourcePolynomial
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    {t Ptest : ℝ} (ht : 1 ≤ t) (hD : s.D ≤ t) (hpcap : s.pcap ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    s.slicedComparisonSourceLog Ptest ≤ preparedComparisonSourcePolynomial t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsq : s.D * s.D ≤ t * t := mul_le_mul hD hD s.hD.nonneg ht0
  unfold ActualFixedSpatialForecastSetup.slicedComparisonSourceLog
    preparedComparisonSourcePolynomial
  rw [max_eq_right hPtest0]
  linarith

variable {cost : ℝ}

theorem comparisonGridLog_le_preparedComparisonGridPolynomial
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
    {t Ptest : ℝ} (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hX : (Fintype.card X : ℝ) ≤ t) (hD : s.D ≤ t) (hP : s.P ≤ t)
    (hpcap : s.pcap ≤ t) (hPbad : s.Pbad ≤ t) (hPpres : s.Ppres ≤ t)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
      (s.slicedComparisonSourceLog Ptest) ≤ preparedComparisonGridPolynomial m t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsource := slicedComparisonSourceLog_le_preparedComparisonSourcePolynomial
    s ht hD hpcap hPtest0 hPtest
  have hsource0 := preparedComparisonSourcePolynomial_nonneg ht0
  have hmul : ((Fintype.card X : ℝ) + 1) * (cost + 1) ≤ (t + 1) * (t + 1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hinner0 : 0 ≤ s.P + ((Fintype.card X : ℝ) + 1) * (cost + 1) + 1 := by
    have hP0 : 0 ≤ s.P := zero_le_one.trans s.hP
    positivity
  have hinner : s.P + ((Fintype.card X : ℝ) + 1) * (cost + 1) + 1 ≤
      t + (t + 1) * (t + 1) + 1 := by linarith
  have hsquare := pow_le_pow_left₀ hinner0 hinner 2
  have hcoef : 10 * (m : ℝ) + 30 ≤ 10 * t + 30 := by linarith
  have hsmooth : forecastOriginalSmoothBudget m
      (s.P + (Fintype.card X + 1) * (cost + 1)) ≤
      (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    unfold forecastOriginalSmoothBudget
    exact mul_le_mul hcoef hsquare (sq_nonneg _) (by positivity)
  have hsmooth0 : 0 ≤ (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    positivity
  have hprod : (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) ≤ (2 * t) * (t + 2) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hmodular : (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) *
      (modularRankChargeFactor m : ℝ) ≤
      (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) :=
    mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)
  have hmodular0 : 0 ≤ (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) := by
    positivity
  unfold ActualFixedSpatialSlicedForecastPath.comparisonGridLog
    preparedComparisonGridPolynomial
  exact max_le (by linarith only [hsource, hsmooth0, hmodular0])
    (max_le (by linarith only [hsmooth, hsource0, hmodular0])
      (by linarith only [hmodular, hsource0, hsmooth0]))

end Erdos3.VectorPolynomial

end

end OAI
