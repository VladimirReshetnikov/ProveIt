import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

def allocatedSiteSpatialMassLog {A : Type*} [Semiring A] (D w v : A) : A :=
  coefficientMajorantMassLog D + D * w + v

theorem allocatedSiteSpatialMassLog_nonneg {D w v : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    0 ≤ allocatedSiteSpatialMassLog D w v := by
  have hbase := coefficientMajorantMassLog_nonneg hD
  unfold allocatedSiteSpatialMassLog
  positivity

theorem allocatedSiteSpatialMass_exp_bound {m : ℕ} (O Q J : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] [∀ j, Fintype (J j)]
    (C : Fin m → ℝ≥0) (period M N : ℕ) (CM Cf : ℝ≥0)
    {D w v : ℝ} (hD : 0 ≤ D) (hw : 0 ≤ w) (hm : (m : ℝ) ≤ D)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ D)
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ D)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (hM : (M : ℝ) ≤ D) (hN : (N : ℝ) ≤ D)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp D)
    (hperiod : (period : ℝ) ≤ Real.exp (D ^ 2))
    (hCM : (CM : ℝ) ≤ Real.exp w) (hCf : (Cf : ℝ) ≤ Real.exp v) :
    ((Real.toNNReal (coefficientDeckPeriodCap O Q period) * CM ^ M * Cf : ℝ≥0) : ℝ) *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^ N ≤
      Real.exp (allocatedSiteSpatialMassLog D w v) := by
  have hbase := coefficientMajorantMassFactor_exp_bound O Q J C period N
    hD hm hO hQ hJ hN hC hperiod
  have hmask := pow_le_exp_mul_of_le_exp CM.coe_nonneg hCM hw M hM
  simp only [NNReal.coe_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
  calc
    _ = (coefficientDeckPeriodCap O Q period *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^ N) *
        (CM : ℝ) ^ M * Cf := by ring
    _ ≤ Real.exp (coefficientMajorantMassLog D) * Real.exp (D * w) * Real.exp v :=
      mul_le_mul (mul_le_mul hbase hmask (pow_nonneg CM.coe_nonneg M) (Real.exp_pos _).le)
        hCf Cf.coe_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (allocatedSiteSpatialMassLog D w v) := by
      rw [← Real.exp_add, ← Real.exp_add]
      rfl

theorem allocatedSiteSpatial_error_budget {H L E δ δFourier ε : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ Real.exp L)
    (hδ : δ ≤ physicalIdealErrorShare E L)
    (hδFourier : δFourier ≤ physicalIdealErrorShare E 1)
    (hε : ε ≤ physicalIdealErrorShare E 1) :
    δ * H + 2 * δFourier + ε ≤ Real.exp (-E) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : (1 / 2 : ℝ) ≤ Real.exp 0 := by norm_num
  have h := physicalIdeal_three_errors_le (a := H) (b := 2) (c := 1 / 2)
    (V := L) (W := 1) (K := 0) hH0 (by norm_num) (by norm_num) hH htwo hhalf
    hδ hδFourier (by simpa only [add_zero] using hε)
  convert h using 1
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedSitePrimitiveTolerance (m : ℕ) (p w v E : ℝ) : ℝ :=
  physicalIdealErrorShare E (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) w v)

theorem allocatedSitePrimitiveTolerance_pos (m : ℕ) (p w v E : ℝ) :
    0 < allocatedSitePrimitiveTolerance m p w v E :=
  physicalIdealErrorShare_pos _ _

theorem allocatedSitePrimitiveTolerance_le_one (m : ℕ) {p w v E : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    allocatedSitePrimitiveTolerance m p w v E ≤ 1 :=
  physicalIdealErrorShare_le_one hE
    (allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hp).1 hw hv)

theorem allocatedSitePrimitiveTolerance_inv (m : ℕ) (p w v E : ℝ) :
    (allocatedSitePrimitiveTolerance m p w v E)⁻¹ =
      Real.exp (E + allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) w v + 3) :=
  physicalIdealErrorShare_inv _ _

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedSiteSpatialMass_primitive_bound
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1)) (CM Cf : ℝ≥0) (C : Fin m → ℝ≥0)
    {p w v : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hM : (M : ℝ) ≤ Real.exp p) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    (hCM : (CM : ℝ) ≤ Real.exp w) (hCf : (Cf : ℝ) ≤ Real.exp v) :
    ((Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ) *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) ≤
      Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) w v) := by
  let D := allocatedComparisonDimension m p
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  obtain ⟨hD, hmD, hpD, _⟩ := allocatedComparisonDimension_bounds m hp
  have hQD (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans ((hJ j).trans hpD)
  have hper : (period : ℝ) ≤ Real.exp (D ^ 2) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
      _ ≤ Real.exp p ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = Real.exp ((m + 1 : ℕ) * p) := (Real.exp_nat_mul p (m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [pow_two] using mul_le_mul hmD hpD hp hD)
  exact allocatedSiteSpatialMass_exp_bound O Q J C period _ _ CM Cf hd.nonneg hw
    hd.degree hd.rows hQD (fun j => (hJ j).trans hpD) hd.axes hd.outputs
    (fun j => (hC j).trans (Real.exp_le_exp.mpr hpD)) hper hCM hCf

theorem allocatedSiteSpatial_primitive_error_budget
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1)) (CM Cf : ℝ≥0) (C : Fin m → ℝ≥0)
    {p w v E δ δFourier ε : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hM : (M : ℝ) ≤ Real.exp p) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    (hCM : (CM : ℝ) ≤ Real.exp w) (hCf : (Cf : ℝ) ≤ Real.exp v)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p w v E)
    (hδFourier : δFourier ≤ physicalIdealErrorShare E 1)
    (hε : ε ≤ physicalIdealErrorShare E 1) :
    δ * ((Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ) *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) + 2 * δFourier + ε ≤
      Real.exp (-E) := by
  have hmass := allocatedSiteSpatialMass_primitive_bound B U b rows hq hinj hb bW M period
    hperiod CM Cf C hp hw hvars hI hn hJ hM hC hCM hCf
  have herr := allocatedSiteSpatial_error_budget (by positivity) hmass hδ hδFourier hε
  simpa only [mul_assoc] using herr

end Erdos3.VectorPolynomial

end

end OAI
