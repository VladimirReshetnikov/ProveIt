import OAI.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
import OAI.Combinatorics.Progressions.Linear.RankDependentInputBudget
import OAI.Combinatorics.Progressions.Linear.RefiltrationLayerBasis

namespace OAI

section

namespace Erdos3

def refiltrationCoordinateBudget (p : ℝ) : ℝ :=
  ((p + 1 + (p + 3) ^ 7 + 2) ^ 9 + p + 4) ^ 4

theorem refiltrationCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ refiltrationCoordinateBudget p := by
  unfold refiltrationCoordinateBudget
  positivity

namespace NilpotentLieFiltration

open Module

theorem exists_refiltration_bases_in_coordinates
    {ι κ ν L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℚ L) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ i j, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v i) j) ≤ p)
    (he : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) :
    ∀ d, ∃ a : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer U d))) ℚ
        (F.gradedRefiltrationLayer U d),
      ∀ i j, rationalLogHeight (b.repr (a i : L) j) ≤ refiltrationCoordinateBudget p := by
  let H := ⌈Real.exp p⌉₊
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨B, _, hB, hbasis⟩ := F.exists_uniform_refiltration_layer_bases e ω hF U v hspan
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hv i j))
    (by linarith : 0 ≤ p + 1) (hd.trans (by linarith)) (hκ.trans (by linarith)) hHp
  let r := (p + 1 + (p + 3) ^ 7 + 2) ^ 9
  have hBr : (B : ℝ) ≤ Real.exp r := by
    simpa only [r, show p + 1 + 2 = p + 3 by ring] using hB
  let t := r + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hHt : (H : ℝ) ≤ Real.exp t :=
    hHp.trans (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  intro d
  obtain ⟨a, ha⟩ := hbasis d
  refine ⟨a, ?_⟩
  intro i j
  have hx : ∀ k, rationalLogHeight (e.repr (a i : L) k) ≤ t := fun k =>
    (rationalLogHeight_le_of_height (ha i k) hBr).trans hrt
  have h := rational_basis_coordinates_logHeight e b ht (hd.trans hpt) hHt
    (fun i j => rationalHeightLE_ceil_exp (he i j)) (a i : L) hx j
  have hshape : t + 2 = r + p + 4 := by dsimp [t]; ring
  rw [hshape] at h
  exact h

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

def horizontalCoordinateBudget (p : ℝ) : ℝ :=
  p + p * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)

theorem horizontalCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ horizontalCoordinateBudget p := by
  have h := refiltrationCoordinateBudget_nonneg hp
  unfold horizontalCoordinateBudget
  positivity

theorem horizontalCoordinateHeight_bound {p : ℝ} (hp : 0 ≤ p)
    (n H K : ℕ) (hn : (n : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (refiltrationCoordinateBudget p + 1))
    (hK : (K : ℝ) ≤ Real.exp ((p + 3) ^ 7)) :
    (((n + 1) * (H * K) ^ n : ℕ) : ℝ) ≤ Real.exp (horizontalCoordinateBudget p) := by
  have hcount : (n : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hsum : 0 ≤ refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7 := by
    have h := refiltrationCoordinateBudget_nonneg hp
    positivity
  calc
    _ ≤ Real.exp p * (Real.exp (refiltrationCoordinateBudget p + 1) *
        Real.exp ((p + 3) ^ 7)) ^ n := by
      push_cast
      gcongr
    _ = Real.exp (p + (n : ℝ) * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hsum))

end Erdos3

end

section

namespace Erdos3

def nativeCoordinateBaseBudget (s : ℕ) (P : ℝ) : ℝ :=
  4 * P + (P + 3) ^ 7 + horizontalCoordinateBudget P +
    (s : ℝ) * P + (P + 3) ^ 2 + 4

def nativeCoordinateInputBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeCoordinateBaseBudget s P + (nativeCoordinateBaseBudget s P + 2) ^ 3 + P + 2

noncomputable def nativeDependentBudget (s : ℕ) (P : ℝ) : ℝ :=
  let Z := rankDependentInputBudget (nativeCoordinateInputBudget s P)
  Z + sparseGeneratorBudget Z

noncomputable def nativeCoordinateSeparationBudget (s : ℕ) (P : ℝ) : ℝ :=
  separationBudget (nativeCoordinateInputBudget s P) + separationBudget (nativeDependentBudget s P)

noncomputable def nativeDependentDenominatorBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeDependentBudget s P + (nativeDependentBudget s P + 2) ^ 3 +
    (nativeDependentBudget s P + 2) ^ 36

noncomputable def nativeDependentSlowBudget (s : ℕ) (P : ℝ) : ℝ :=
  (nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
    nativeDependentBudget s P + 1

theorem nativeCoordinateBaseBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateBaseBudget s P ∧ 4 * P ≤ nativeCoordinateBaseBudget s P ∧
      P ≤ nativeCoordinateBaseBudget s P ∧ (P + 3) ^ 7 + 1 ≤ nativeCoordinateBaseBudget s P ∧
      horizontalCoordinateBudget P + 1 ≤ nativeCoordinateBaseBudget s P ∧
      (P + 3) ^ 2 + (s : ℝ) * P ≤ nativeCoordinateBaseBudget s P := by
  have hH := horizontalCoordinateBudget_nonneg hP
  have h₇ : 0 ≤ (P + 3) ^ 7 := by positivity
  have h₂ : 0 ≤ (P + 3) ^ 2 := sq_nonneg _
  have hs : 0 ≤ (s : ℝ) * P := mul_nonneg (Nat.cast_nonneg s) hP
  unfold nativeCoordinateBaseBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nativeCoordinateInputBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    nativeCoordinateBaseBudget s P ≤ nativeCoordinateInputBudget s P ∧
      (nativeCoordinateBaseBudget s P + 2) ^ 3 + P ≤ nativeCoordinateInputBudget s P ∧
      1 + (nativeCoordinateBaseBudget s P + 2) ^ 3 + nativeCoordinateBaseBudget s P ≤
        nativeCoordinateInputBudget s P := by
  have hU := (nativeCoordinateBaseBudget_bounds s hP).1
  have hc : 0 ≤ (nativeCoordinateBaseBudget s P + 2) ^ 3 := by positivity
  unfold nativeCoordinateInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem nativeCoordinateInputBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateInputBudget s P :=
  (nativeCoordinateBaseBudget_bounds s hP).1.trans (nativeCoordinateInputBudget_bounds s hP).1

theorem nativeDependentBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeDependentBudget s P := by
  have hZ := (rankDependentInputBudget_bounds (nativeCoordinateInputBudget_nonneg s hP)).1
  exact add_nonneg hZ (sparseGeneratorBudget_nonneg hZ)

theorem nativeCoordinateSeparationBudget_cutoffs (s : ℕ) {P N : ℝ} (hP : 0 ≤ P)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    Real.exp (separationBudget (nativeCoordinateInputBudget s P)) ≤ N ∧
      Real.exp (separationBudget (nativeDependentBudget s P)) ≤ N := by
  have h₁ := separationBudget_nonneg (nativeCoordinateInputBudget_nonneg s hP)
  have h₂ := separationBudget_nonneg (nativeDependentBudget_nonneg s hP)
  constructor
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_right h₂)).trans hN
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_left h₁)).trans hN

theorem nativeDependentSlowBudget_bound (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    Real.exp (nativeDependentBudget s P) +
        Real.exp ((nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
          nativeDependentBudget s P) ≤ Real.exp (nativeDependentSlowBudget s P) := by
  let Q := nativeDependentBudget s P
  let L := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q
  have hQ : 0 ≤ Q := nativeDependentBudget_nonneg s hP
  have hQL : Q ≤ L := by
    have h₁ : 0 ≤ (Q + 2) ^ 3 := by positivity
    have h₂ : 0 ≤ (Q + 2) ^ 18 := by positivity
    dsimp only [L]
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp Q + Real.exp L ≤ 2 * Real.exp L := by linarith [Real.exp_le_exp.mpr hQL]
    _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (L + 1) := (mul_comm _ _).trans (Real.exp_add L 1).symm

end Erdos3

end

section

namespace Erdos3

theorem nativeCoordinate_denominator_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ℕ) {P : ℝ} (hP : 0 ≤ P)
    (A : Matrix ι κ ℚ) (l : ℕ) (hl : (l : ℝ) ≤ Real.exp P)
    (hrows : (Fintype.card ι : ℝ) ≤ P) (hcols : (Fintype.card κ : ℝ) ≤ P)
    (hA : ∀ i j, rationalLogHeight (A i j) ≤ (P + 3) ^ 7) :
    ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hU 1 (hrows.trans hPU) (hcols.trans hPU) (by
      intro i j
      apply ((rationalLogHeight_le_iff (A i j) _).mp (hA i j)).2.trans
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      linarith)
  rw [Nat.cast_mul]
  calc
    (matrixDenominator A : ℝ) * l ≤
        Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) * Real.exp P :=
      mul_le_mul hden hl (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3 + P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.1

theorem nativeCoordinate_slow_bound (s : ℕ) {P p : ℝ} (hP : 0 ≤ P) (hpP : p ≤ P)
    (n K : ℕ) (hn : (n : ℝ) ≤ P) (hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1)) :
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
      Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, hSU⟩ := nativeCoordinateBaseBudget_bounds s hP
  let U := nativeCoordinateBaseBudget s P
  have hKU : (K : ℝ) ≤ Real.exp ((U + 2) ^ 1) := by
    apply hK.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hfac : ((n : ℝ) + 1) * (K + 1) ≤ Real.exp ((U + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power n hU (hn.trans hPU) 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hKU le_rfl) (by positivity)
  have hSU' : (P + 3) ^ 2 + (s : ℝ) * p ≤ U :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s))).trans hSU
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
        Real.exp 1 * (Real.exp ((U + 2) ^ 3) * Real.exp U) :=
      mul_le_mul htwo (mul_le_mul hfac (Real.exp_le_exp.mpr hSU')
        (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (1 + (U + 2) ^ 3 + U) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.2

end Erdos3

end

end OAI
