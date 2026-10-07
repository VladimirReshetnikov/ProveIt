import OAI.Combinatorics.Progressions.Linear.RationalClearedMatrixReal
import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

theorem rational_matrix_column_mem_denominatorGrid {ι κ : Type*}
    [Fintype ι] [Fintype κ] (S : Matrix ι κ ℚ) (j : κ) :
    (fun i => (S i j : ℝ)) ∈ realDenominatorGrid (matrixDenominator S) := by
  classical
  refine ⟨fun i => clearedMatrix S i j, funext (fun i => ?_)⟩
  exact (matrixDenominator_mul_entry_real S i j).symm

theorem rational_matrix_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ a)) ∧
    0 < matrixDenominator S ∧
    (matrixDenominator S : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) ∧
    ∀ i j, ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = z := by
  refine ⟨?_, matrixDenominator_pos S, ?_, ?_⟩
  · intro i j
    exact (rational_abs_real_le_numerator (S i j)).trans (hS i j).1
  · apply matrixDenominator_le_exp_power S hp a hι hκ
    intro i j
    exact (hS i j).2
  · exact matrixDenominator_mul_entry_real_integral S

theorem rational_section_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ 45)) ∧
    ∃ q : ℕ, q = matrixDenominator S ∧ 0 < q ∧
      (q : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
      ∀ i j, ∃ z : ℤ, (q : ℝ) * (S i j : ℝ) = z := by
  obtain ⟨hentry, hpos, hden, hint⟩ := rational_matrix_entry_budget S hp 45 hι hκ hS
  exact ⟨hentry, matrixDenominator S, rfl, hpos, hden, hint⟩

end Erdos3

end

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem representativeInclusion_scaledIntegerGrid_subset (A : Matrix ι κ ℚ) (l : ℕ) :
    scaledIntegerGrid (l * matrixDenominator A) ⊆ A.mulVec ⁻¹' scaledIntegerGrid l := by
  classical
  rintro x ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := integralVector_denominator_mulVec A (fun i => (z i : ℚ))
    ⟨z, fun _ => rfl⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul, funext hw]

theorem representativeInclusion_matrixDenominator_le_exp
    (A : Matrix ι κ ℚ) {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hH : (H : ℝ) ≤ Real.exp p) :
    (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power A hp 1 hι hκ
  intro i j
  have hd : ((A i j).den : ℝ) ≤ H := by exact_mod_cast (hA i j).2
  simpa only [pow_one] using
    hd.trans (hH.trans (Real.exp_le_exp.mpr (by linarith : p ≤ p + 2)))

theorem representativeInclusion_denominator_spec
    (A : Matrix ι κ ℚ) {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hH : (H : ℝ) ≤ Real.exp p) :
    0 < matrixDenominator A ∧
      (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∀ i j, ∃ z : ℤ, (matrixDenominator A : ℝ) * (A i j : ℝ) = (z : ℝ) :=
  ⟨matrixDenominator_pos A,
    representativeInclusion_matrixDenominator_le_exp A hp hι hκ hA hH,
    matrixDenominator_mul_entry_real_integral A⟩

theorem representativeInclusion_gridDenominator_le_exp
    (A : Matrix ι κ ℚ) (l : ℕ) {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((l * matrixDenominator A : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hq := representativeInclusion_matrixDenominator_le_exp A hp hι hκ hA hH
  have hbudget : p + (p + 2) ^ 3 ≤ (p + 2) ^ 4 := by
    have hc : p ≤ (p + 2) ^ 3 := le_power_budget hp (by norm_num)
    calc
      _ ≤ 2 * (p + 2) ^ 3 := by linarith
      _ ≤ (p + 2) * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 3) :=
      mul_le_mul hl hq (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 3) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hbudget

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Matrix

def lieSubalgebraRepresentativeHeight (d r H : ℕ) : ℕ :=
  rationalLieStructureHeight d (max H (rationalSolveHeight r H))

noncomputable def lieSubalgebraRepresentativeParameter (p : ℝ) : ℝ := (p + 2) ^ 12

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]

theorem lieSubalgebraRepresentative_bracket_height (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k)
      (lieSubalgebraRepresentativeHeight (Fintype.card ι) (Fintype.card κ) H) := by
  obtain ⟨P, hP, hPH, hsource⟩ := exists_bounded_lie_embedding_retraction bk b K.incl
    (fun _ _ h => Subtype.ext h) hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hinc i j)
  exact hsource

theorem lieSubalgebraRepresentativeHeight_le_exp (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤ Real.exp ((p + 2) ^ 11) :=
  rationalLieStructureHeight_inverse_budget d r H hp hd hr hH

theorem lieSubalgebraRepresentativeParameter_dimension {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    (r : ℝ) ≤ lieSubalgebraRepresentativeParameter p :=
  hr.trans (le_power_budget hp (by decide : 1 ≤ 12))

theorem lieSubalgebraRepresentativeParameter_pos {p : ℝ} (hp : 0 ≤ p) :
    0 < lieSubalgebraRepresentativeParameter p := by
  unfold lieSubalgebraRepresentativeParameter
  positivity

theorem lieSubalgebraRepresentativeHeight_le_exp_parameter (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤
      Real.exp (lieSubalgebraRepresentativeParameter p) := by
  apply (lieSubalgebraRepresentativeHeight_le_exp d r H hp hd hr hH).trans
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 11 ≤ 12)

noncomputable def lieSubalgebraInclusionDenominator (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) : ℕ :=
  matrixDenominator (fun i j => b.repr (bk j : L) i)

theorem lieSubalgebraInclusionDenominator_spec {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L] (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H)
    (hH : (H : ℝ) ≤ Real.exp p) :
    0 < lieSubalgebraInclusionDenominator b K bk ∧
      (lieSubalgebraInclusionDenominator b K bk : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∀ i j, ∃ z : ℤ, (lieSubalgebraInclusionDenominator b K bk : ℝ) *
        (b.repr (bk j : L) i : ℝ) = (z : ℝ) :=
  representativeInclusion_denominator_spec (fun i j => b.repr (bk j : L) i)
    hp hι hκ hinc hH

theorem lieSubalgebraInclusionDenominator_grid_bound {ι κ L : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((l * lieSubalgebraInclusionDenominator b K bk : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) :=
  representativeInclusion_gridDenominator_le_exp (fun i j => b.repr (bk j : L) i)
    l hp hι hκ hinc hH hl

theorem lieSubalgebraRepresentativeBudget_spec (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) (l : ℕ) {H : ℕ} {p : ℝ}
    (hHpos : 1 ≤ H) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    let HC := lieSubalgebraRepresentativeHeight (Fintype.card ι) (Fintype.card κ) H
    let q := lieSubalgebraInclusionDenominator b K bk
    let t := lieSubalgebraRepresentativeParameter p
    (∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) HC) ∧
      (HC : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ 0 < q ∧
      (q : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ((l * q : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      0 < t ∧ (Fintype.card κ : ℝ) ≤ t ∧
      (HC : ℝ) ≤ Real.exp t ∧ ((l * q : ℕ) : ℝ) ≤ Real.exp t := by
  dsimp only
  have hq := lieSubalgebraInclusionDenominator_spec b K bk hp hι hκ hinc hH
  have hgrid := lieSubalgebraInclusionDenominator_grid_bound b K bk l hp hι hκ hinc hH hl
  refine ⟨lieSubalgebraRepresentative_bracket_height b K bk hHpos hc hinc,
    lieSubalgebraRepresentativeHeight_le_exp _ _ H hp hι hκ hH,
    hq.1, hq.2.1, hgrid, lieSubalgebraRepresentativeParameter_pos hp,
    lieSubalgebraRepresentativeParameter_dimension hp hκ,
    lieSubalgebraRepresentativeHeight_le_exp_parameter _ _ H hp hι hκ hH, ?_⟩
  apply hgrid.trans (Real.exp_le_exp.mpr ?_)
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 4 ≤ 12)

end Erdos3

end

end OAI
