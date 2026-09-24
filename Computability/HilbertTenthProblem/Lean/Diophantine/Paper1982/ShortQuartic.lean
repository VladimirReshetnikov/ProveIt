import Diophantine.Common.PolynomialRenaming
import Diophantine.Paper1982.ShortQuadraticBridgeDefs
import Diophantine.Paper1982.ShortQuadraticIndex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The explicit quartic in the repository's standard coordinates

Renaming puts the input in coordinate zero and the 58 witnesses in the
remaining coordinates. Shifting the witnesses identifies nonnegative
solutions of this quartic with positive solutions of the quadratic system.
-/

namespace Jones1982.ShortQuadratic

/-- The 58 named witnesses, indexed by an ordinary finite type. -/
noncomputable def witnessIndex : ShortQuadraticVar ≃ Fin 58 :=
  Fintype.equivFinOfCardEq ShortQuadraticVar.card

/-- Coordinate zero is the input; the other 58 coordinates are witnesses. -/
noncomputable def coordinate : Option ShortQuadraticVar ≃ Fin 59 :=
  (Equiv.optionCongr witnessIndex).trans (finSuccEquiv 58).symm

@[simp] theorem coordinate_none : coordinate none = 0 := by
  simp [coordinate]

@[simp] theorem coordinate_some (idx : ShortQuadraticVar) :
    coordinate (some idx) = (witnessIndex idx).succ := by
  simp [coordinate]

@[simp] theorem coordinate_symm_zero : coordinate.symm 0 = none := by
  exact coordinate.injective (by simp)

/-- The concrete polynomial with one input and exactly 58 witness coordinates. -/
noncomputable def quartic58 (z u y L : ℕ) : MvPolynomial (Fin 59) ℤ :=
  MvPolynomial.rename coordinate (shiftedSumSquares z u y L)

theorem quartic58_totalDegree_le_four (z u y L : ℕ) :
    (quartic58 z u y L).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans
    (shiftedSumSquares_totalDegree_le_four z u y L)

/-- Shifting by one is a bijection between natural witnesses and positive
natural witnesses, and the sum of squares enforces every residual. -/
theorem exists_shifted_iff (x z u y L : ℕ) :
    (∃ v : ShortQuadraticVar → ℕ,
      MvPolynomial.eval (assignment x v) (shiftedSumSquares z u y L) = 0) ↔
      Nonempty (PositiveWitnesses x z u y L) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨⟨fun idx => v idx + 1, fun idx => Nat.succ_pos _, ?_⟩⟩
    have ha : shiftAssignment (assignment x v) =
        assignment x (fun idx => v idx + 1) := by
      funext idx
      cases idx <;> simp [shiftAssignment, assignment]
    rw [eval_shiftedSumSquares, ha, eval_sumSquares_eq_zero_iff] at hv
    exact hv
  · rintro ⟨h⟩
    refine ⟨fun idx => h.val idx - 1, ?_⟩
    have ha : shiftAssignment (assignment x (fun idx => h.val idx - 1)) =
        assignment x h.val := by
      funext idx
      cases idx with
      | none => rfl
      | some idx =>
        have hj : 1 ≤ h.val idx := h.pos idx
        simp [shiftAssignment, assignment, Nat.cast_sub hj]
    rw [eval_shiftedSumSquares, ha, eval_sumSquares_eq_zero_iff]
    exact h.equations

/-- Renaming preserves the distinguished input and all existential witnesses. -/
theorem wset_quartic58_iff (x z u y L : ℕ) :
    Wset (quartic58 z u y L) x ↔ Nonempty (PositiveWitnesses x z u y L) := by
  rw [← exists_shifted_iff]
  have h := Diophantine.exists_eval_rename_option_iff coordinate (shiftedSumSquares z u y L)
    (fun value : ℕ => (value : ℤ)) x 0
  simp only [coordinate_none, Function.comp_def] at h
  refine h.trans ?_
  apply exists_congr
  intro v
  apply Iff.of_eq
  apply congrArg (fun values : Option ShortQuadraticVar → ℤ =>
    MvPolynomial.eval values (shiftedSumSquares z u y L) = 0)
  funext idx
  cases idx <;> rfl

/-- The same 58 witnesses suffice for normalization in standard coordinates. -/
theorem quartic58_normalized (z u y L : ℕ) (hu : 2 * z < u) :
    Normalized (quartic58 z u y L) := by
  intro x
  have heval := Diophantine.eval_rename_zeroWitnesses coordinate
    (shiftedSumSquares z u y L) (x : ℤ)
  simp only [coordinate_none] at heval
  change MvPolynomial.eval _ (MvPolynomial.rename coordinate (shiftedSumSquares z u y L)) ≠ 0
  rw [heval]
  refine (congrArg (fun values : Option ShortQuadraticVar → ℤ =>
    MvPolynomial.eval values (shiftedSumSquares z u y L) ≠ 0) ?_).mp
      (shiftedSumSquares_nonzero_at_zeroWitnesses z u y L hu x)
  funext idx
  cases idx <;> rfl

theorem quartic58_index_normalized {ν : ℕ}
    {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}
    (hI : Index ν P z u y) (hν : 1 ≤ ν) :
    Normalized (quartic58 z u y (L4 ν)) :=
  quartic58_normalized z u y (L4 ν) (hI.two_mul_lt_u hν)

end Jones1982.ShortQuadratic
