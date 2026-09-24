import Diophantine.Common.PolynomialDegree
import Diophantine.Common.PolynomialRenaming
import Diophantine.Paper1982.EnumerationQuadratic
import Diophantine.Paper1982.Master1
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Normalized quartics for arbitrary Diophantine sets

Each integer node in the finite gate system is represented by a difference
of two natural witnesses. All gate residuals remain quadratic. One further
witness is constrained to equal one, making the sum of squared residuals
nonzero at the zero witness tuple, independently of the input.

For enumeration index `n` this gives an ordinary integer polynomial in
`Fin (6*n+8)`, with input coordinate zero and `6*n+7` witnesses. Its degree
is at most four and its natural solutions represent `Jones1978.W n`.
The existing enumeration theorem then covers any `IsDiophantine` set on
positive inputs. No recursively enumerable representation theorem is used.
-/

namespace Jones1982
namespace EnumerationQuartic

open EnumerationQuadratic

/-- Two natural components for each integer node and one guard witness.
`false` selects the positive component, `true` the negative component. -/
abbrev Witness (n : ℕ) := (GateIndex n × Bool) ⊕ Unit

theorem card_witness (n : ℕ) : Fintype.card (Witness n) = 6 * n + 7 := by
  simp [Witness, GateIndex]
  omega

abbrev Poly (n : ℕ) := MvPolynomial (Option (Witness n)) ℤ

/-- A difference of two independent natural witness coordinates. -/
noncomputable def nodePolynomial (n : ℕ) (k : GateIndex n) : Poly n :=
  MvPolynomial.X (some (.inl (k, false))) - MvPolynomial.X (some (.inl (k, true)))

private theorem degree_sub_le {σ : Type*} {p q : MvPolynomial σ ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p - q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

private theorem degree_add_le {σ : Type*} {p q : MvPolynomial σ ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p + q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

theorem nodePolynomial_totalDegree_le_one (n : ℕ) (k : GateIndex n) :
    (nodePolynomial n k).totalDegree ≤ 1 :=
  degree_sub_le (MvPolynomial.totalDegree_X _).le (MvPolynomial.totalDegree_X _).le

private theorem nodePolynomial_totalDegree_le_two (n : ℕ) (k : GateIndex n) :
    (nodePolynomial n k).totalDegree ≤ 2 :=
  (nodePolynomial_totalDegree_le_one n k).trans (by decide)

/-- The finite list of quadratic conditions, including the guard. -/
inductive Equation (n : ℕ)
  | guard
  | zero
  | output
  | add (i : Fin (n + 1))
  | mul (i : Fin (n + 1))
  deriving DecidableEq, Fintype

/-- All residuals as ordinary integer multivariate polynomials. -/
noncomputable def residual (n : ℕ) : Equation n → Poly n
  | .guard => MvPolynomial.X (some (.inr ())) - 1
  | .zero => nodePolynomial n (nodeZero n)
  | .output => nodePolynomial n (nodeLeft n (Fin.last n)) -
      (nodePolynomial n (nodeRight n (Fin.last n)) + MvPolynomial.X none)
  | .add i => nodePolynomial n (nodeAdd n i) -
      (nodePolynomial n (nodeLeft n i) + nodePolynomial n (nodeRight n i))
  | .mul i => nodePolynomial n (nodeMul n i) -
      nodePolynomial n (nodeLeft n i) * nodePolynomial n (nodeRight n i)

theorem residual_totalDegree_le_two (n : ℕ) (i : Equation n) :
    (residual n i).totalDegree ≤ 2 := by
  cases i with
  | guard => exact degree_sub_le (by simp) (by simp)
  | zero => exact nodePolynomial_totalDegree_le_two _ _
  | output =>
      exact degree_sub_le (nodePolynomial_totalDegree_le_two _ _)
        (degree_add_le (nodePolynomial_totalDegree_le_two _ _) (by simp))
  | add i =>
      exact degree_sub_le (nodePolynomial_totalDegree_le_two _ _)
        (degree_add_le (nodePolynomial_totalDegree_le_two _ _)
          (nodePolynomial_totalDegree_le_two _ _))
  | mul i =>
      apply degree_sub_le (nodePolynomial_totalDegree_le_two _ _)
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add (nodePolynomial_totalDegree_le_one _ _)
          (nodePolynomial_totalDegree_le_one _ _))

noncomputable def sumSquares (n : ℕ) : Poly n :=
  ∑ i : Equation n, residual n i ^ 2

theorem sumSquares_totalDegree_le_four (n : ℕ) :
    (sumSquares n).totalDegree ≤ 4 :=
  Diophantine.totalDegree_sum_pow_le Finset.univ (residual n) 2 2
    (fun idx _ => residual_totalDegree_le_two n idx)

/-- The input and natural witnesses, evaluated in the integer ring. -/
def assignment {n : ℕ} (x : ℕ) (v : Witness n → ℕ) : Option (Witness n) → ℤ
  | none => x
  | some k => v k

def nodeValues {n : ℕ} (v : Witness n → ℕ) : GateIndex n → ℤ :=
  fun k => (v (.inl (k, false)) : ℤ) - v (.inl (k, true))

@[simp] theorem eval_nodePolynomial (n x : ℕ) (v : Witness n → ℕ) (k : GateIndex n) :
    MvPolynomial.eval (assignment x v) (nodePolynomial n k) = nodeValues v k := by
  simp only [nodePolynomial, MvPolynomial.eval_sub, MvPolynomial.eval_X,
    assignment, nodeValues]

/-- Arithmetic evaluation of the finite gate residuals. -/
def residualValue (n x : ℕ) (v : Witness n → ℕ) : Equation n → ℤ
  | .guard => (v (.inr ()) : ℤ) - 1
  | .zero => nodeValues v (nodeZero n)
  | .output => nodeValues v (nodeLeft n (Fin.last n)) -
      (nodeValues v (nodeRight n (Fin.last n)) + x)
  | .add i => nodeValues v (nodeAdd n i) -
      (nodeValues v (nodeLeft n i) + nodeValues v (nodeRight n i))
  | .mul i => nodeValues v (nodeMul n i) -
      nodeValues v (nodeLeft n i) * nodeValues v (nodeRight n i)

theorem eval_residual (n x : ℕ) (v : Witness n → ℕ) (i : Equation n) :
    MvPolynomial.eval (assignment x v) (residual n i) = residualValue n x v i := by
  cases i <;>
    simp only [residual, residualValue, MvPolynomial.eval_sub, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_X, map_one, eval_nodePolynomial, assignment]

theorem residuals_zero_iff (n x : ℕ) (v : Witness n → ℕ) :
    (∀ i : Equation n, MvPolynomial.eval (assignment x v) (residual n i) = 0) ↔
      v (.inr ()) = 1 ∧ GateSys n x (nodeValues v) := by
  simp only [eval_residual]
  constructor
  · intro h
    have hg : (v (.inr ()) : ℤ) = 1 := sub_eq_zero.mp (h .guard)
    refine ⟨by exact_mod_cast hg, ?_⟩
    exact {
      zero := h .zero
      output := sub_eq_zero.mp (h .output)
      add := fun i => sub_eq_zero.mp (h (.add i))
      mul := fun i => sub_eq_zero.mp (h (.mul i))
    }
  · rintro ⟨hg, h⟩ i
    cases i with
    | guard => simp [residualValue, hg]
    | zero => exact h.zero
    | output => exact sub_eq_zero.mpr h.output
    | add i => exact sub_eq_zero.mpr (h.add i)
    | mul i => exact sub_eq_zero.mpr (h.mul i)

theorem eval_sumSquares_eq_zero_iff (n : ℕ) (a : Option (Witness n) → ℤ) :
    MvPolynomial.eval a (sumSquares n) = 0 ↔
      ∀ i : Equation n, MvPolynomial.eval a (residual n i) = 0 := by
  simp only [sumSquares, MvPolynomial.eval_sum, MvPolynomial.eval_pow]
  simpa only [pow_two, Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Equation n))
      (fun i => MvPolynomial.eval a (residual n i)))

/-- Every integer node has a difference-of-naturals representation. The
guard is chosen to be one. -/
def naturalWitnesses {n : ℕ} (t : GateIndex n → ℤ) : Witness n → ℕ
  | .inl (k, false) => (t k).toNat
  | .inl (k, true) => (-t k).toNat
  | .inr _ => 1

@[simp] theorem nodeValues_naturalWitnesses {n : ℕ} (t : GateIndex n → ℤ) :
    nodeValues (naturalWitnesses t) = t := by
  funext k
  dsimp [nodeValues, naturalWitnesses]
  omega

/-- The unrenamed quartic has natural solutions exactly for members of
the corresponding enumeration set. -/
theorem exists_sumSquares_iff (n x : ℕ) :
    (∃ v : Witness n → ℕ, MvPolynomial.eval (assignment x v) (sumSquares n) = 0) ↔
      x ∈ Jones1978.W n := by
  constructor
  · rintro ⟨v, hv⟩
    rw [eval_sumSquares_eq_zero_iff, residuals_zero_iff] at hv
    exact mem_of_gateSys hv.2
  · intro hx
    obtain ⟨t, ht⟩ := exists_gateSys_of_mem hx
    refine ⟨naturalWitnesses t, ?_⟩
    rw [eval_sumSquares_eq_zero_iff, residuals_zero_iff]
    exact ⟨rfl, by simpa only [nodeValues_naturalWitnesses] using ht⟩

/-- The guard residual is minus one at the zero witness tuple. -/
theorem sumSquares_nonzero_at_zeroWitnesses (n x : ℕ) :
    MvPolynomial.eval (assignment x (fun _ => 0)) (sumSquares n) ≠ 0 := by
  intro h
  have hg := (eval_sumSquares_eq_zero_iff n (assignment x (fun _ => 0))).mp h
    Equation.guard
  rw [eval_residual] at hg
  norm_num [residualValue] at hg

/-- Index the named witnesses by `Fin (6*n+7)`. -/
noncomputable def witnessIndex (n : ℕ) : Witness n ≃ Fin (6 * n + 7) :=
  Fintype.equivFinOfCardEq (card_witness n)

/-- Renaming preserves input coordinate zero. -/
noncomputable def coordinate (n : ℕ) : Option (Witness n) ≃ Fin (6 * n + 8) :=
  (Equiv.optionCongr (witnessIndex n)).trans (finSuccEquiv (6 * n + 7)).symm

@[simp] theorem coordinate_none (n : ℕ) : coordinate n none = 0 := by
  simp [coordinate]

@[simp] theorem coordinate_some (n : ℕ) (k : Witness n) :
    coordinate n (some k) = ((witnessIndex n) k).succ := by
  simp [coordinate]

@[simp] theorem coordinate_symm_zero (n : ℕ) : (coordinate n).symm 0 = none := by
  exact (coordinate n).injective (by simp)

/-- An explicit normalized quartic in standard coordinates, with `6*n+7`
natural witnesses and the input at coordinate zero. -/
noncomputable def quartic (n : ℕ) : MvPolynomial (Fin (6 * n + 8)) ℤ :=
  MvPolynomial.rename (coordinate n) (sumSquares n)

theorem quartic_totalDegree_le_four (n : ℕ) : (quartic n).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (sumSquares_totalDegree_le_four n)

theorem wset_quartic_iff (n x : ℕ) : Wset (quartic n) x ↔ x ∈ Jones1978.W n := by
  rw [← exists_sumSquares_iff]
  have h := Diophantine.exists_eval_rename_option_iff (coordinate n) (sumSquares n)
    (fun value : ℕ => (value : ℤ)) x 0
  simp only [coordinate_none, Function.comp_def] at h
  refine h.trans ?_
  apply exists_congr
  intro v
  apply Iff.of_eq
  apply congrArg (fun values : Option (Witness n) → ℤ =>
    MvPolynomial.eval values (sumSquares n) = 0)
  funext idx
  cases idx <;> rfl

theorem quartic_normalized (n : ℕ) : Normalized (quartic n) := by
  intro x
  have heval := Diophantine.eval_rename_zeroWitnesses (coordinate n) (sumSquares n) (x : ℤ)
  simp only [coordinate_none] at heval
  change MvPolynomial.eval _ (MvPolynomial.rename (coordinate n) (sumSquares n)) ≠ 0
  rw [heval]
  refine (congrArg (fun values : Option (Witness n) → ℤ =>
    MvPolynomial.eval values (sumSquares n) ≠ 0) ?_).mp
      (sumSquares_nonzero_at_zeroWitnesses n x)
  funext idx
  cases idx <;> rfl

/-- Arbitrary-degree Diophantine representations have normalized quartics
with finitely many natural witnesses. This does not assume DPRM. -/
theorem exists_normalized_quartic_representation {S : Set ℕ}
    (hS : Jones1978.IsDiophantine S) :
    ∃ (ν : ℕ), 1 ≤ ν ∧ ∃ P : MvPolynomial (Fin (ν + 1)) ℤ,
      P.totalDegree ≤ 4 ∧ Normalized P ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Wset P x) := by
  obtain ⟨n, hn⟩ := Jones1978.lemma_3_1 hS
  refine ⟨6 * n + 7, by omega, quartic n, quartic_totalDegree_le_four n,
    quartic_normalized n, ?_⟩
  exact fun x hx => (hn x hx).trans (wset_quartic_iff n x).symm

end EnumerationQuartic
end Jones1982
