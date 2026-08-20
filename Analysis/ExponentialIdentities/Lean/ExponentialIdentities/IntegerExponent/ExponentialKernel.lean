import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Set

namespace LeanProofs.IntegerExponent

private theorem exp_sum_coeff_eq_zero :
    ∀ n : ℕ, ∀ (a b : Fin n → ℝ), StrictMono a → StrictMono b →
      ∀ c : Fin n → ℝ,
        (∀ i, ∑ j, Real.exp (a i * b j) * c j = 0) → c = 0 := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb c h
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro a b ha hb c hzero
      let b' : Fin n → ℝ := fun j ↦ b j.succ - b 0
      let g : ℝ → ℝ := fun t ↦
        ∑ j : Fin n, Real.exp (t * b' j) * c j.succ
      let dg : ℝ → ℝ := fun t ↦
        ∑ j : Fin n, (Real.exp (t * b' j) * b' j) * c j.succ

      have hfactor (i : Fin (n + 1)) :
          (∑ j : Fin (n + 1), Real.exp (a i * b j) * c j) =
            Real.exp (a i * b 0) * (c 0 + g (a i)) := by
        rw [Fin.sum_univ_succ, mul_add]
        dsimp only [g]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [b']
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

      have hg_value (i : Fin (n + 1)) : g (a i) = -c 0 := by
        have hz := hzero i
        rw [hfactor i] at hz
        have hsum : c 0 + g (a i) = 0 :=
          (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)
        linarith

      have hg_deriv (t : ℝ) : HasDerivAt g (dg t) t := by
        dsimp only [g, dg]
        apply HasDerivAt.fun_sum (u := Finset.univ)
        intro j hj
        simpa only [one_mul, mul_assoc] using
          (((hasDerivAt_id' t).mul_const (b' j)).exp.mul_const (c j.succ))

      have hrolle (i : Fin n) :
          ∃ z ∈ Ioo (a i.castSucc) (a i.succ), dg z = 0 := by
        apply exists_hasDerivAt_eq_zero
        · exact ha i.castSucc_lt_succ
        · intro x hx
          exact (hg_deriv x).continuousAt.continuousWithinAt
        · rw [hg_value, hg_value]
        · intro x hx
          exact hg_deriv x

      choose ξ hξmem hξzero using hrolle

      have hξ : StrictMono ξ := by
        intro i j hij
        calc
          ξ i < a i.succ := (hξmem i).2
          _ ≤ a j.castSucc := ha.monotone (Fin.succ_le_castSucc_iff.mpr hij)
          _ < ξ j := (hξmem j).1

      have hb' : StrictMono b' := by
        intro i j hij
        dsimp only [b']
        exact sub_lt_sub_right (hb (Fin.succ_lt_succ_iff.mpr hij)) _

      let d : Fin n → ℝ := fun j ↦ b' j * c j.succ
      have hdzero (i : Fin n) :
          ∑ j : Fin n, Real.exp (ξ i * b' j) * d j = 0 := by
        rw [← hξzero i]
        dsimp only [dg, d]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hd : d = 0 := ih ξ b' hξ hb' d hdzero

      have hc_tail (j : Fin n) : c j.succ = 0 := by
        have hdj := congrFun hd j
        have hbpos : 0 < b' j := by
          dsimp only [b']
          exact sub_pos.mpr (hb j.succ_pos)
        dsimp [d] at hdj
        exact (mul_eq_zero.mp hdj).resolve_left hbpos.ne'

      have hc_zero : c 0 = 0 := by
        have hz := hzero (0 : Fin (n + 1))
        rw [Fin.sum_univ_succ] at hz
        simp only [hc_tail, mul_zero, Finset.sum_const_zero, add_zero] at hz
        exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

      funext i
      exact Fin.cases hc_zero hc_tail i

/-- The matrix `(exp (a i * b j))` is nonsingular when both real sequences are strictly
increasing. -/
theorem det_exp_mul_ne_zero {n : ℕ} (a b : Fin n → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) :
    Matrix.det (fun i j : Fin n ↦ Real.exp (a i * b j)) ≠ 0 := by
  intro hdet
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ Real.exp (a i * b j)
  change M.det = 0 at hdet
  obtain ⟨c, hc, hMc⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := M)).2 hdet
  apply hc
  apply exp_sum_coeff_eq_zero n a b ha hb c
  intro i
  have hi := congrFun hMc i
  simpa [M, Matrix.mulVec, dotProduct] using hi

private theorem exists_sorted_equiv
    {I : Type*} [Fintype I] (a : I → ℝ) (ha : Function.Injective a) :
    ∃ e : Fin (Fintype.card I) ≃ I, StrictMono (a ∘ e) := by
  letI : LinearOrder I := LinearOrder.lift' a ha
  let e : Fin (Fintype.card I) ≃o I := monoEquivOfFin I rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have heij : e i < e j := e.strictMono hij
  change a (e i) < a (e j)
  exact heij

/-- The exponential kernel is nonsingular for any two injective finite real families. -/
theorem det_exp_mul_ne_zero_of_injective
    {I : Type*} [Fintype I] [DecidableEq I] (a b : I → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    Matrix.det (fun i j ↦ Real.exp (a i * b j)) ≠ 0 := by
  obtain ⟨ea, hea⟩ := exists_sorted_equiv a ha
  obtain ⟨eb, heb⟩ := exists_sorted_equiv b hb
  let M : Matrix I I ℝ := fun i j ↦ Real.exp (a i * b j)
  have hsorted : Matrix.det (M.submatrix ea eb) ≠ 0 := by
    change Matrix.det (fun i j ↦ Real.exp (a (ea i) * b (eb j))) ≠ 0
    exact det_exp_mul_ne_zero (a ∘ ea) (b ∘ eb) hea heb
  intro hzero
  apply hsorted
  apply abs_eq_zero.mp
  rw [Matrix.abs_det_submatrix_equiv_equiv, hzero, abs_zero]

end LeanProofs.IntegerExponent
