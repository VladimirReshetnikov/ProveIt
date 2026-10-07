import GowersSzemeredi.Proofs16UniformAlphabet

/-! A uniform word can balance every symbol on every set in a finite
family whenever the explicit exponential union-bound budget is below one. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace LeanProofs.GowersSzemeredi

theorem exists_balanced_alphabet_word {I J C : Type*} [Fintype I] [Fintype J] [Fintype C]
    [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (T : J → Finset I) (L epsilon : Real) (hε : 0 ≤ epsilon)
    (hL : ∀ j, L ≤ ((T j).card : Real))
    (hbudget : (Fintype.card J : Real) * Fintype.card C * Real.exp (-2 * epsilon ^ 2 * L) < 1) :
    ∃ w : I → C, ∀ j c, (((T j).filter (fun i => w i = c)).card : Real) ≤
      (1 / (Fintype.card C : Real) + epsilon) * (T j).card := by
  classical
  let bad (p : J × C) : Set (I → C) := {w |
    (1 / (Fintype.card C : Real) + epsilon) * (T p.1).card ≤
      (((T p.1).filter (fun i => w i = p.2)).card : Real)}
  have hb (p : J × C) : (alphabetWordMeasure I C).real (bad p) ≤ Real.exp (-2 * epsilon ^ 2 * L) := by
    have ht := alphabetWordMeasure_symbol_concentration (T p.1) p.2 epsilon hε
    have hn : -2 * epsilon ^ 2 ≤ 0 := by nlinarith only [sq_nonneg epsilon]
    exact ht.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hL p.1) hn))
  have hu : (alphabetWordMeasure I C).real (⋃ p, bad p) ≤
      (Fintype.card J : Real) * Fintype.card C * Real.exp (-2 * epsilon ^ 2 * L) := by
    calc
      _ ≤ ∑ p : J × C, (alphabetWordMeasure I C).real (bad p) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : J × C, Real.exp (-2 * epsilon ^ 2 * L) := Finset.sum_le_sum (fun p _ => hb p)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  by_contra hnone
  push_neg at hnone
  have hall : (⋃ p, bad p) = Set.univ := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, c, hc⟩ := hnone w
    exact ⟨(j, c), hc.le⟩
  rw [hall] at hu
  have hlt := hu.trans_lt hbudget
  simpa using hlt

end LeanProofs.GowersSzemeredi
