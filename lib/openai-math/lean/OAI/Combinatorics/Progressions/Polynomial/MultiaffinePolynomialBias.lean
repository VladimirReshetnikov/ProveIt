import OAI.Combinatorics.Progressions.Estimates.MultiaffineBias
import OAI.Combinatorics.Progressions.Estimates.MultiaffineOptionExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_real_phase_double_mean_le_one {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X → Y → ℝ) :
    ‖𝔼 x, 𝔼 y, character (F x y : CircleFourier.Circle)‖ ≤ 1 := by
  calc
    _ ≤ 𝔼 x, ‖𝔼 y, character (F x y : CircleFourier.Circle)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 𝔼 x, 𝔼 y, ‖character (F x y : CircleFourier.Circle)‖ :=
      Finset.expect_le_expect (fun x _ => RCLike.norm_expect_le (K := ℂ))
    _ = 1 := by simp

theorem multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin n → ℕ) (M : ℕ)
    (u : Fin n → ℝ) (w : ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : (∀ i, Fin (N i)), 𝔼 t : Fin M,
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hMp⟩⟩
  have hζ1 : ζ ≤ 1 := hbias.trans (norm_real_phase_double_mean_le_one _)
  let a := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)
  let b := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)
  have hphase (x : ∀ i, Fin (N i)) (t : Fin M) :
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle) = multiaffineIntervalPhase a b u w x t := by
    rw [multiaffineOption_eval P hP]
    rfl
  simp_rw [hphase] at hbias
  have h := multiaffine_bias_approximation N M a b u w hζ hζ1 hN hM hbias
  simpa only [a, optionSquarefree_full_exponent] using h

end Erdos3

end

end OAI
