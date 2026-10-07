import OAI.Combinatorics.Progressions.Polynomial.PrependPolynomialVariable

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem coefficient_multiaffine_strided_bias {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N s : Fin n → ℕ) (M k : ℕ)
    (hs : ∀ i, 0 < s i) (hk : 0 < k) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ i, Fin (N i),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*∏ i, (s i : ℝ)) ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val-
        (m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
          (((k : ℝ)*M)*∏ i, ((s i : ℝ)*(N i : ℝ))) := by
  let A := prependPolynomialVariable P
  let L : Fin (n+1) → ℕ := Fin.cons M N
  let t : Fin (n+1) → ℕ := Fin.cons k s
  let v : Fin (n+1) → ℝ := Fin.cons w u
  have ht : ∀ i, 0 < t i := by
    intro i
    exact Fin.cases hk hs i
  have hL : ∀ i, multiaffineBiasBudget n ζ ≤ L i := by
    intro i
    exact Fin.cases hM hN i
  have heval (c : Fin M) (x : ∀ i, Fin (N i)) :
      MvPolynomial.eval (fun i => v i+(t i : ℝ)*
        (((Fin.cons c x : ∀ i, Fin (L i)) i).val : ℝ)) A =
      (w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P := by
    have he : (fun i => v i+(t i : ℝ)*
        (((Fin.cons c x : ∀ i, Fin (L i)) i).val : ℝ)) =
        Fin.cons (w+(k : ℝ)*(c.val : ℝ)) (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he]
    exact prependPolynomialVariable_eval P _ _
  have hb : ζ ≤ ‖𝔼 x : ∀ i, Fin (L i),
      character ((MvPolynomial.eval (fun i => v i+(t i : ℝ)*((x i).val : ℝ)) A : ℝ) :
        CircleFourier.Circle)‖ := by
    rw [expect_dependent_fin_cons]
    apply hbias.trans_eq
    congr 1
    apply Finset.expect_congr rfl
    intro c _
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg (fun r : ℝ => character (r : CircleFourier.Circle)) (heval c x).symm
  have h := fin_multiaffine_strided_bias A (prependPolynomialVariable_degree P hP)
    L t ht v hζ hL hb
  simpa only [A, prependPolynomialVariable_top, L, t, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem moderateBooleanBlock_selected_entry {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (N s : Fin n → Option α → ℕ) (M k : ℕ) (u : Fin n → Option α → ℝ) (w : ℝ)
    (ξ : Finset α → ℝ) (label : Fin n → Option α) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S)
    (hNpos : ∀ g r, 0 < N g r) (hs : ∀ g, 0 < s g (label g)) (hk : 0 < k)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g (label g))
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g r, Fin (N g r),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*∏ g, (s g (label g) : ℝ)) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        (((k : ℝ)*M)*∏ g, ((s g (label g) : ℝ)*(N g (label g) : ℝ))) := by
  let : ∀ g r, Nonempty (Fin (N g r)) := fun g r => ⟨⟨0,hNpos g r⟩⟩
  let F := fun x : ∀ g r, Fin (N g r) => 𝔼 c : Fin M,
    character (((w+(k : ℝ)*(c.val : ℝ))*
      booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
      CircleFourier.Circle)
  have hbias' : ζ ≤ ‖𝔼 x, F x‖ := by
    rw [Finset.expect_comm] at hbias
    exact hbias
  obtain ⟨b,hb⟩ := exists_frozen_group_bias label F hbias'
  let a := fun g r => u g r+(s g r : ℝ)*((b g r).val : ℝ)
  let P := frozenBooleanPhasePolynomial label a ξ
  have hphase (t : ∀ g, Fin (N g (label g))) : F (resampleGroupCoordinates label b t) =
      𝔼 c : Fin M, character (((w+(k : ℝ)*(c.val : ℝ))*
        MvPolynomial.eval (fun g => u g (label g)+(s g (label g) : ℝ)*((t g).val : ℝ)) P : ℝ) :
        CircleFourier.Circle) := by
    dsimp only [F,P]
    simp only [frozenBooleanPhasePolynomial_eval, a, progressionCoordinates_resample]
  simp_rw [hphase] at hb
  rw [Finset.expect_comm] at hb
  have h := coefficient_multiaffine_strided_bias P (frozenBooleanPhasePolynomial_degree label a ξ)
    (fun g => N g (label g)) (fun g => s g (label g)) M k hs hk
    (fun g => u g (label g)) w hζ hN hM hb
  simpa only [P, frozenBooleanPhasePolynomial_coefficient n label a ξ S hlabel] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_bounded_stride_entry {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (s : Fin (n+1) → Option α → ℕ)
    (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ) (S : Finset α)
    (hS : S.card ≤ n+1) (hs : ∀ g r, 0 < s g r) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * R^(n+1) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  obtain ⟨label,hlabel⟩ := exists_padded_boolean_labels S (n+1) hS
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ g, 0 < N g := fun g => by exact_mod_cast hQ.trans_le (hN g)
  obtain ⟨D,hD,hDQ,m,hm⟩ := booleanBlockPhase_strided_selected_entry (fun g _ => N g) s u ξ
    label S hlabel (fun g _ => hNp g) (fun g => hs g (label g)) hζ hN hbias
  refine ⟨D,hD,hDQ.trans ?_,m,hm.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hQ.le
    simpa only [Fintype.card_fin] using stride_product_le (fun g => s g (label g))
      (fun g => hR g (label g))
  · simpa only [one_mul] using stride_product_error_le N (fun g => s g (label g)) hNp
      (fun g => hs g (label g)) (by norm_num : (0 : ℝ) < 1) hQ.le

theorem moderateBooleanBlock_bounded_stride_entry {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin n → ℕ) (s : Fin n → Option α → ℕ) (M k : ℕ)
    (u : Fin n → Option α → ℝ) (w : ℝ) (ξ : Finset α → ℝ) (S : Finset α)
    (hS : S.card ≤ n) (hs : ∀ g r, 0 < s g r) (hk : 0 < k)
    {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g, Option α → Fin (N g),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ((k : ℝ)*R^n) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        (((k : ℝ)*M)*∏ g, (N g : ℝ)) := by
  obtain ⟨label,hlabel⟩ := exists_padded_boolean_labels S n hS
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ g, 0 < N g := fun g => by exact_mod_cast hQ.trans_le (hN g)
  have hMp : (0 : ℝ) < M := hQ.trans_le hM
  obtain ⟨D,hD,hDQ,m,hm⟩ := moderateBooleanBlock_selected_entry (fun g _ => N g) s M k u w ξ
    label S hlabel (fun g _ => hNp g) (fun g => hs g (label g)) hk hζ hN hM hbias
  refine ⟨D,hD,hDQ.trans ?_,m,hm.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hQ.le
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    simpa only [Fintype.card_fin] using stride_product_le (fun g => s g (label g))
      (fun g => hR g (label g))
  · apply stride_product_error_le N (fun g => s g (label g)) hNp
      (fun g => hs g (label g)) _ hQ.le
    exact mul_pos (by exact_mod_cast hk) hMp

end Erdos3

end

end OAI
