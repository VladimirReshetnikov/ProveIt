import GowersSzemeredi.Proofs16BalancedFieldWord
import GowersSzemeredi.Proofs16BalancedWordObstruction

/-! At each fixed dimension, balanced finite-alphabet words yield genuine
failures of the unit-parameter multiple-linearity conclusion at all
sufficiently large prime moduli. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

theorem exists_non_multiplyLinear_finite_word (k : Nat) :
    ∃ R N₀ : Nat, 0 < R ∧ (R : Real) ≤ 8 * multipleQ (1 / 2) 1 (k + 1) ∧
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∃ S : Finset (ZMod N), ∃ f : ZMod N → ZMod N,
        S.card = R ∧ (∀ y, f y ∈ S) ∧
        ¬ MultiplyLinearFunction 1 1 Finset.univ (fun x : Point N (k + 1) => f (section16Last x)) := by
  let delta : Real := multipleC (1 / 2) 1 (k + 1)
  have hδ : 0 < delta := by unfold delta multipleC; positivity
  have hδone : delta ≤ 1 := by
    unfold delta multipleC
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hQ : 0 < multipleQ (1 / 2) 1 (k + 1) := inv_pos.mpr hδ
  let K : Nat := Nat.ceil (multipleQ (1 / 2) 1 (k + 1))
  have hK : multipleQ (1 / 2) 1 (k + 1) ≤ (K : Real) := Nat.le_ceil _
  have hKupper : (K : Real) < multipleQ (1 / 2) 1 (k + 1) + 1 := Nat.ceil_lt_add_one hQ.le
  have hQone : 1 ≤ multipleQ (1 / 2) 1 (k + 1) := (one_le_inv₀ hδ).mpr hδone
  have hKreal : (0 : Real) < K := hQ.trans_le hK
  have hKnat : 0 < K := by exact_mod_cast hKreal
  let R : Nat := 4 * K
  let epsilon : Real := 1 / (32 * (K : Real))
  let beta : Real := 1 / (R : Real) + epsilon
  have hR : 0 < R := Nat.mul_pos (by norm_num) hKnat
  have hε : 0 < epsilon := by dsimp [epsilon]; positivity
  have hβ : 0 ≤ beta := by dsimp [beta]; positivity
  have hsmall : (K : Real) * beta ≤ 9 / 32 := by
    dsimp [beta, epsilon, R]
    push_cast
    apply le_of_eq
    field_simp
    <;> ring
  obtain ⟨N₀, hN₀⟩ := exists_balanced_field_word_large_N R hR hδ hδone hε
  have hscale : Tendsto (fun N : Nat => (N : Real) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hwidth : ∀ᶠ N : Nat in atTop, (32 : Real) * K * R ≤ (N : Real) ^ delta :=
    hscale.eventually (eventually_ge_atTop _)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hwidth
  have hRbound : (R : Real) ≤ 8 * multipleQ (1 / 2) 1 (k + 1) := by
    dsimp [R]
    push_cast
    linarith only [hKupper, hQone]
  refine ⟨R, max N₀ N₁, hR, hRbound, fun N _ _ hN => ?_⟩
  obtain ⟨S, f, hS, hf, hbal⟩ := hN₀ N ((le_max_left _ _).trans hN)
  refine ⟨S, f, hS, hf, ?_⟩
  apply balanced_word_not_multiplyLinear S f hf (K : Real) ((N : Real) ^ delta) beta hβ hK le_rfl hbal hsmall
  rw [hS]
  have ht := hN₁ N ((le_max_right _ _).trans hN)
  linarith only [ht]

end LeanProofs.GowersSzemeredi
