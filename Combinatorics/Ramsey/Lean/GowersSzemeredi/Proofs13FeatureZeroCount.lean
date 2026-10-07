import GowersSzemeredi.Proofs13FeaturePolynomial
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! Quantitative exceptional-set control for individual unintended
feature relations, obtained from the quadratic Schwartz-Zippel bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open MvPolynomial

private theorem feature_countWhere_sum {T : Type*} [Fintype T] (P : T → Prop) :
    countWhere P = ∑ t : T, @ite Nat (P t) (Classical.propDecidable _) 1 0 := by
  classical
  simp [countWhere]

private theorem feature_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) :
    countWhere P = countWhere (fun x => P (e x)) := by
  classical
  simp_rw [feature_countWhere_sum]
  exact (e.sum_comp (fun y => if P y then 1 else 0)).symm

theorem polynomial_zero_count_fin {R : Type*} [Field R] [Fintype R]
    {n : Nat} (p : MvPolynomial (Fin (n + 1)) R) (hp : p ≠ 0) :
    countWhere (fun x => eval x p = 0) ≤ p.totalDegree * Fintype.card R ^ n := by
  classical
  have h := schwartz_zippel_totalDegree hp (Finset.univ : Finset R)
  have hpi : (Fintype.piFinset fun _ : Fin (n + 1) => (Finset.univ : Finset R)) =
      Finset.univ := by ext x; simp
  rw [hpi, Finset.card_univ] at h
  change (countWhere (fun x => eval x p = 0) : ℚ≥0) / (Fintype.card R : ℚ≥0) ^ (n + 1) ≤
    (p.totalDegree : ℚ≥0) / Fintype.card R at h
  have hq : (0 : ℚ≥0) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h' := (div_le_iff₀ (pow_pos hq _)).mp h
  have hr : (p.totalDegree : ℚ≥0) / Fintype.card R * (Fintype.card R : ℚ≥0) ^ (n + 1) =
      (p.totalDegree : ℚ≥0) * (Fintype.card R : ℚ≥0) ^ n := by
    rw [pow_succ]
    field_simp
  rw [hr] at h'
  exact_mod_cast h'

theorem polynomial_zero_count {V R : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Field R] [Fintype R] (p : MvPolynomial V R) (hp : p ≠ 0) :
    countWhere (fun x => eval x p = 0) ≤
      p.totalDegree * Fintype.card R ^ (Fintype.card V - 1) := by
  classical
  let n := Fintype.card V - 1
  have hn : Fintype.card V = n + 1 := by
    have hv : 0 < Fintype.card V := Fintype.card_pos
    omega
  let e : V ≃ Fin (n + 1) := (Fintype.equivFin V).trans (finCongr hn)
  let q := rename e p
  have hq : q ≠ 0 := by
    exact fun h => hp ((rename_eq_zero_iff_of_injective p e.injective).mp h)
  have h := polynomial_zero_count_fin q hq
  have hc : countWhere (fun x => eval x p = 0) = countWhere (fun x => eval x q = 0) := by
    rw [feature_countWhere_equiv (e.symm.arrowCongr (Equiv.refl R))]
    congr 1
    funext x
    simp only [q, eval_rename]
    rfl
  rw [hc]
  exact h.trans (Nat.mul_le_mul_right _ (totalDegree_rename_le e p))

theorem balancedFeaturePolynomial_zero_count {I R : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R] [Fintype R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option I → R)
    (hnot : ¬ ∃ c : R, u₀ none = c ∧ u₁ none = -c ∧
      (∀ i, u₀ (some i) = -(sign i * c)) ∧
      (∀ i, u₁ (some i) = sign i * c)) :
    countWhere (fun z => eval z (balancedFeaturePolynomial sign u₀ u₁) = 0) ≤
      2 * Fintype.card R ^ (2 * Fintype.card I + 1) := by
  have hp := balancedFeaturePolynomial_ne_zero sign hsign u₀ u₁ hnot
  have h := polynomial_zero_count (balancedFeaturePolynomial sign u₀ u₁) hp
  rw [balancedFeatureVariable_card] at h
  have hn : 2 * Fintype.card I + 2 - 1 = 2 * Fintype.card I + 1 := by omega
  rw [hn] at h
  exact h.trans (Nat.mul_le_mul_right _ (balancedFeaturePolynomial_totalDegree sign u₀ u₁))

theorem balancedFeaturePolynomial_exceptional_count {I R E : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R] [Fintype R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0)
    (S : Finset E) (u₀ u₁ : E → Option I → R)
    (hnot : ∀ e ∈ S, ¬ ∃ c : R, u₀ e none = c ∧ u₁ e none = -c ∧
      (∀ i, u₀ e (some i) = -(sign i * c)) ∧
      (∀ i, u₁ e (some i) = sign i * c)) :
    countWhere (fun z => ∃ e ∈ S, eval z (balancedFeaturePolynomial sign (u₀ e) (u₁ e)) = 0) ≤
      S.card * (2 * Fintype.card R ^ (2 * Fintype.card I + 1)) := by
  classical
  let Z (e : E) := Finset.univ.filter
    (fun z => eval z (balancedFeaturePolynomial sign (u₀ e) (u₁ e)) = 0)
  have heq : countWhere (fun z => ∃ e ∈ S,
      eval z (balancedFeaturePolynomial sign (u₀ e) (u₁ e)) = 0) = (S.biUnion Z).card := by
    unfold countWhere
    congr 1
    ext z
    simp [Z]
  rw [heq]
  calc
    (S.biUnion Z).card ≤ ∑ e ∈ S, (Z e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ S, 2 * Fintype.card R ^ (2 * Fintype.card I + 1) := by
      apply Finset.sum_le_sum
      intro e he
      exact balancedFeaturePolynomial_zero_count sign hsign (u₀ e) (u₁ e) (hnot e he)
    _ = _ := by simp

theorem balancedFeaturePolynomial_zero_count_32 {N : Nat} [NeZero N] [Fact N.Prime]
    (sign : Fin 15 → ZMod N) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option (Fin 15) → ZMod N)
    (hnot : ¬ ∃ c : ZMod N, u₀ none = c ∧ u₁ none = -c ∧
      (∀ i, u₀ (some i) = -(sign i * c)) ∧
      (∀ i, u₁ (some i) = sign i * c)) :
    countWhere (fun z => MvPolynomial.eval z (balancedFeaturePolynomial sign u₀ u₁) = 0) ≤
      2 * N ^ 31 := by
  simpa using balancedFeaturePolynomial_zero_count sign hsign u₀ u₁ hnot

end LeanProofs.GowersSzemeredi
