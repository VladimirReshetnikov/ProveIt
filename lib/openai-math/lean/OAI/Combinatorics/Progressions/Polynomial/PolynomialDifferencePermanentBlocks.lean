/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ModularMultilinearAffineCost

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

noncomputable def permanentPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.permanent (fun i j => X (i, j))

noncomputable def permanentExponent (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin n × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i, i) 1

theorem permanentExponent_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (j : Fin n × Fin n) :
    permanentExponent n σ j = if σ j.2 = j.1 then 1 else 0 := by
  rcases j with ⟨a, b⟩
  simp only [permanentExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq,
    and_comm, ite_and]
  simp

theorem permanentExponent_injective (n : ℕ) : Function.Injective (permanentExponent n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hh := congrArg (fun d => d (σ i, i)) h
  simp only [permanentExponent_apply, ite_true] at hh
  by_contra hi
  have hne : τ i ≠ σ i := Ne.symm hi
  simp [hne] at hh

theorem permanentPolynomial_eq_monomial_sum (n : ℕ) :
    permanentPolynomial n (R := R) = ∑ σ : Equiv.Perm (Fin n), monomial (permanentExponent n σ) 1 := by
  unfold permanentPolynomial Matrix.permanent permanentExponent
  apply Finset.sum_congr rfl
  intro σ _
  rw [monomial_sum_one]
  rfl

theorem permanentPolynomial_degreeOf (n : ℕ) (j : Fin n × Fin n) :
    degreeOf j (permanentPolynomial n (R := R)) ≤ 1 := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  rw [permanentPolynomial_eq_monomial_sum]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  rw [degreeOf_monomial_eq _ _ one_ne_zero, permanentExponent_apply]
  split_ifs <;> omega

theorem permanentPolynomial_totalDegree (n : ℕ) :
    (permanentPolynomial n (R := R)).totalDegree ≤ n := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  unfold permanentPolynomial Matrix.permanent
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_finsetProd _ _).trans
  simp [totalDegree_X]

theorem permanentPolynomial_coeff (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permanentPolynomial n (R := R)).coeff (permanentExponent n σ) = 1 := by
  rw [permanentPolynomial_eq_monomial_sum, coeff_sum]
  simp only [coeff_monomial, (permanentExponent_injective n).eq_iff]
  simp

theorem permanentExponent_one_eq_diagonal (n : ℕ) :
    permanentExponent n 1 = (fullShiftExponent n).mapDomain (fun i => (i, i)) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => Finsupp.single_zero _)]
  simp only [fullShiftExponent_apply, permanentExponent, Equiv.Perm.one_apply]

theorem permanentPolynomial_diagonal_coefficient (n : ℕ) :
    (permanentPolynomial n (R := R)).coeff
      ((fullShiftExponent n).mapDomain (fun i => (i, i))) = 1 := by
  rw [← permanentExponent_one_eq_diagonal]
  exact permanentPolynomial_coeff n 1

theorem eval_permanentPolynomial (n : ℕ) (x : Fin n × Fin n → R) :
    eval x (permanentPolynomial n) = Matrix.permanent (fun i j => x (i, j)) := by
  simp only [permanentPolynomial, Matrix.permanent, map_sum, map_prod, eval_X]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem permanent_gcd_mean_sublevel {n p a : ℕ} [NeZero p]
    (hn : 0 < n) (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  have h := modularMultilinear_gcd_mean_sublevel hn hp ha
    (permanentPolynomial n) (fun i => (i, i))
    (fun _ _ h => congrArg Prod.fst h)
    (permanentPolynomial_totalDegree n) (permanentPolynomial_degreeOf n)
    (by rw [permanentPolynomial_diagonal_coefficient]; exact isUnit_one)
  simpa only [eval_permanentPolynomial] using h

theorem permanent_zero_gcd_mean {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin 0 × Fin 0) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) =
        1 / (p ^ a : ℕ) := by
  have hm : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
  have hval : (1 : ZMod (p ^ a)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt hm
  have hperm (x : (Fin 0 × Fin 0) → ZMod (p ^ a)) :
      Matrix.permanent (fun i j => x (i, j)) = 1 := Matrix.permanent_isEmpty
  simp only [hperm, hval, Nat.gcd_one_left, Nat.cast_one,
    Fintype.expect_const]

theorem permanent_gcd_mean_sublevel_all {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  cases n with
  | zero =>
    rw [permanent_zero_gcd_mean hp ha]
    simp only [Nat.zero_add, Nat.cast_one, pow_zero, div_one, one_mul]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Nat.cast_pow, one_div]
  | succ n => exact permanent_gcd_mean_sublevel (Nat.succ_pos _) hp ha

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem disjoint_permanent_gcd_mean_bound {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hn : 0 < n) (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  rw [uniform_expect_prod_disjoint_permanents n J v hv hdisjoint
    (fun _ (z : ZMod (p ^ a)) => (z.val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)),
    ← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · intro b hb
    exact Finset.expect_nonneg (fun x _ => by positivity)
  · intro b hb
    exact permanent_gcd_mean_sublevel hn hp ha

theorem disjoint_permanent_gcd_mean_bound_curried {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hn : 0 < n) (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  have he : (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) =
      (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) := by
    apply Fintype.expect_equiv (Equiv.curry (Fin n) I (ZMod (p ^ a))).symm
    intro x
    rfl
  rw [he]
  exact disjoint_permanent_gcd_mean_bound hn hp ha J v hv hdisjoint

theorem disjoint_permanent_gcd_mean_bound_all {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  rw [uniform_expect_prod_disjoint_permanents n J v hv hdisjoint
    (fun _ (z : ZMod (p ^ a)) => (z.val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)),
    ← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · intro b hb
    exact Finset.expect_nonneg (fun x _ => by positivity)
  · intro b hb
    exact permanent_gcd_mean_sublevel_all hp ha

theorem disjoint_permanent_gcd_mean_bound_curried_all {I A : Type*}
    [Fintype I] [DecidableEq I] {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ b ∈ J, Function.Injective (v b))
    (hdisjoint : (J : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c)))) :
    (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ J.card := by
  have he : (𝔼 u : Fin n → I → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => u i (v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) =
      (𝔼 x : (Fin n × I) → ZMod (p ^ a),
      ∏ b ∈ J, ((Matrix.permanent (fun i j => x (i, v b j))).val.gcd (p ^ a) : ℝ) /
        (p ^ a : ℕ)) := by
    apply Fintype.expect_equiv (Equiv.curry (Fin n) I (ZMod (p ^ a))).symm
    intro x
    rfl
  rw [he]
  exact disjoint_permanent_gcd_mean_bound_all hp ha J v hv hdisjoint

end Erdos3

end

end OAI
