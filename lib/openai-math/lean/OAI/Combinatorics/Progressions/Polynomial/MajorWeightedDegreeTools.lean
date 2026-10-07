/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Logic.Function.Basic
import OAI.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
import OAI.Combinatorics.Progressions.Geometry.TopSupportSubstitution

namespace OAI


namespace Erdos3

open MvPolynomial

variable {σ τ ι R : Type*} [CommRing R]

theorem polynomialHom_preserves_weightedDegree (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p ∈ weightedSupportLE w n := by
  rw [MvPolynomial.aeval_unique F]
  exact weightedSupportLE_aeval v w _ hF hp

noncomputable def coordinateShearHom (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) :
    MvPolynomial τ R →ₐ[R] MvPolynomial τ R := by
  classical
  exact aeval (Function.update X i (X i + rename f Q))

theorem coordinateShearHom_X [DecidableEq τ] (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) (j : τ) :
    coordinateShearHom i f Q (X j) =
      Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q) j := by
  classical
  by_cases h : j = i
  · subst j
    simp only [coordinateShearHom, MvPolynomial.aeval_X, Function.update_self]
  · simp [coordinateShearHom, Function.update, h]

theorem coordinateShearHom_rename (i : τ) (f : σ → τ) (Q : MvPolynomial σ R)
    (g : ι → τ) (hg : ∀ j, g j ≠ i) (P : MvPolynomial ι R) :
    coordinateShearHom i f Q (rename g P) = rename g P := by
  classical
  rw [coordinateShearHom, MvPolynomial.aeval_rename]
  have he : (Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q)) ∘ g = X ∘ g := by
    funext j
    exact Function.update_of_ne (hg j) _ _
  rw [he, ← MvPolynomial.rename_eq_aeval]

theorem coordinateShearHom_comp_neg (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) :
    (coordinateShearHom i f Q).comp (coordinateShearHom i f (-Q)) = AlgHom.id R _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  change coordinateShearHom i f Q (coordinateShearHom i f (-Q) (X j)) = X j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self, map_add, coordinateShearHom_X, Function.update_self,
      coordinateShearHom_rename i f Q f hf, map_neg]
    exact add_neg_cancel_right (X i) (rename f Q)
  · rw [Function.update_of_ne h, coordinateShearHom_X, Function.update_of_ne h]

noncomputable def coordinateShearEquiv (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) : MvPolynomial τ R ≃ₐ[R] MvPolynomial τ R :=
  AlgEquiv.ofAlgHom (coordinateShearHom i f Q) (coordinateShearHom i f (-Q))
    (coordinateShearHom_comp_neg i f hf Q)
    (by simpa only [neg_neg] using coordinateShearHom_comp_neg i f hf (-Q))

theorem coordinateShearEquiv_apply (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) (P : MvPolynomial τ R) :
    coordinateShearEquiv i f hf Q P = coordinateShearHom i f Q P := rfl

theorem coordinateShearEquiv_symm_apply (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) (P : MvPolynomial τ R) :
    (coordinateShearEquiv i f hf Q).symm P = coordinateShearHom i f (-Q) P := rfl

theorem coordinateShearHom_degree (w : τ → ℕ) (i : τ) (f : σ → τ)
    (Q : MvPolynomial σ R) (hQ : rename f Q ∈ weightedSupportLE w (w i))
    {P : MvPolynomial τ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    coordinateShearHom i f Q P ∈ weightedSupportLE w n := by
  classical
  apply polynomialHom_preserves_weightedDegree w w _ _ hP
  intro j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self]
    exact (weightedSupportLE w (w i)).add_mem (weightedSupportLE_X w i) hQ
  · rw [Function.update_of_ne h]
    exact weightedSupportLE_X w j

end Erdos3


namespace Erdos3

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

theorem earlierSlot_ne_self (i : Fin d) (j : Fin i.val) : earlierSlot i j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  change j.val = i.val at hv
  omega

theorem exists_triangularPolynomialEquiv_prefix (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_⟩
      · intro i
        rw [ite_eq_right (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [ite_eq_right (by change ¬ n < n; omega),
            ite_eq_left (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [ite_eq_left hi, ite_eq_left (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [ite_eq_right hi, ite_eq_right (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)

theorem exists_triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = X i + rename (earlierSlot i) (Q i)) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  obtain ⟨E, hE, hd, hi⟩ := exists_triangularPolynomialEquiv_prefix w Q hQ d le_rfl
  refine ⟨E, ?_, hd, hi⟩
  intro i
  simpa only [ite_eq_left i.isLt] using hE i

noncomputable def triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R :=
  Classical.choose (exists_triangularPolynomialEquiv w Q hQ)

theorem triangularPolynomialEquiv_X (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (i : Fin d) :
    triangularPolynomialEquiv w Q hQ (X i) = X i + rename (earlierSlot i) (Q i) :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).1 i

theorem triangularPolynomialEquiv_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    triangularPolynomialEquiv w Q hQ p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.1 m p hp

theorem triangularPolynomialEquiv_inverse_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    (triangularPolynomialEquiv w Q hQ).symm p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.2 m p hp

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_lt_succ {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLT w (d + 1) :=
  fun _ ha => Nat.lt_succ_iff.mpr (hp ha)

theorem weightedSupportLT_map (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLT v n) :
    F p ∈ weightedSupportLT w n := by
  cases n with
  | zero =>
      rw [weightedSupportLT_zero_eq hp, map_zero]
      exact Submodule.zero_mem _
  | succ n =>
      exact weightedSupportLE_lt_succ (polynomialHom_preserves_weightedDegree v w F hF
        (weightedSupportLT_succ_le hp))

theorem weightedComparison_mul (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hGp : G p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - G p ∈ weightedSupportLT w d)
    (hdq : F q - G q ∈ weightedSupportLT w e) :
    F (p * q) - G (p * q) ∈ weightedSupportLT w (d + e) := by
  rw [map_mul, map_mul,
    show F p * F q - G p * G q = (F p - G p) * F q + G p * (F q - G q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hGp hdq)

theorem weightedComparison_monomial_one (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - G (monomial a 1) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - G (monomial (Finsupp.single i n) 1) ∈
        weightedSupportLT w (n * v i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - G 1 ∈ _
        rw [map_one, map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
          (X i) (n * v i) (v i) (polynomialHom_preserves_weightedDegree v w G hG hp)
          (hF i) ih (hD i)
        simpa only [X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - G 1 ∈ weightedSupportLT w 0
      rw [map_one, map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial v a (1 : R)
      have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight v (Finsupp.single i n)) (Finsupp.weight v a)
        (polynomialHom_preserves_weightedDegree v w G hG hp)
        (polynomialHom_preserves_weightedDegree v w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [monomial_mul_monomial, one_mul, map_add] using hh

theorem weightedComparison_monomial (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - G (monomial a r) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  have hFc : F (C r) = C r := F.commutes r
  have hGc : G (C r) = C r := G.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [monomial_mul_monomial, zero_add, mul_one]
  rw [← hm, map_mul, map_mul, hFc, hGc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedComparison_monomial_one v w F G hF hG hD a)

theorem weightedComparison_difference (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p - G p ∈ weightedSupportLT w n := by
  classical
  change (F.toLinearMap - G.toLinearMap : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) p ∈
    weightedSupportLT w n
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w n).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha)
    (weightedComparison_monomial v w F G hF hG hD a (p.coeff a))

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem totalDegree_le_of_positive_weightedSupport (w : σ → ℕ) (hw : ∀ i, 1 ≤ w i)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) : P.totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff P n).mp
  intro α hα
  have hweight : Finsupp.weight (1 : σ → ℕ) α ≤ Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Pi.one_apply]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (α i) (hw i))
  exact hweight.trans (hP hα)

theorem coordinateShearHom_mass (i : τ) (f : σ → τ) (Q : MvPolynomial σ ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass (coordinateShearHom i f Q P) ≤ realPolynomialMass P * (1 + M) ^ n := by
  classical
  apply realPolynomialMass_substitution_le P _ (by linarith) _ hP
  intro j
  by_cases hj : j = i
  · subst j
    rw [Function.update_self]
    exact (realPolynomialMass_add_le _ _).trans (by simpa only [realPolynomialMass_X] using add_le_add (le_refl (1 : ℝ)) hQ)
  · rw [Function.update_of_ne hj, realPolynomialMass_X]
    linarith

theorem coordinateShearEquiv_inverse_mass (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass ((coordinateShearEquiv i f hf Q).symm P) ≤
      realPolynomialMass P * (1 + M) ^ n := by
  exact coordinateShearHom_mass i f (-Q) hM (by simpa only [map_neg, realPolynomialMass_neg] using hQ) hP

end Erdos3


namespace Erdos3

open MvPolynomial

variable {d : ℕ}

theorem exists_triangularPolynomialEquiv_prefix_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m →
        realPolynomialMass (E.symm p) ≤ realPolynomialMass p * (1 + M) ^ (m * n)) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [ite_eq_right (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
      · intro m p hp
        change realPolynomialMass p ≤ realPolynomialMass p * (1 + M) ^ (m * 0)
        simp only [Nat.mul_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv, hEmass⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [ite_eq_right (by change ¬ n < n; omega),
            ite_eq_left (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [ite_eq_left hi, ite_eq_left (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [ite_eq_right hi, ite_eq_right (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
      · intro m p hp
        have hHp : H.symm p ∈ weightedSupportLE w m := by
          change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
          apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
          simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
        have hHm : realPolynomialMass (H.symm p) ≤ realPolynomialMass p * (1 + M) ^ m :=
          coordinateShearEquiv_inverse_mass k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
            hM (hQM k) (totalDegree_le_of_positive_weightedSupport w hw hp)
        change realPolynomialMass (E.symm (H.symm p)) ≤ realPolynomialMass p * (1 + M) ^ (m * (n + 1))
        calc
          _ ≤ realPolynomialMass (H.symm p) * (1 + M) ^ (m * n) := hEmass m (H.symm p) hHp
          _ ≤ (realPolynomialMass p * (1 + M) ^ m) * (1 + M) ^ (m * n) :=
            mul_le_mul_of_nonneg_right hHm (pow_nonneg (by linarith) _)
          _ = realPolynomialMass p * (1 + M) ^ (m * (n + 1)) := by
            rw [mul_assoc, ← pow_add, show m + m * n = m * (n + 1) by ring]

theorem triangularPolynomialEquiv_inverse_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass ((triangularPolynomialEquiv w Q hQ).symm P) ≤
      realPolynomialMass P * (1 + M) ^ (n * d) := by
  obtain ⟨E, hE, _, _, hmass⟩ :=
    exists_triangularPolynomialEquiv_prefix_mass w hw Q hQ hM hQM d le_rfl
  have he : E.toAlgHom = (triangularPolynomialEquiv w Q hQ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change E (X i) = triangularPolynomialEquiv w Q hQ (X i)
    rw [hE, triangularPolynomialEquiv_X, ite_eq_left i.isLt]
  have heq : E = triangularPolynomialEquiv w Q hQ :=
    AlgEquiv.ext (fun P => DFunLike.congr_fun he P)
  rw [← heq]
  exact hmass n P hP

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem weightedSupportLE_totalDegree_le_of_pos {w : σ → ℕ}
    (hw : ∀ i, 0 < w i) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P ∈ weightedSupportLE w d) : P.totalDegree ≤ d := by
  exact totalDegree_le_of_positive_weightedSupport w hw hP

theorem weightedSupportLE_of_map_injective (φ : R →+* S)
    (hφ : Function.Injective φ) {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : map φ P ∈ weightedSupportLE w d) :
    P ∈ weightedSupportLE w d := by
  intro α hα
  apply hP
  change α ∈ (map φ P).support
  change α ∈ P.support at hα
  rwa [support_map_of_injective P hφ]

theorem weightedSupportLE_map_iff_of_injective (w : σ → ℕ) (φ : R →+* S)
    (hφ : Function.Injective φ) (P : MvPolynomial σ R) (d : ℕ) :
    map φ P ∈ weightedSupportLE w d ↔ P ∈ weightedSupportLE w d := by
  constructor
  · exact weightedSupportLE_of_map_injective φ hφ
  · intro hP α hα
    exact hP (support_map_subset φ P hα)

end Erdos3

end OAI
