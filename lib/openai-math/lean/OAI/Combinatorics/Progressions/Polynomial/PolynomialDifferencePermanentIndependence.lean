/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.PDeriv
import OAI.Combinatorics.Progressions.Estimates.IndependentProductMeans
import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentCombinatorics

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

theorem polynomialIterDifference_zero (n : ℕ) (u : Fin n → I → R) :
    polynomialIterDifference n (0 : MvPolynomial I R) u = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [polynomialIterDifference, map_zero] using ih (Fin.tail u)

theorem polynomialIterDifference_sum {A : Type*} (n : ℕ) (S : Finset A)
    (P : A → MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (∑ a ∈ S, P a) u =
      ∑ a ∈ S, polynomialIterDifference n (P a) u := by
  induction S using Finset.induction_on with
  | empty => simp [polynomialIterDifference_zero]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, polynomialIterDifference_add, ih]

theorem polynomialIterDifference_sub (n : ℕ) (P Q : MvPolynomial I R)
    (u : Fin n → I → R) :
    polynomialIterDifference n (P - Q) u =
      polynomialIterDifference n P u - polynomialIterDifference n Q u := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih => simp only [polynomialIterDifference, map_sub, ih]

theorem polynomialIterDifference_eq_zero_of_totalDegree_lt (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree < n) (u : Fin n → I → R) :
    polynomialIterDifference n P u = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [polynomialIterDifference, polynomialIterDifference_commute]
    have hd := polynomialIterDifference_degree n 0 P (by omega) (Fin.tail u)
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hd)
    rw [he, polynomialDifference_C]

theorem pderiv_polynomialTranslate (i : I) (u : I → R) (P : MvPolynomial I R) :
    pderiv i (polynomialTranslate u P) = polynomialTranslate u (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    by_cases h : j = i
    · subst j
      simp only [map_mul, polynomialTranslate_X, pderiv_mul, map_add, pderiv_X_self,
        pderiv_C, add_zero, mul_one, hP]
    · simp only [map_mul, polynomialTranslate_X, pderiv_mul, map_add,
        pderiv_X_of_ne h, pderiv_C, add_zero, mul_zero, hP]

theorem pderiv_polynomialIterDifference (i : I) (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) :
    pderiv i (polynomialIterDifference n P u) =
      polynomialIterDifference n (pderiv i P) u := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [polynomialIterDifference, ih]
    congr 1
    simp only [polynomialDifference_apply, map_sub, pderiv_polynomialTranslate]

theorem polynomialIterDifference_linearCoeff (i : I) (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) :
    (polynomialIterDifference n P u).coeff (Finsupp.single i 1) =
      (polynomialIterDifference n (pderiv i P) u).coeff 0 := by
  rw [← pderiv_polynomialIterDifference, coeff_pderiv]
  simp

theorem pderiv_prod_X_of_notMem (S : Finset I) (i : I) (hi : i ∉ S) :
    pderiv i (∏ j ∈ S, X j : MvPolynomial I R) = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    simp only [Finset.mem_insert, not_or] at hi
    simp only [Finset.prod_insert hj, pderiv_mul, pderiv_X_of_ne (Ne.symm hi.1),
      ih hi.2, mul_zero, zero_mul, add_zero]

theorem pderiv_prod_X_of_mem (S : Finset I) (i : I) (hi : i ∈ S) :
    pderiv i (∏ j ∈ S, X j : MvPolynomial I R) = ∏ j ∈ S.erase i, X j := by
  rw [← Finset.mul_prod_erase S (fun j => (X j : MvPolynomial I R)) hi,
    pderiv_mul, pderiv_X_self, one_mul,
    pderiv_prod_X_of_notMem _ _ (Finset.notMem_erase _ _), mul_zero, add_zero]

theorem polynomialIterDifference_prod_X_linearCoeff_zero (S : Finset I) (i : I)
    (hi : i ∉ S) (n : ℕ) (u : Fin n → I → R) :
    (polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u).coeff
      (Finsupp.single i 1) = 0 := by
  rw [polynomialIterDifference_linearCoeff, pderiv_prod_X_of_notMem S i hi,
    polynomialIterDifference_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem totalDegree_prod_X_le (S : Finset I) :
    (∏ j ∈ S, X j : MvPolynomial I R).totalDegree ≤ S.card := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have he : (∏ j ∈ S, X j : MvPolynomial I R) = 0 := Subsingleton.elim _ _
    simp [he]
  | inr h =>
    exact (totalDegree_finsetProd S (fun j => (X j : MvPolynomial I R))).trans
      (by simp)

theorem polynomialDifference_prod_X (S : Finset I) (v : I → R) :
    polynomialDifference v (∏ j ∈ S, X j : MvPolynomial I R) =
      ∑ T ∈ S.powerset.erase ∅, (∏ j ∈ T, v j) •
        (∏ j ∈ S \ T, X j : MvPolynomial I R) := by
  rw [polynomialDifference_apply, map_prod]
  simp only [polynomialTranslate_X]
  have h := Finset.prod_add (fun j => (C (v j) : MvPolynomial I R)) X S
  simp only [← map_prod, ← smul_eq_C_mul] at h
  conv_lhs => arg 1; rw [show (∏ j ∈ S, (X j + C (v j))) =
    ∏ j ∈ S, (C (v j) + X j) by apply Finset.prod_congr rfl; intros; rw [add_comm]]
  rw [h, ← Finset.sum_erase_add _ _ (Finset.mem_powerset.mpr (Finset.empty_subset S))]
  simp

theorem polynomialIterDifference_prod_X_step (n : ℕ) (S : Finset I)
    (hS : S.card = n + 1) (v : I → R) (u : Fin n → I → R) :
    polynomialIterDifference n (polynomialDifference v (∏ j ∈ S, X j : MvPolynomial I R)) u =
      ∑ j ∈ S, v j • polynomialIterDifference n (∏ l ∈ S.erase j, X l) u := by
  rw [polynomialDifference_prod_X, polynomialIterDifference_sum]
  have hsub : S.image (fun j => ({j} : Finset I)) ⊆ S.powerset.erase ∅ := by
    intro T hT
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hT
    simp [hj]
  have hz : ∀ T ∈ S.powerset.erase ∅, T ∉ S.image (fun j => ({j} : Finset I)) →
      polynomialIterDifference n ((∏ j ∈ T, v j) • (∏ j ∈ S \ T, X j)) u = 0 := by
    intro T hT hn
    obtain ⟨hne, hTS⟩ := Finset.mem_erase.mp hT
    have hTS := Finset.mem_powerset.mp hTS
    have hcard : 2 ≤ T.card := by
      have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      by_contra! h
      have he : T.card = 1 := by omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp he
      exact hn (Finset.mem_image.mpr ⟨j, hTS (by simp), rfl⟩)
    rw [polynomialIterDifference_smul]
    have hd : (∏ j ∈ S \ T, X j : MvPolynomial I R).totalDegree < n := by
      have htc := Finset.card_le_card hTS
      have hc := Finset.card_sdiff_of_subset hTS
      have hp := totalDegree_prod_X_le (R := R) (S \ T)
      omega
    rw [polynomialIterDifference_eq_zero_of_totalDegree_lt n _ hd, smul_zero]
  rw [← Finset.sum_subset hsub hz, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.prod_singleton, Finset.sdiff_singleton_eq_erase,
      polynomialIterDifference_smul]
  · intro a ha b hb h
    exact Finset.singleton_injective h

theorem polynomialIterDifference_prod_X_eq_permanent (n : ℕ) (S : Finset I)
    (hS : S.card = n) (u : Fin n → I → R) :
    polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u =
      C (squarefreePermanent n S u) := by
  induction n generalizing S with
  | zero =>
    have he : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [polynomialIterDifference, squarefreePermanent]
  | succ n ih =>
    rw [polynomialIterDifference, polynomialIterDifference_prod_X_step n S hS,
      squarefreePermanent, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih (S.erase j) (by rw [Finset.card_erase_of_mem hj, hS]; omega)]
    simp [smul_eq_C_mul]

theorem polynomialIterDifference_prod_X_linearCoeff_permanent (n : ℕ) (S : Finset I)
    (hS : S.card = n + 1) (i : I) (hi : i ∈ S) (u : Fin n → I → R) :
    (polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u).coeff
      (Finsupp.single i 1) = squarefreePermanent n (S.erase i) u := by
  rw [polynomialIterDifference_linearCoeff, pderiv_prod_X_of_mem S i hi,
    polynomialIterDifference_prod_X_eq_permanent n _
      (by rw [Finset.card_erase_of_mem hi, hS]; omega)]
  simp

theorem polynomialIterDifference_prod_X_linearCoeff_matrix_permanent
    (n : ℕ) (S : Finset I) (i : I) (hi : i ∈ S)
    (e : Fin n ≃ S.erase i) (u : Fin n → I → R) :
    (polynomialIterDifference n (∏ j ∈ S, X j : MvPolynomial I R) u).coeff
      (Finsupp.single i 1) = Matrix.permanent (fun a b => u a (e b).val) := by
  have hS : S.card = n + 1 := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_erase_of_mem hi] at hc
    have hp := Finset.card_pos.mpr (show S.Nonempty from ⟨i, hi⟩)
    omega
  rw [polynomialIterDifference_prod_X_linearCoeff_permanent n S hS i hi,
    squarefreePermanent_eq_matrix_permanent n _ e]

theorem polynomialIterDifference_designated_linearCoeff {A : Type*} (J : Finset A)
    (S : A → Finset I) (c : A → R) (Q : MvPolynomial I R)
    (n : ℕ) (b : A) (hb : b ∈ J) (i : I) (hi : i ∈ S b)
    (hcard : (S b).card = n + 1)
    (hseparate : ∀ a ∈ J, a ≠ b → i ∉ S a) (u : Fin n → I → R) :
    (polynomialIterDifference n (Q + ∑ a ∈ J, c a • ∏ j ∈ S a, X j) u).coeff
      (Finsupp.single i 1) =
      (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) +
        c b * squarefreePermanent n ((S b).erase i) u := by
  rw [polynomialIterDifference_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    polynomialIterDifference_sum]
  congr 1
  simp only [coeff_sum, polynomialIterDifference_smul, coeff_smul, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [polynomialIterDifference_prod_X_linearCoeff_permanent n (S b) hcard i hi]
  · intro a ha hab
    rw [polynomialIterDifference_prod_X_linearCoeff_zero (S a) i
      (hseparate a ha hab), mul_zero]
  · exact fun hn => False.elim (hn hb)

theorem polynomialIterDifference_disjoint_designated_linearCoeff {A : Type*}
    (J : Finset A) (S : A → Finset I) (c : A → R) (Q : MvPolynomial I R)
    (n : ℕ) (b : A) (hb : b ∈ J) (i : I) (hi : i ∈ S b)
    (hcard : (S b).card = n + 1)
    (hdisjoint : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)))
    (u : Fin n → I → R) :
    (polynomialIterDifference n (Q + ∑ a ∈ J, c a • ∏ j ∈ S a, X j) u).coeff
      (Finsupp.single i 1) =
      (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) +
        c b * squarefreePermanent n ((S b).erase i) u := by
  apply polynomialIterDifference_designated_linearCoeff J S c Q n b hb i hi hcard
  intro a ha hab hia
  exact (Finset.disjoint_left.mp (hdisjoint ha hb hab)) hia hi

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_mean
    {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).mean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, X i, (∏ i, (Fintype.card (X i) : ℝ)⁻¹) * f x) = _
  have hcard : (∏ i, (Fintype.card (X i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, X i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniform_expect_coordinate_pullback
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (a : J → I) (ha : Function.Injective a) (f : (∀ j, X (a j)) → ℝ) :
    (𝔼 x : ∀ i, X i, f (fun j => x (a j))) = 𝔼 y : ∀ j, X (a j), f y := by
  let μ := fun i => FiniteProbabilityWeights.uniform (X i)
  have h := productMean_pullback μ a ha (fun i => Classical.choice (inferInstance : Nonempty (X i))) f
  simpa only [μ, FiniteProbabilityWeights.pi_uniform_mean] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem productMean_prod_disjoint {I A : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (J : Finset A)
    (S : A → Finset I) (f : A → (∀ i, X i) → ℝ)
    (hdisjoint : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)))
    (hf : ∀ a ∈ J, ProductDependsOn (S a) (f a)) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ a ∈ J, f a x) =
      ∏ a ∈ J, (FiniteProbabilityWeights.pi μ).mean (f a) := by
  induction J using Finset.induction_on with
  | empty => simp [FiniteProbabilityWeights.mean_const]
  | @insert a J ha ih =>
    have hrest : (J : Set A).Pairwise (fun a b => Disjoint (S a) (S b)) :=
      fun b hb c hc hbc => hdisjoint (Finset.mem_insert_of_mem hb)
        (Finset.mem_insert_of_mem hc) hbc
    have hsep : Disjoint (S a) (J.biUnion S) := by
      rw [Finset.disjoint_left]
      intro i hi ht
      obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp ht
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      exact Finset.disjoint_left.mp
        (hdisjoint (Finset.mem_insert_self a J) (Finset.mem_insert_of_mem hb) hab) hi hib
    have hprod : ProductDependsOn (J.biUnion S) (fun x => ∏ b ∈ J, f b x) := by
      intro x y hxy
      apply Finset.prod_congr rfl
      intro b hb
      apply hf b (Finset.mem_insert_of_mem hb) x y
      intro i hi
      exact hxy i (Finset.mem_biUnion.mpr ⟨b,hb,hi⟩)
    simp only [Finset.prod_insert ha]
    rw [productMean_mul_disjoint μ (S a) (J.biUnion S) hsep (f a) _
      (hf a (Finset.mem_insert_self a J)) hprod]
    rw [ih hrest (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem uniform_expect_prod_disjoint_tuples {I A K V : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] [Fintype V] [Nonempty V]
    (J : Finset A) (v : A → K → I)
    (hv : ∀ a ∈ J, Function.Injective (v a))
    (hdisjoint : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (v a)) (Finset.univ.image (v b))))
    (f : A → (K → V) → ℝ) :
    (𝔼 x : I → V, ∏ a ∈ J, f a (fun k => x (v a k))) =
      ∏ a ∈ J, 𝔼 y : K → V, f a y := by
  have h := productMean_prod_disjoint
    (fun _ : I => FiniteProbabilityWeights.uniform V) J
    (fun a => Finset.univ.image (v a)) (fun a x => f a (fun k => x (v a k)))
    hdisjoint (by
      intro a ha x y hxy
      exact congrArg (f a) (funext fun k =>
        hxy (v a k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)))
  simp only [FiniteProbabilityWeights.pi_uniform_mean] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro a ha
  exact uniform_expect_coordinate_pullback (X := fun _ : I => V) (v a) (hv a ha) (f a)

theorem uniform_expect_prod_disjoint_tuples_le {I A K V : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] [Fintype V] [Nonempty V]
    (J : Finset A) (v : A → K → I)
    (hv : ∀ a ∈ J, Function.Injective (v a))
    (hdisjoint : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (v a)) (Finset.univ.image (v b))))
    (f : A → (K → V) → ℝ) (B : ℝ)
    (hf : ∀ a ∈ J, ∀ y, 0 ≤ f a y)
    (hmean : ∀ a ∈ J, (𝔼 y : K → V, f a y) ≤ B) :
    (𝔼 x : I → V, ∏ a ∈ J, f a (fun k => x (v a k))) ≤ B ^ J.card := by
  rw [uniform_expect_prod_disjoint_tuples J v hv hdisjoint f,
    ← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · intro a ha
    exact Finset.expect_nonneg (fun y _ => hf a ha y)
  · exact hmean

theorem uniform_expect_prod_disjoint_permanents {I A R : Type*}
    [Fintype I] [DecidableEq I] [Fintype R] [CommRing R] (n : ℕ)
    (J : Finset A) (v : A → Fin n → I)
    (hv : ∀ a ∈ J, Function.Injective (v a))
    (hdisjoint : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (v a)) (Finset.univ.image (v b))))
    (f : A → R → ℝ) :
    (𝔼 x : (Fin n × I) → R,
      ∏ a ∈ J, f a (Matrix.permanent (fun i j => x (i, v a j)))) =
      ∏ a ∈ J, 𝔼 y : (Fin n × Fin n) → R,
        f a (Matrix.permanent (fun i j => y (i,j))) := by
  let w : A → (Fin n × Fin n) → (Fin n × I) := fun a k => (k.1, v a k.2)
  have hw : ∀ a ∈ J, Function.Injective (w a) := by
    intro a ha k l h
    exact Prod.ext (congrArg (fun z : Fin n × I => z.1) h)
      (hv a ha (congrArg (fun z : Fin n × I => z.2) h))
  have hsep : (J : Set A).Pairwise (fun a b =>
      Disjoint (Finset.univ.image (w a)) (Finset.univ.image (w b))) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hz1
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hz2
    have he : v a k.2 = v b l.2 := congrArg Prod.snd (hk.trans hl.symm)
    exact Finset.disjoint_left.mp (hdisjoint ha hb hab)
      (Finset.mem_image.mpr ⟨k.2, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨l.2, Finset.mem_univ _, he.symm⟩)
  exact uniform_expect_prod_disjoint_tuples J w hw hsep
    (fun a y => f a (Matrix.permanent (fun i j => y (i,j))))

end Erdos3

end

end OAI
