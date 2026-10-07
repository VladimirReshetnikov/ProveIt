import OAI.Combinatorics.Progressions.Estimates.PreparationLogCost

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_polynomial_layer_exp {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    (M : ℝ) ≤ p → ((j + 1 : ℕ) : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ p →
    (T : ℝ) + 1 ≤ p → share⁻¹ ≤ Real.exp p → (∀ i, Real.exp budget ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ (∀ x k, |err x k| ≤ δ) ∧
      ∀ x k, eval (fun i => ((S.point x i).val : ℝ)) P k =
        L.value (fun i => ((x i).val : ℝ)) k +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip k) : ℝ) + c k + err x k := by
  classical
  intro D T M share budget hM hs hn hT hshareinv hN
  have hshare : 0 < share := by dsimp [share]; positivity
  obtain ⟨hQ, hC⟩ := preparation_total_cost_le_exp hp hs hn hM hT hRp hshare hshareinv
  obtain ⟨q, S, L, ip, c, err, hrank, hsize, hheight, hgood, hq, hqbound,
    hlength, hscore, hip, herr, hid⟩ :=
    exists_prepared_polynomial_layer P hP hp hR hRp hδ N f hM (fun i => hC.trans (hN i))
  refine ⟨q, S, L, ip, c, err, hrank, hsize, hheight, hgood, hq,
    (Nat.cast_le.mpr hqbound).trans hQ, ?_, hscore, hip, herr, hid⟩
  intro i
  refine ⟨(hlength i).1, (hlength i).2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (pow_le_pow_right₀ (preparationShrink_one_le (j + 1) (Fintype.card I) M hR hp hshare)
    (Nat.le_succ T)).trans hC

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace VectorPolynomial

theorem degreeLE_subtraction {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} {p q : VectorPolynomial I ℝ V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q) :
    DegreeLE (fun _ => 1) d (p - q) := by
  intro α hα
  simp only [map_sub, Finsupp.sub_apply, hp α hα, hq α hα, sub_self]

noncomputable def integerCoordinates {I J : Type*} [Fintype J] (ip : J → MvPolynomial I ℤ) :
    VectorPolynomial I ℝ (J → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ J) (fun j => MvPolynomial.map (Int.castRingHom ℝ) (ip j))

theorem integerCoordinates_degree {I J : Type*} [Fintype J] {d : ℕ}
    (ip : J → MvPolynomial I ℤ) (hip : ∀ j, (ip j).totalDegree ≤ d) :
    DegreeLE (fun _ => 1) d (integerCoordinates ip) := by
  classical
  intro α hα
  have hs : d < ∑ i ∈ α.support, α i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_one] using hα
  rw [integerCoordinates, coefficients_ofCoordinates]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_eq_zero_of_totalDegree_lt ((hip j).trans_lt hs)]
  simp

theorem integerCoordinates_eval {I J : Type*} [Fintype J]
    (ip : J → MvPolynomial I ℤ) (x : I → ℤ) :
    eval (fun i => (x i : ℝ)) (integerCoordinates ip) =
      fun j => (MvPolynomial.eval x (ip j) : ℝ) := by
  have he : eval₂ (fun i => (x i : ℝ)) (integerCoordinates ip) =
      eval (fun i => (x i : ℝ)) (integerCoordinates ip) := by
    simpa using (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℝ)) (integerCoordinates ip))
  rw [← he, integerCoordinates, eval₂_ofCoordinates, Pi.basisFun_equivFun]
  funext j
  exact (MvPolynomial.map_eval (Int.castRingHom ℝ) x (ip j)).symm

theorem integerCoordinates_eval_real {I J : Type*} [Fintype J]
    (ip : J → MvPolynomial I ℤ) (x : I → ℝ) :
    eval x (integerCoordinates ip) =
      fun j => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (ip j)) := by
  have he : eval₂ x (integerCoordinates ip) = eval x (integerCoordinates ip) := by
    simpa using (eval₂_algebraMap (S := ℝ) x (integerCoordinates ip))
  rw [← he, integerCoordinates, eval₂_ofCoordinates, Pi.basisFun_equivFun]
  rfl

end VectorPolynomial

namespace RankPreparationFamily

noncomputable def polynomial {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) : VectorPolynomial I ℝ (J → ℝ) :=
  ∑ u, map (coordinateCopySum (L u).label) (L u).poly

theorem polynomial_eval {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) (x : I → ℝ) : eval x L.polynomial = L.value x := by
  simp only [polynomial, map_sum, eval_map]
  rfl

theorem polynomial_degree {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s)
    (hL : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly) :
    DegreeLE (fun _ => 1) s L.polynomial := by
  apply degreeLE_finset_sum
  intro u _
  apply DegreeLE.map
  intro α hα
  exact hL u α (lt_of_le_of_lt (Nat.succ_le_of_lt u.isLt) hα)

end RankPreparationFamily

theorem prepared_error_polynomial {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    {s q : ℕ} {δ : ℝ} {N : I → ℕ} (S : ResidueBoxSlice N q)
    (P : VectorPolynomial I ℝ (J → ℝ)) (hP : DegreeLE (fun _ => 1) s P)
    (L : RankPreparationFamily I J s)
    (hL : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly)
    (ip : J → MvPolynomial I ℤ) (hip : ∀ j, (ip j).totalDegree ≤ s)
    (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ)
    (herr : ∀ x j, |err x j| ≤ δ)
    (hid : ∀ x j, eval (fun i => ((S.point x i).val : ℝ)) P j =
      L.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j) :
    ∃ E : VectorPolynomial I ℝ (J → ℝ), DegreeLE (fun _ => 1) s E ∧
      substitute S.polynomial P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E ∧
      ∀ (x : ∀ i, Fin (S.length i)) (j : J), |eval (fun i => ((x i).val : ℝ)) E j| ≤ δ := by
  let E := substitute S.polynomial P - L.polynomial - integerCoordinates ip - (1 ⊗ₜ[ℝ] c)
  have hE : DegreeLE (fun _ => 1) s E := by
    apply degreeLE_subtraction
    · apply degreeLE_subtraction
      · exact degreeLE_subtraction (degreeLE_substitute_affine S.polynomial S.polynomial_degree P hP)
          (L.polynomial_degree hL)
      · exact integerCoordinates_degree ip hip
    · exact degreeLE_tmul_totalDegree 1 c (by simp)
  refine ⟨E, hE, ?_, ?_⟩
  · dsimp [E]
    abel
  · intro x j
    have hint := integerCoordinates_eval ip (fun i => ((x i).val : ℤ))
    simp only [Int.cast_natCast] at hint
    have heval : eval (fun i => ((x i).val : ℝ)) E j = err x j := by
      dsimp only [E]
      rw [map_sub, map_sub, map_sub, eval_slice_substitute, RankPreparationFamily.polynomial_eval, hint]
      simp only [Pi.sub_apply, eval_tmul, map_one, one_smul]
      linarith [hid x j]
    rw [heval]
    exact herr x j

end Erdos3

end

end OAI
