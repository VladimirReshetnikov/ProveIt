import OAI.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realJetMatrix_monomial_congr_support {α K I J : Type*} [DecidableEq α]
    (e : J → K →₀ ℕ) (v u : Finset α → K → ℝ) (rows : I → Finset α)
    (he : ∀ j t k, k ∈ (e j).support → v t k = u t k) :
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) v rows =
      realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) u rows := by
  funext i j
  apply congrArg (fun f => booleanCoefficient f (rows i))
  funext t
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  exact Finset.prod_congr rfl (fun k hk => congrArg (fun a => a^e j k) (he j t k hk))

theorem normalizedIntegerKernelJetMatrix_eq_support {α K I J : Type*} [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (v : Finset α → K → ℤ) (u : Finset α → K → ℝ)
    (rows : I → Finset α) (T : K → ℝ) {H : ℝ} (hH : H ≠ 0)
    (he : ∀ j t k, k ∈ (e j).support → (v t k : ℝ)/T k = u t k) :
    normalizedIntegerColumns (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) v rows)
      (fun j => H/monomialScale T (e j)) (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) u rows := by
  rw [normalizedIntegerMonomialJetMatrix_eq e v rows T hH]
  exact realJetMatrix_monomial_congr_support e _ u rows he

theorem normalizedCubeTuple_eq_of_frozen {Z X K α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (x y : X → ℝ) (k : K)
    (hk : ∀ r, ∃ j, input k r = Sum.inl j) (t : Finset α) :
    normalizedCubeTuple input z x t k = normalizedCubeTuple input z y t k := by
  unfold normalizedCubeTuple
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨j, hj⟩ := hk r
  simp only [hj, Sum.elim_inl]

theorem kernelJetMatrix_ignore_active {Z X K α I J : Type*} [Fintype α] [DecidableEq α]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (x y : X → ℝ)
    (he : ∀ j k, k ∈ (e j).support → ∀ r, ∃ a, input k r = Sum.inl a) :
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) (normalizedCubeTuple input z x) rows =
      realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) (normalizedCubeTuple input z y) rows :=
  realJetMatrix_monomial_congr_support e _ _ rows
    (fun j t k hk => normalizedCubeTuple_eq_of_frozen input z x y k (he j k hk) t)

theorem normalized_frozenKernelJetMatrix {Z X K α I J : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (v : Finset α → K → ℤ) (T : K → ℝ) {H : ℝ} (hH : H ≠ 0)
    (hcoords : ∀ j t k, k ∈ (e j).support → (v t k : ℝ)/T k = normalizedCubeTuple input z 0 t k)
    (hfrozen : ∀ j k, k ∈ (e j).support → ∀ r, ∃ a, input k r = Sum.inl a) (x : X → ℝ) :
    normalizedIntegerColumns (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) v rows)
      (fun j => H/monomialScale T (e j)) (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) (normalizedCubeTuple input z x) rows :=
  (normalizedIntegerKernelJetMatrix_eq_support e v _ rows T hH hcoords).trans
    (kernelJetMatrix_ignore_active e input z rows 0 x hfrozen)

end Erdos3

end

end OAI
