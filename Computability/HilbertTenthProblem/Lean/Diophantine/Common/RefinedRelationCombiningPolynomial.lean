import Diophantine.Common.RelationCombiningPolynomial

/-!
# The refined relation-combining polynomial

This version uses the unsquared divisibility parameters and a separate
weight `Vᵢ` for each formal radical. Write `Pᵢ = ∏ j < i, Vⱼ`. Its signed
factors are

`B*n + C - B*(2*D - 1)*(C + Pq + ∑ i, ±rᵢ*Pᵢ)`.

The weights are independent coefficient variables. Independent radical
sign changes permute the factors, so explicit exponent halving produces
an ordinary integer polynomial in the radicands, weights, and parameters.
The evaluation and composition results are purely algebraic: positivity,
growth bounds, and the arithmetic relation-combining equivalence belong
to the semantic layer.
-/

namespace Diophantine.RefinedRelationCombiningPolynomial

open MvPolynomial
open Diophantine.RelationCombiningPolynomial (signed toggle toggleEquiv)

noncomputable section

/-- The product of the weights whose indices are strictly below `m`. -/
def weightPrefix {q : ℕ} {S : Type*} [CommMonoid S] (V : Fin q → S) (m : ℕ) : S :=
  (Finset.univ.filter fun j : Fin q => j.val < m).prod V

@[simp]
theorem prefix_zero {q : ℕ} {S : Type*} [CommMonoid S] (V : Fin q → S) :
    weightPrefix V 0 = 1 := by
  simp [weightPrefix]

@[simp]
theorem prefix_all {q : ℕ} {S : Type*} [CommMonoid S] (V : Fin q → S) :
    weightPrefix V q = ∏ j : Fin q, V j := by
  simp [weightPrefix]

theorem map_prefix {q : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (V : Fin q → R) (m : ℕ) :
    f (weightPrefix V m) = weightPrefix (fun i => f (V i)) m := by
  simp [weightPrefix]

/-- Left coefficient variables are the individual weights; right variables
`0`, `1`, `2`, `3` are respectively `n`, `B`, `C`, `D`. -/
abbrev Coeff (q : ℕ) := MvPolynomial (Fin q ⊕ Fin 4) ℤ

/-- The outer variables are formal radicals, with polynomial coefficients. -/
abbrev RootPoly (q : ℕ) := MvPolynomial (Fin q) (Coeff q)

/-- The prefix product of the independent coefficient weight variables. -/
def rawWeight (q m : ℕ) : Coeff q :=
  weightPrefix (fun j : Fin q => X (Sum.inl j)) m

/-- One factor of the refined signed product. -/
def rawFactor (q : ℕ) (ε : Fin q → Bool) : RootPoly q :=
  C ((X (Sum.inr 1) : Coeff q) * X (Sum.inr 0) + X (Sum.inr 2)) -
    C ((X (Sum.inr 1) : Coeff q) * (2 * X (Sum.inr 3) - 1)) *
      (C (X (Sum.inr 2)) + C (rawWeight q q) +
        ∑ i : Fin q, signed (ε i) (X i) * C (rawWeight q i.val))

/-- The product over all `2^q` choices of radical signs. -/
def rawProduct (q : ℕ) : RootPoly q :=
  ∏ ε : Fin q → Bool, rawFactor q ε

/-- Changing one radical sign changes just that sign in every factor. -/
theorem signFlip_rawFactor (q : ℕ) (i : Fin q) (ε : Fin q → Bool) :
    signFlip i (rawFactor q ε) = rawFactor q (toggle i ε) := by
  simp only [rawFactor, map_sub, map_mul, signFlip_C, map_add,
    map_sum, RelationCombiningPolynomial.signFlip_signed_X, toggle]

/-- The full product is invariant under each independent sign change. -/
theorem signFlip_rawProduct (q : ℕ) (i : Fin q) :
    signFlip i (rawProduct q) = rawProduct q := by
  rw [rawProduct, map_prod]
  exact Fintype.prod_equiv (toggleEquiv i)
    (fun ε => signFlip i (rawFactor q ε)) (rawFactor q)
    (fun ε => signFlip_rawFactor q i ε)

/-- The explicit polynomial in radicands, constructed by halving the
exponents of the formal radical variables. -/
def core (q : ℕ) : RootPoly q := halveExponents (rawProduct q)

/-- Substituting the squares recovers the exact refined signed product. -/
theorem expand_two_core (q : ℕ) : expand 2 (core q) = rawProduct q :=
  expand_two_halveExponents_of_signFlip_invariant (rawProduct q) (signFlip_rawProduct q)

section Evaluation

variable {S : Type*} [CommRing S]

/-- The unsquared signed product, using the individual prefix weights. -/
def radicalProduct (q : ℕ) (V r : Fin q → S) (n B C D : S) : S :=
  Finset.univ.prod (fun ε : Fin q → Bool =>
    B * n + C - B * (2 * D - 1) *
      (C + weightPrefix V q + ∑ i : Fin q, signed (ε i) (r i) * weightPrefix V i.val))

@[simp]
theorem eval₂_signed (q : ℕ) (f : Coeff q →+* S) (r : Fin q → S)
    (b : Bool) (p : RootPoly q) :
    eval₂ f r (signed b p) = signed b (eval₂ f r p) := by
  cases b <;> simp [signed]

/-- Evaluation of a formal prefix weight is the same prefix product of
the evaluated independent weight variables. -/
theorem eval_rawWeight (q m : ℕ) (f : Coeff q →+* S) :
    f (rawWeight q m) = weightPrefix (fun i => f (X (Sum.inl i))) m := by
  exact map_prefix f _ m

/-- Evaluation of the formal product gives its displayed arithmetic form. -/
theorem eval₂_rawProduct (q : ℕ) (f : Coeff q →+* S) (r : Fin q → S) :
    eval₂ f r (rawProduct q) =
      radicalProduct q (fun i => f (X (Sum.inl i))) r
        (f (X (Sum.inr 0))) (f (X (Sum.inr 1)))
        (f (X (Sum.inr 2))) (f (X (Sum.inr 3))) := by
  simp only [rawProduct, radicalProduct, eval₂_prod]
  apply Finset.prod_congr rfl
  intro ε hε
  simp only [rawFactor, eval₂_sub, eval₂_C, eval₂_mul, eval₂_add,
    eval₂_sum, eval₂_signed, eval₂_X, eval_rawWeight,
    map_add, map_mul, map_sub, map_ofNat, map_one, eval₂_ofNat, eval₂_one,
    weightPrefix, eval₂_prod]

/-- The ordinary core evaluated at radicands equals the signed product
whenever the supplied radicals square to those radicands. -/
theorem eval₂_core_eq_product (q : ℕ) (f : Coeff q →+* S) (A r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = A i) :
    eval₂ f A (core q) =
      radicalProduct q (fun i => f (X (Sum.inl i))) r
        (f (X (Sum.inr 0))) (f (X (Sum.inr 1)))
        (f (X (Sum.inr 2))) (f (X (Sum.inr 3))) := by
  have hpow : r ^ 2 = A := funext hr
  calc
    eval₂ f A (core q) = eval₂ f r (expand 2 (core q)) := by
      rw [eval₂_expand, hpow]
    _ = eval₂ f r (rawProduct q) := by rw [expand_two_core]
    _ = _ := eval₂_rawProduct q f r

end Evaluation

/-- Evaluate the independent weights and the four arithmetic parameters. -/
def coeffEval (q : ℕ) (V : Fin q → ℤ) (n B C D : ℤ) : Coeff q →+* ℤ :=
  eval (Sum.elim V ![n, B, C, D])

/-- Integer value of the refined ordinary relation-combining polynomial. -/
def value (q : ℕ) (A V : Fin q → ℤ) (n B C D : ℤ) : ℤ :=
  eval₂ (coeffEval q V n B C D) A (core q)

/-- Casting the integer polynomial value into a ring with the chosen roots
gives the exact refined signed product. -/
theorem value_eq_product {S : Type*} [CommRing S] (q : ℕ)
    (A V : Fin q → ℤ) (n B C D : ℤ) (r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = (A i : S)) :
    (value q A V n B C D : S) =
      radicalProduct q (fun i => (V i : S)) r n B C D := by
  change (Int.castRingHom S) (eval₂ (coeffEval q V n B C D) A (core q)) = _
  rw [eval₂_comp_left]
  have hh := eval₂_core_eq_product q
    ((Int.castRingHom S).comp (coeffEval q V n B C D))
    (fun i => (A i : S)) r hr
  simpa [coeffEval, Function.comp_def] using hh

section Composition

variable {σ : Type*}

/-- Simultaneously substitute all individual weights and parameters by
ordinary integer polynomials in an arbitrary variable type. -/
def parameterSubstitution (q : ℕ) (V : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) : Coeff q →+* MvPolynomial σ ℤ :=
  eval₂Hom C (Sum.elim V ![n, b, c, d])

/-- Polynomial composition with the refined core. -/
def compose (q : ℕ) (A V : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  eval₂ (parameterSubstitution q V n b c d) A (core q)

theorem eval_comp_parameterSubstitution (q : ℕ) (v : σ → ℤ)
    (V : Fin q → MvPolynomial σ ℤ) (n b c d : MvPolynomial σ ℤ) :
    (eval v).comp (parameterSubstitution q V n b c d) =
      coeffEval q (fun i => eval v (V i))
        (eval v n) (eval v b) (eval v c) (eval v d) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [parameterSubstitution, coeffEval]
  · intro i
    rcases i with i | i
    · simp [parameterSubstitution, coeffEval]
    · fin_cases i <;> simp [parameterSubstitution, coeffEval]

/-- Evaluation commutes with substitution of all radicands, individual
weights, and arithmetic parameters. -/
theorem eval_compose (q : ℕ) (A V : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) (v : σ → ℤ) :
    eval v (compose q A V n b c d) =
      value q (fun i => eval v (A i)) (fun i => eval v (V i))
        (eval v n) (eval v b) (eval v c) (eval v d) := by
  unfold compose value
  rw [eval₂_comp_left, eval_comp_parameterSubstitution]
  rfl

end Composition

/-- A literal integer polynomial on `2*q + 4` coordinates: first the
radicands, then the weights, and finally `n`, `B`, `C`, `D`. -/
def polynomial (q : ℕ) : MvPolynomial (Fin q ⊕ (Fin q ⊕ Fin 4)) ℤ :=
  compose q (fun i => X (Sum.inl i)) (fun i => X (Sum.inr (Sum.inl i)))
    (X (Sum.inr (Sum.inr 0))) (X (Sum.inr (Sum.inr 1)))
    (X (Sum.inr (Sum.inr 2))) (X (Sum.inr (Sum.inr 3)))

theorem eval_polynomial (q : ℕ) (A V : Fin q → ℤ) (n b c d : ℤ) :
    eval (Sum.elim A (Sum.elim V ![n, b, c, d])) (polynomial q) =
      value q A V n b c d := by
  rw [polynomial, eval_compose]
  simp

theorem eval_polynomial_assignment (q : ℕ) (v : Fin q ⊕ (Fin q ⊕ Fin 4) → ℤ) :
    eval v (polynomial q) =
      value q (fun i => v (Sum.inl i)) (fun i => v (Sum.inr (Sum.inl i)))
        (v (Sum.inr (Sum.inr 0))) (v (Sum.inr (Sum.inr 1)))
        (v (Sum.inr (Sum.inr 2))) (v (Sum.inr (Sum.inr 3))) := by
  rw [polynomial, eval_compose]
  simp

end

end Diophantine.RefinedRelationCombiningPolynomial
