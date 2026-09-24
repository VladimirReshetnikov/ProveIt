import Diophantine.Common.SignInvariantPolynomial
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The integer polynomial in the relation-combining theorem

The coefficient variables, in order, are the witness `n` and the parameters
`B`, `C`, `D`. The outer variables stand for the square radicands `Aᵢ`.
Before removing the formal radicals, `rawW = 1 + ∑ Xᵢ⁴`; after replacing
each `Xᵢ²` by `Aᵢ`, this is the original `W = 1 + ∑ Aᵢ²`.

Independent sign changes permute the factors of the signed product. The
explicit exponent-halving construction therefore produces an ordinary
polynomial with integer polynomial coefficients. This module proves the
polynomial and its evaluation formula; it does not assume the arithmetic
equivalence asserted by the relation-combining theorem.
-/

namespace Diophantine.RelationCombiningPolynomial

open MvPolynomial

noncomputable section

/-- The four coefficient variables are `n`, `B`, `C`, `D`, in this order. -/
abbrev Coeff := MvPolynomial (Fin 4) ℤ

/-- Formal radical variables with the four arithmetic parameters as coefficients. -/
abbrev RootPoly (q : ℕ) := MvPolynomial (Fin q) Coeff

/-- Boolean `true` chooses the positive sign. -/
def signed {S : Type*} [Neg S] (b : Bool) (x : S) : S :=
  if b then x else -x

/-- Flipping a variable toggles its chosen sign exactly when its index matches. -/
theorem signFlip_signed_X {σ R : Type*} [DecidableEq σ] [CommRing R]
    (i j : σ) (b : Bool) :
    signFlip i (signed b (X j : MvPolynomial σ R)) =
      signed (if j = i then !b else b) (X j) := by
  by_cases hji : j = i <;> cases b <;> simp [signed, hji]

/-- Change precisely one sign in a choice of signs. -/
def toggle {q : ℕ} (i : Fin q) (ε : Fin q → Bool) : Fin q → Bool :=
  fun j => if j = i then !(ε j) else ε j

@[simp]
theorem toggle_toggle {q : ℕ} (i : Fin q) (ε : Fin q → Bool) :
    toggle i (toggle i ε) = ε := by
  funext j
  by_cases hji : j = i <;> simp [toggle, hji]

/-- Changing one sign is a permutation of all sign choices. -/
def toggleEquiv {q : ℕ} (i : Fin q) : (Fin q → Bool) ≃ (Fin q → Bool) where
  toFun := toggle i
  invFun := toggle i
  left_inv := toggle_toggle i
  right_inv := toggle_toggle i

/-- The base before the formal radical squares have been removed. -/
def rawW (q : ℕ) : RootPoly q := 1 + ∑ i : Fin q, X i ^ 4

/-- One signed factor in the original Matiyasevich--Robinson product. -/
def rawFactor (q : ℕ) (ε : Fin q → Bool) : RootPoly q :=
  C ((X 1 : Coeff) ^ 2 * X 0 + X 2 ^ 2) -
    C ((X 1 : Coeff) ^ 2 * (2 * X 3 - 1)) *
      (C ((X 2 : Coeff) ^ 2) + rawW q ^ q +
        ∑ i : Fin q, signed (ε i) (X i) * rawW q ^ i.val)

/-- The product over all `2^q` sign choices. -/
def rawProduct (q : ℕ) : RootPoly q :=
  ∏ ε : Fin q → Bool, rawFactor q ε

@[simp]
theorem signFlip_rawW (q : ℕ) (i : Fin q) : signFlip i (rawW q) = rawW q := by
  simp only [rawW, map_add, map_one, map_sum, map_pow]
  apply congrArg (fun p : RootPoly q => 1 + p)
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j = i <;> simp [hji]
  ring

/-- Flipping one radical changes precisely its sign in each factor. -/
theorem signFlip_rawFactor (q : ℕ) (i : Fin q) (ε : Fin q → Bool) :
    signFlip i (rawFactor q ε) = rawFactor q (toggle i ε) := by
  simp only [rawFactor, map_sub, map_mul, signFlip_C, map_add, map_pow,
    map_sum, signFlip_rawW, signFlip_signed_X, toggle]

/-- Every independent sign change permutes the factors of the whole product. -/
theorem signFlip_rawProduct (q : ℕ) (i : Fin q) :
    signFlip i (rawProduct q) = rawProduct q := by
  rw [rawProduct, map_prod]
  exact Fintype.prod_equiv (toggleEquiv i)
    (fun ε => signFlip i (rawFactor q ε)) (rawFactor q)
    (fun ε => signFlip_rawFactor q i ε)

/-- The explicit polynomial in the square radicands, obtained by halving exponents. -/
def core (q : ℕ) : RootPoly q := halveExponents (rawProduct q)

/-- Substitution of the squares recovers the exact original signed product. -/
theorem expand_two_core (q : ℕ) : expand 2 (core q) = rawProduct q :=
  expand_two_halveExponents_of_signFlip_invariant (rawProduct q) (signFlip_rawProduct q)

section Evaluation

variable {S : Type*} [CommRing S]

/-- The arithmetic signed product in an arbitrary commutative ring. -/
def radicalProduct (q : ℕ) (A r : Fin q → S) (n B C D : S) : S :=
  Finset.univ.prod (fun ε : Fin q → Bool =>
    B ^ 2 * n + C ^ 2 - B ^ 2 * (2 * D - 1) *
      (C ^ 2 + (1 + ∑ i : Fin q, A i ^ 2) ^ q +
        ∑ i : Fin q, signed (ε i) (r i) * (1 + ∑ j : Fin q, A j ^ 2) ^ i.val))

@[simp]
theorem eval₂_signed (q : ℕ) (f : Coeff →+* S) (r : Fin q → S)
    (b : Bool) (p : RootPoly q) :
    eval₂ f r (signed b p) = signed b (eval₂ f r p) := by
  cases b <;> simp [signed]

theorem eval₂_rawW (q : ℕ) (f : Coeff →+* S) (A r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = A i) :
    eval₂ f r (rawW q) = 1 + ∑ i : Fin q, A i ^ 2 := by
  simp only [rawW, eval₂_add, eval₂_one, eval₂_sum, eval₂_pow, eval₂_X]
  apply congrArg (fun s : S => 1 + s)
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hr i]

/-- Evaluation of the formal radical product gives the displayed product. -/
theorem eval₂_rawProduct (q : ℕ) (f : Coeff →+* S) (A r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = A i) :
    eval₂ f r (rawProduct q) =
      radicalProduct q A r (f (X 0)) (f (X 1)) (f (X 2)) (f (X 3)) := by
  simp only [rawProduct, radicalProduct, eval₂_prod]
  apply Finset.prod_congr rfl
  intro ε hε
  simp only [rawFactor, eval₂_sub, eval₂_C, eval₂_mul, eval₂_add, eval₂_pow,
    eval₂_sum, eval₂_signed, eval₂_X, eval₂_rawW q f A r hr,
    map_add, map_mul, map_pow, map_sub, map_ofNat, map_one, eval₂_ofNat, eval₂_one]

/-- Evaluation of the ordinary core polynomial equals the signed radical
product whenever the supplied roots square to the supplied radicands. -/
theorem eval₂_core_eq_product (q : ℕ) (f : Coeff →+* S) (A r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = A i) :
    eval₂ f A (core q) =
      radicalProduct q A r (f (X 0)) (f (X 1)) (f (X 2)) (f (X 3)) := by
  have hpow : r ^ 2 = A := funext hr
  calc
    eval₂ f A (core q) = eval₂ f r (expand 2 (core q)) := by
      rw [eval₂_expand, hpow]
    _ = eval₂ f r (rawProduct q) := by rw [expand_two_core]
    _ = _ := eval₂_rawProduct q f A r hr

end Evaluation

/-- Evaluation of the four coefficient variables in the order `n`, `B`, `C`, `D`. -/
def coeffEval (n B C D : ℤ) : Coeff →+* ℤ := eval ![n, B, C, D]

/-- Integer value of the ordinary relation-combining polynomial. -/
def value (q : ℕ) (A : Fin q → ℤ) (n B C D : ℤ) : ℤ :=
  eval₂ (coeffEval n B C D) A (core q)

/-- The semantic interface: the integer polynomial value, cast to any
commutative ring containing the chosen roots, is the exact signed product. -/
theorem value_eq_product {S : Type*} [CommRing S] (q : ℕ)
    (A : Fin q → ℤ) (n B C D : ℤ) (r : Fin q → S)
    (hr : ∀ i, r i ^ 2 = (A i : S)) :
    (value q A n B C D : S) =
      radicalProduct q (fun i => (A i : S)) r n B C D := by
  change (Int.castRingHom S) (eval₂ (coeffEval n B C D) A (core q)) = _
  rw [eval₂_comp_left]
  have hh := eval₂_core_eq_product q
    ((Int.castRingHom S).comp (coeffEval n B C D))
    (fun i => (A i : S)) r hr
  simpa [coeffEval, Function.comp_def] using hh

end

end Diophantine.RelationCombiningPolynomial
