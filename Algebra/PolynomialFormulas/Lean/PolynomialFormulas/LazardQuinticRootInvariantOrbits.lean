import PolynomialFormulas.Fin5TransitiveC5
import PolynomialFormulas.FrobeniusDummitResolvent
import PolynomialFormulas.LazardInvariantModule

/-!
# Metacyclic root-orbit polynomials

This module isolates the common orbit-polynomial construction and its
`F₂₀` invariance.  Keeping it separate bounds elaboration of the later
explicit ten-term orbit formulas and root-invariant identities.
-/

open scoped BigOperators Polynomial
open Equiv MvPolynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5
open LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
open LeanProofs.PolynomialFormulas.LazardInvariantModule

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev RootExponent := Fin 5 → ℕ

/-- Exponent vector supported at positions `0`, `1`, and `4`. -/
def lazardBaseExponent (a b c : ℕ) : RootExponent := fun i ↦
  if i = 0 then a else if i = 1 then b else if i = 4 then c else 0

/-- Exponent vector of one displayed term, with distinguished exponent `a`
at `i` and equal paired exponents `b` at `j` and `k`. -/
def lazardTermExponent (a b : ℕ) (i j k : Fin 5) : RootExponent := fun n ↦
  if n = i then a else if n = j ∨ n = k then b else 0

/-- The ten exponent vectors in Lazard's displayed orbit formula. -/
def lazardOrbitExponent (a b : ℕ) : Fin 10 → RootExponent :=
  ![lazardTermExponent a b 0 1 4, lazardTermExponent a b 0 2 3,
    lazardTermExponent a b 1 0 2, lazardTermExponent a b 1 3 4,
    lazardTermExponent a b 2 0 4, lazardTermExponent a b 2 1 3,
    lazardTermExponent a b 3 0 1, lazardTermExponent a b 3 2 4,
    lazardTermExponent a b 4 0 3, lazardTermExponent a b 4 1 2]

/-- Support of the ten displayed terms.  The injectivity hypothesis in the
evaluation theorem below makes explicit when these really are ten distinct
monomials. -/
def lazardOrbitFormulaSupport (a b : ℕ) : Finset RootExponent :=
  Finset.univ.image (lazardOrbitExponent a b)

/-- The ten-term cyclic formula for the orbit with distinguished exponent
`a` and paired exponents `b`. -/
def lazardOrbitFormula {K : Type*} [CommRing K] (a b : ℕ)
    (x : Fin 5 → K) : K :=
  x 0 ^ a * x 1 ^ b * x 4 ^ b + x 0 ^ a * x 2 ^ b * x 3 ^ b +
  x 1 ^ a * x 0 ^ b * x 2 ^ b + x 1 ^ a * x 3 ^ b * x 4 ^ b +
  x 2 ^ a * x 0 ^ b * x 4 ^ b + x 2 ^ a * x 1 ^ b * x 3 ^ b +
  x 3 ^ a * x 0 ^ b * x 1 ^ b + x 3 ^ a * x 2 ^ b * x 4 ^ b +
  x 4 ^ a * x 0 ^ b * x 3 ^ b + x 4 ^ a * x 1 ^ b * x 2 ^ b

/-- The ten formal monomials in display order. -/
noncomputable def lazardOrbitTerm (a b : ℕ) :
    Fin 10 → MvPolynomial (Fin 5) ℤ :=
  ![X 0 ^ a * X 1 ^ b * X 4 ^ b, X 0 ^ a * X 2 ^ b * X 3 ^ b,
    X 1 ^ a * X 0 ^ b * X 2 ^ b, X 1 ^ a * X 3 ^ b * X 4 ^ b,
    X 2 ^ a * X 0 ^ b * X 4 ^ b, X 2 ^ a * X 1 ^ b * X 3 ^ b,
    X 3 ^ a * X 0 ^ b * X 1 ^ b, X 3 ^ a * X 2 ^ b * X 4 ^ b,
    X 4 ^ a * X 0 ^ b * X 3 ^ b, X 4 ^ a * X 1 ^ b * X 2 ^ b]

theorem monomial_lazardOrbitExponent_eq_lazardOrbitTerm
    (a b : ℕ) (i : Fin 10) :
    monomial (Finsupp.equivFunOnFinite.symm (lazardOrbitExponent a b i)) 1 =
      lazardOrbitTerm a b i := by
  fin_cases i <;>
    simp [lazardOrbitExponent, lazardOrbitTerm, MvPolynomial.X,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_mul] <;>
    ext x <;> fin_cases x <;> simp [lazardTermExponent]

set_option maxHeartbeats 1000000 in
/-- Evaluating the displayed ten-monomial support gives the literal formula.
The visible injectivity condition rules out accidental multiplicities. -/
theorem eval₂_lazardOrbitFormulaSupport_eq_lazardOrbitFormula
    {K : Type*} [CommRing K] (x : Fin 5 → K) (a b : ℕ)
    (hinj : Function.Injective (lazardOrbitExponent a b)) :
    MvPolynomial.eval₂ (Int.castRingHom K) x
        (polynomialOfSupport (lazardOrbitFormulaSupport a b)) =
      lazardOrbitFormula a b x := by
  classical
  rw [lazardOrbitFormulaSupport, polynomialOfSupport,
    Finset.sum_image hinj.injOn]
  simp_rw [monomial_lazardOrbitExponent_eq_lazardOrbitTerm]
  simp [Fin.sum_univ_succ, lazardOrbitTerm, lazardOrbitFormula]
  ring

/-- Distinct monomials in the `F₂₀` orbit of an exponent vector. -/
def metacyclicOrbitSupport (d : RootExponent) : Finset RootExponent :=
  f20Elements.image (fun g ↦ actExponent g d)

/-- Sum of the distinct monomials in an `F₂₀` orbit. -/
noncomputable def metacyclicOrbitPolynomial (d : RootExponent) :
    MvPolynomial (Fin 5) ℤ :=
  polynomialOfSupport (metacyclicOrbitSupport d)

/-- Left multiplication by an element of `F₂₀` merely reindexes a complete
metacyclic orbit of exponent vectors. -/
theorem permuteSupport_metacyclicOrbitSupport
    (g : Fin5Solvable.S5) (hg : g ∈ standardF20) (d : RootExponent) :
    permuteSupport g (metacyclicOrbitSupport d) =
      metacyclicOrbitSupport d := by
  classical
  rw [metacyclicOrbitSupport, permuteSupport, Finset.image_image]
  ext e
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨g * h, ?_, actExponent_mul g h d⟩
    exact (mem_f20Elements_iff _).2
      (standardF20.mul_mem hg ((mem_f20Elements_iff _).1 hh))
  · rintro ⟨k, hk, rfl⟩
    refine ⟨g⁻¹ * k, ?_, ?_⟩
    · exact (mem_f20Elements_iff _).2
        (standardF20.mul_mem (standardF20.inv_mem hg)
          ((mem_f20Elements_iff _).1 hk))
    · rw [← actExponent_mul]
      congr 2
      group

/-- Each orbit polynomial is fixed by every element of the standard
metacyclic subgroup. -/
theorem rename_metacyclicOrbitPolynomial
    (g : Fin5Solvable.S5) (hg : g ∈ standardF20) (d : RootExponent) :
    rename g (metacyclicOrbitPolynomial d) =
      metacyclicOrbitPolynomial d := by
  rw [metacyclicOrbitPolynomial, rename_polynomialOfSupport,
    permuteSupport_metacyclicOrbitSupport g hg d]

/-- The same orbit polynomial over an arbitrary coefficient ring. -/
noncomputable def metacyclicOrbitPolynomialOver
    (K : Type*) [CommRing K] (d : RootExponent) :
    MvPolynomial (Fin 5) K :=
  (metacyclicOrbitPolynomial d).map (Int.castRingHom K)

theorem rename_metacyclicOrbitPolynomialOver
    (K : Type*) [CommRing K]
    (g : Fin5Solvable.S5) (hg : g ∈ standardF20) (d : RootExponent) :
    rename g (metacyclicOrbitPolynomialOver K d) =
      metacyclicOrbitPolynomialOver K d := by
  rw [metacyclicOrbitPolynomialOver, ← map_rename,
    rename_metacyclicOrbitPolynomial g hg d]

/-- In particular, every displayed orbit polynomial is an actual member of
the `F₂₀` invariant subalgebra used by Lazard's Theorem 2. -/
theorem metacyclicOrbitPolynomialOver_mem_invariantSubalgebra
    (K : Type*) [CommRing K] (d : RootExponent) :
    metacyclicOrbitPolynomialOver K d ∈
      invariantSubalgebra K (Fin 5) standardF20 := by
  rw [mem_invariantSubalgebra]
  intro g
  exact rename_metacyclicOrbitPolynomialOver K g.1 g.2 d

/-- Evaluation of a metacyclic orbit sum on five values. -/
noncomputable def metacyclicOrbitValue {K : Type*} [CommRing K]
    (d : RootExponent) (x : Fin 5 → K) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) x (metacyclicOrbitPolynomial d)

/-- Evaluation of an integral orbit polynomial commutes with every ring
homomorphism. -/
theorem map_metacyclicOrbitValue
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (d : RootExponent) (x : Fin 5 → K) :
    φ (metacyclicOrbitValue d x) =
      metacyclicOrbitValue d (fun j ↦ φ (x j)) := by
  change φ (MvPolynomial.eval₂ (Int.castRingHom K) x
      (metacyclicOrbitPolynomial d)) =
    MvPolynomial.eval₂ (Int.castRingHom L) (fun j ↦ φ (x j))
      (metacyclicOrbitPolynomial d)
  have hcast : φ.comp (Int.castRingHom K) = Int.castRingHom L := by
    ext z
    simp
  rw [MvPolynomial.hom_eval₂, hcast]

/-- A finite support equality transports the abstract orbit sum to Lazard's
literal ten-term expression.  The concrete equalities below discharge both
finite conditions by ordinary kernel computation. -/
theorem metacyclicOrbitValue_eq_lazardOrbitFormula
    {K : Type*} [CommRing K] (x : Fin 5 → K)
    (d : RootExponent) (a b : ℕ)
    (hsupport : metacyclicOrbitSupport d = lazardOrbitFormulaSupport a b)
    (hinj : Function.Injective (lazardOrbitExponent a b)) :
    metacyclicOrbitValue d x = lazardOrbitFormula a b x := by
  rw [metacyclicOrbitValue, metacyclicOrbitPolynomial, hsupport]
  exact eval₂_lazardOrbitFormulaSupport_eq_lazardOrbitFormula x a b hinj

def i4Exponent : RootExponent := lazardBaseExponent 2 1 1
def i5Exponent : RootExponent := lazardBaseExponent 3 1 1
def i6Exponent : RootExponent := lazardBaseExponent 4 1 1
def i7Exponent : RootExponent := lazardBaseExponent 3 2 2
def i8Exponent : RootExponent := lazardBaseExponent 4 2 2

theorem metacyclicOrbitValue_i5 {K : Type*} [CommRing K]
    (x : Fin 5 → K) :
    metacyclicOrbitValue i5Exponent x = lazardOrbitFormula 3 1 x := by
  apply metacyclicOrbitValue_eq_lazardOrbitFormula x i5Exponent 3 1
  · decide
  · decide

theorem metacyclicOrbitValue_i6 {K : Type*} [CommRing K]
    (x : Fin 5 → K) :
    metacyclicOrbitValue i6Exponent x = lazardOrbitFormula 4 1 x := by
  apply metacyclicOrbitValue_eq_lazardOrbitFormula x i6Exponent 4 1
  · decide
  · decide

theorem metacyclicOrbitValue_i7 {K : Type*} [CommRing K]
    (x : Fin 5 → K) :
    metacyclicOrbitValue i7Exponent x = lazardOrbitFormula 3 2 x := by
  apply metacyclicOrbitValue_eq_lazardOrbitFormula x i7Exponent 3 2
  · decide
  · decide

theorem metacyclicOrbitValue_i8 {K : Type*} [CommRing K]
    (x : Fin 5 → K) :
    metacyclicOrbitValue i8Exponent x = lazardOrbitFormula 4 2 x := by
  apply metacyclicOrbitValue_eq_lazardOrbitFormula x i8Exponent 4 2
  · decide
  · decide

end LeanProofs.PolynomialFormulas.LazardQuintic
