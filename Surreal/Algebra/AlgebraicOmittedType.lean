import Surreal.Algebra.IntegerPolynomialAvoidance
import Surreal.Algebra.IntegerPolynomialFormulas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The algebraic omitted type

The semantic core of `odg:def:thm:saturation`, for native ring formulas:
if a guard includes the ordinary naturals but only selects algebraic elements,
then the guard together with all nonzero integer polynomial inequalities is
finitely satisfiable and omitted. Finite satisfiability has ordinary natural
witnesses. Computable coding and recursive saturation are separate obligations.
-/

namespace Surreal.AlgebraicOmittedType
open FirstOrder FirstOrder.Language
open IntegerPolynomialFormulas

/-- The source's parameter-free type, expressed as a set of native formulas. -/
def formulas (δ : Language.ring.Formula (Fin 1)) : Set (Language.ring.Formula (Fin 1)) :=
  insert δ (nonvanishing '' {p : Polynomial ℤ | p ≠ 0})

/-- Realization of every formula in a unary partial type by one element. -/
def Realizes {R : Type*} [Language.ring.Structure R]
    (T : Set (Language.ring.Formula (Fin 1))) (x : R) : Prop :=
  ∀ φ ∈ T, φ.Realize (fun _ => x)

/-- Every finite subcollection of a unary partial type is realized in this structure. -/
def FinitelySatisfiable (R : Type*) [Language.ring.Structure R]
    (T : Set (Language.ring.Formula (Fin 1))) : Prop :=
  ∀ s : Finset (Language.ring.Formula (Fin 1)), (↑s : Set _) ⊆ T →
    ∃ x : R, ∀ φ ∈ s, φ.Realize (fun _ => x)

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]
    (δ : Language.ring.Formula (Fin 1))

/-- The full type says exactly that the guard holds and every nonzero polynomial is nonzero. -/
theorem realizes_iff (x : R) :
    Realizes (formulas δ) x ↔ δ.Realize (fun _ => x) ∧
      ∀ p : Polynomial ℤ, p ≠ 0 → p.eval₂ (Int.castRingHom R) x ≠ 0 := by
  simp [Realizes, formulas]

/-- A finite collection of polynomial inequalities has an ordinary witness with the source's bound. -/
theorem bounded_realization [CharZero R]
    (hδ : ∀ n : ℕ, δ.Realize (fun _ => (n : R)))
    (s : Finset (Polynomial ℤ)) (hs : ∀ p ∈ s, p ≠ 0) :
    ∃ n : ℕ, n ≤ ∑ p ∈ s, p.natDegree ∧ δ.Realize (fun _ => (n : R)) ∧
      ∀ p ∈ s, (nonvanishing p).Realize (fun _ => (n : R)) := by
  obtain ⟨n, hn, hp⟩ := IntegerPolynomialAvoidance.exists_nat_le_sum_degrees_cast R s hs
  exact ⟨n, hn, hδ n, fun p hps => (realize_nonvanishing p _).mpr (hp p hps)⟩

/-- Every finite subset of the native formula type is realized by an ordinary natural number. -/
theorem finite_subset_realized [CharZero R]
    (hδ : ∀ n : ℕ, δ.Realize (fun _ => (n : R)))
    (s : Finset (Language.ring.Formula (Fin 1))) (hs : (↑s : Set _) ⊆ formulas δ) :
    ∃ n : ℕ, ∀ φ ∈ s, φ.Realize (fun _ => (n : R)) := by
  classical
  have h : ∀ φ : s, ∃ p : Polynomial ℤ, p ≠ 0 ∧
      ((φ : Language.ring.Formula (Fin 1)) = δ ∨ φ.val = nonvanishing p) := by
    intro φ
    rcases hs φ.property with hφ | ⟨p, hp, hφ⟩
    · exact ⟨1, one_ne_zero, Or.inl hφ⟩
    · exact ⟨p, hp, Or.inr hφ.symm⟩
  choose p hp hφ using h
  obtain ⟨n, _, hn, hall⟩ := bounded_realization δ hδ (Finset.univ.image p) (by
    intro q hq
    obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp φ)
  refine ⟨n, fun φ hφs => ?_⟩
  rcases hφ ⟨φ, hφs⟩ with hguard | hpoly
  · change φ = δ at hguard
    rw [hguard]
    exact hn
  · change φ = nonvanishing (p ⟨φ, hφs⟩) at hpoly
    rw [hpoly]
    exact hall _ (Finset.mem_image.mpr ⟨⟨φ, hφs⟩, Finset.mem_univ _, rfl⟩)

/-- Native finite satisfiability follows from the guard holding on ordinary naturals. -/
theorem finitelySatisfiable [CharZero R]
    (hδ : ∀ n : ℕ, δ.Realize (fun _ => (n : R))) :
    FinitelySatisfiable R (formulas δ) := by
  intro s hs
  obtain ⟨n, hn⟩ := finite_subset_realized δ hδ s hs
  exact ⟨(n : R), hn⟩

/-- A guard selecting only algebraic elements makes the whole type impossible to realize. -/
theorem omitted (hδ : ∀ x : R, δ.Realize (fun _ => x) → IsAlgebraic ℤ x) :
    ¬ ∃ x : R, Realizes (formulas δ) x := by
  rintro ⟨x, hx⟩
  obtain ⟨hg, hp⟩ := (realizes_iff δ x).mp hx
  obtain ⟨p, hp0, hpx⟩ := hδ x hg
  exact hp p hp0 hpx

/-- Any native definition of an algebraic coefficient image gives a finitely satisfiable omitted type. -/
theorem finitelySatisfiable_and_omitted_of_range [CharZero R]
    {O : Type*} [CommRing O] (i : O →+* R)
    (hδ : ∀ x : R, δ.Realize (fun _ => x) ↔ x ∈ i.range)
    (hAlg : ∀ a : O, IsAlgebraic ℤ a) :
    FinitelySatisfiable R (formulas δ) ∧ ¬ ∃ x : R, Realizes (formulas δ) x := by
  constructor
  · apply finitelySatisfiable
    intro n
    exact (hδ _).mpr ⟨(n : O), map_natCast i n⟩
  · apply omitted
    intro x hx
    obtain ⟨a, rfl⟩ := (hδ x).mp hx
    exact (hAlg a).algHom i.toIntAlgHom

/-- Every quadratic integer has an explicit nonzero integer annihilator. -/
theorem zsqrtd_isAlgebraic (d : ℤ) (z : Zsqrtd d) : IsAlgebraic ℤ z := by
  let p : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
    Polynomial.C (z.re ^ 2 - d * z.im ^ 2)
  refine ⟨p, ?_, ?_⟩
  · intro hp
    have hc := congrArg (fun q : Polynomial ℤ => q.coeff 2) hp
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at hc
    norm_num at hc
  · simp only [p, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    apply Zsqrtd.ext <;> simp [pow_two, sub_eq_add_neg] <;> ring

/-- Xi holds on ordinary naturals in every commutative ring. -/
theorem xi_nat_realize (n : ℕ) :
    ArithmeticGuards.integerGuard.Realize (fun _ => (n : R)) := by
  rw [ArithmeticGuards.realize_integerGuard]
  simpa using (DiophantineConstants.integer_xi (n : ℤ)).map (Int.castRingHom R)

/-- The explicit Xi type is finitely satisfiable in every characteristic-zero ring. -/
theorem xi_finitelySatisfiable [CharZero R] :
    FinitelySatisfiable R (formulas ArithmeticGuards.integerGuard) :=
  finitelySatisfiable _ xi_nat_realize

/-- Defining an algebraic coefficient image suffices to omit the explicit Xi type. -/
theorem xi_omitted_of_range {O : Type*} [CommRing O] (i : O →+* R)
    (hXi : ∀ x : R, DiophantineConstants.Xi x → x ∈ i.range)
    (hAlg : ∀ a : O, IsAlgebraic ℤ a) :
    ¬ ∃ x : R, Realizes (formulas ArithmeticGuards.integerGuard) x := by
  apply omitted
  intro x hx
  obtain ⟨a, rfl⟩ := hXi x ((ArithmeticGuards.realize_integerGuard _).mp hx)
  exact (hAlg a).algHom i.toIntAlgHom

omit [FirstOrder.Ring.CompatibleRing R] in
/-- Any ring image of quadratic integers still consists of algebraic elements. -/
theorem zsqrtd_image_isAlgebraic (d : ℤ) (i : Zsqrtd d →+* R) (z : Zsqrtd d) :
    IsAlgebraic ℤ (i z) :=
  (zsqrtd_isAlgebraic d z).algHom i.toIntAlgHom

end Surreal.AlgebraicOmittedType
