import Surreal.Algebra.PolynomialSolutionRetraction

/-!
# Finite integer-coefficient Diophantine systems

The finite-system convention and the transfer step of `odg:def:thm:ce`.
Free coordinates and existential witnesses are separate finite tuples.
No order, square root, or single-equation conversion is assumed.
-/

namespace Surreal.IntegerDiophantine

/-- A finite system with n free integer-coefficient polynomial coordinates. -/
structure System (n : ℕ) where
  witnesses : ℕ
  equations : ℕ
  polynomial : Fin equations → MvPolynomial (Fin n ⊕ Fin witnesses) ℤ

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- Solvability at a free tuple, with witnesses in the same ring. -/
def System.Holds (p : System n) (x : Fin n → R) : Prop :=
  ∃ y : Fin p.witnesses → R,
    ∀ j, (p.polynomial j).eval₂ (Int.castRingHom R) (Sum.elim x y) = 0

/-- Diophantine definability by finitely many equations with integer coefficients. -/
def Definable (D : Set (Fin n → R)) : Prop :=
  ∃ p : System n, ∀ x, p.Holds x ↔ x ∈ D

/-- Regard a set of ordinary integer tuples as a set of tuples in the larger ring. -/
def standardImage (D : Set (Fin n → ℤ)) : Set (Fin n → R) :=
  {x | ∃ z ∈ D, (fun j => (z j : R)) = x}

/-- Ring homomorphisms carry witnesses and free coordinates together. -/
theorem System.Holds.map {p : System n} {x : Fin n → R}
    (h : p.Holds x) (f : R →+* S) : p.Holds (f ∘ x) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨f ∘ y, fun j => ?_⟩
  have he := congrArg f (hy j)
  rw [MvPolynomial.hom_eval₂, map_zero] at he
  have hf : f.comp (Int.castRingHom R) = Int.castRingHom S := Subsingleton.elim _ _
  have hv : (fun v => f (Sum.elim x y v)) = Sum.elim (f ∘ x) (f ∘ y) := by
    funext v
    cases v <;> rfl
  rw [hf, hv] at he
  exact he

/-- Retracting witnesses preserves truth at ordinary free tuples. -/
theorem System.holds_intCast_iff (p : System n) (ct : R →+* ℤ) (x : Fin n → ℤ) :
    p.Holds (fun j => (x j : R)) ↔ p.Holds x := by
  constructor
  · intro h
    have he := h.map ct
    simpa only [Function.comp_def, map_intCast, Int.cast_id] using he
  · intro h
    exact h.map (Int.castRingHom R)

/-- The same finite equations define the integer trace; witnesses need no extra guards. -/
theorem Definable.integer_trace (ct : R →+* ℤ) {D : Set (Fin n → R)}
    (hD : Definable D) : Definable {x : Fin n → ℤ | (fun j => (x j : R)) ∈ D} := by
  obtain ⟨p, hp⟩ := hD
  exact ⟨p, fun x => (p.holds_intCast_iff ct x).symm.trans (hp _)⟩

/-- A retraction makes the standard inclusion injective on all finite tuples. -/
theorem intCast_tuple_injective (ct : R →+* ℤ) :
    Function.Injective (fun x : Fin n → ℤ => fun j => (x j : R)) := by
  intro x y he
  funext j
  have hj := congrArg ct (congrFun he j)
  simpa only [map_intCast, Int.cast_id] using hj

/-- Taking the integer trace of the standard image recovers precisely the original set. -/
theorem mem_standardImage_intCast_iff (ct : R →+* ℤ) (D : Set (Fin n → ℤ)) (x : Fin n → ℤ) :
    (fun j => (x j : R)) ∈ standardImage D ↔ x ∈ D := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact intCast_tuple_injective ct he ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- A Diophantine set supported on standard tuples has an integer Diophantine presentation. -/
theorem Definable.of_standardImage (ct : R →+* ℤ) {D : Set (Fin n → ℤ)}
    (hD : Definable (standardImage D : Set (Fin n → R))) : Definable D := by
  obtain ⟨p, hp⟩ := hD.integer_trace ct
  exact ⟨p, fun x => (hp x).trans (mem_standardImage_intCast_iff ct D x)⟩

end Surreal.IntegerDiophantine
