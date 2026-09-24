import Surreal.Algebra.NaturalDiophantineBridge
import Surreal.Algebra.QuinticConstants

/-!
# Natural Diophantine sets as integer Diophantine sets

The four-square conversion needed for the integer form of MRDP in
`odg:def:thm:ce`. Natural free coordinates and witnesses are represented by
nonnegative integers, with finite four-square certificates. This does not
assume the still separate computable-enumerability converse.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

variable {n : ℕ}

/-- The natural-coordinate image inside ordinary integer tuples. -/
def naturalImage (D : Set (Fin n → ℕ)) : Set (Fin n → ℤ) :=
  {x | ∃ z ∈ D, (fun j => (z j : ℤ)) = x}

/-- Add four-square certificates for every free and witness coordinate. -/
def System.naturalToInteger (p : System n) : System n :=
  System.ofFinite (ν := Fin p.witnesses ⊕ ((Fin n ⊕ Fin p.witnesses) × Fin 4))
    (ε := Fin p.equations ⊕ (Fin n ⊕ Fin p.witnesses))
    (Sum.elim
      (fun j => rename (Sum.map id Sum.inl) (p.polynomial j))
      (fun v => (Sum.elim (fun j => X (Sum.inl j)) (fun w => X (Sum.inr (Sum.inl w))) v) -
        ∑ k : Fin 4, X (Sum.inr (Sum.inr (v, k))) ^ 2))

/-- Four-square certificates impose exactly nonnegativity of all coordinates. -/
theorem System.holds_naturalToInteger_iff_nonneg (p : System n) (x : Fin n → ℤ) :
    p.naturalToInteger.Holds x ↔ ∃ y : Fin p.witnesses → ℤ,
      (∀ j, (p.polynomial j).eval (Sum.elim x y) = 0) ∧
      ∀ v, 0 ≤ Sum.elim x y v := by
  classical
  rw [naturalToInteger, holds_ofFinite_iff]
  have hc : Int.castRingHom ℤ = RingHom.id ℤ := Subsingleton.elim _ _
  have he (z : Fin p.witnesses ⊕ ((Fin n ⊕ Fin p.witnesses) × Fin 4) → ℤ) :
      Sum.elim x z ∘ Sum.map id Sum.inl = Sum.elim x (fun w => z (Sum.inl w)) := by
    funext v
    cases v <;> rfl
  simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename, he,
    eval₂_sub, eval₂_X, eval₂_sum, eval₂_pow, sub_eq_zero]
  constructor
  · rintro ⟨z, hp, hx, hy⟩
    refine ⟨fun w => z (Sum.inl w), ?_, ?_, ?_⟩
    · simpa only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hc] using hp
    · intro j
      rw [hx j]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · intro j
      change (0 : ℤ) ≤ z (Sum.inl j)
      rw [hy j]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · rintro ⟨y, hy, hx, hw⟩
    have hn : ∀ v, 0 ≤ Sum.elim x y v := by
      intro v
      cases v with
      | inl j => exact hx j
      | inr j => exact hw j
    have hs : ∀ v, ∃ s : Fin 4 → ℤ, ∑ k, s k ^ 2 = Sum.elim x y v :=
      fun v => QuinticConstants.integer_four_squares _ (hn v)
    choose s hs using hs
    refine ⟨Sum.elim y (fun w => s w.1 w.2), ?_,
      fun j => (hs (Sum.inl j)).symm, fun j => (hs (Sum.inr j)).symm⟩
    simpa only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hc, Sum.elim_inl] using hy

/-- The integer system defines precisely the image of the original natural solution set. -/
theorem System.holds_naturalToInteger_iff (p : System n) (x : Fin n → ℤ) :
    p.naturalToInteger.Holds x ↔ x ∈ naturalImage {z : Fin n → ℕ | p.HoldsNat z} := by
  rw [p.holds_naturalToInteger_iff_nonneg]
  constructor
  · rintro ⟨y, hy, hn⟩
    let a : Fin n → ℕ := fun j => (x j).toNat
    let b : Fin p.witnesses → ℕ := fun j => (y j).toNat
    have ha : (fun j => (a j : ℤ)) = x := by
      funext j
      exact Int.toNat_of_nonneg (hn (Sum.inl j))
    have hb : (fun j => (b j : ℤ)) = y := by
      funext j
      exact Int.toNat_of_nonneg (hn (Sum.inr j))
    refine ⟨a, ⟨b, fun j => ?_⟩, ha⟩
    have hv : (fun v => ((Sum.elim a b v : ℕ) : ℤ)) = Sum.elim x y := by
      funext v
      cases v with
      | inl j => exact congrFun ha j
      | inr j => exact congrFun hb j
    rw [hv]
    exact hy j
  · rintro ⟨a, ⟨b, hb⟩, rfl⟩
    refine ⟨fun j => (b j : ℤ), ?_, ?_⟩
    · have hv : (fun v => ((Sum.elim a b v : ℕ) : ℤ)) =
          Sum.elim (fun j => (a j : ℤ)) (fun j => (b j : ℤ)) := by
        funext v
        cases v <;> rfl
      simpa only [hv] using hb
    · intro v
      cases v <;> exact Int.natCast_nonneg _

/-- Any finite natural Diophantine definition becomes an integer Diophantine definition of its image. -/
theorem NatDefinable.naturalImage {D : Set (Fin n → ℕ)} (hD : NatDefinable D) :
    Definable (naturalImage D) := by
  obtain ⟨p, hp⟩ := hD
  refine ⟨p.naturalToInteger, fun x => ?_⟩
  rw [p.holds_naturalToInteger_iff]
  exact exists_congr (fun z => and_congr (hp z) Iff.rfl)

/-- Every existing Mathlib Diophantine result transfers to a finite integer system. -/
theorem naturalImage_definable_of_dioph {D : Set (Fin n → ℕ)} (hD : Dioph D) :
    Definable (naturalImage D) :=
  ((natDefinable_iff_dioph D).mpr hD).naturalImage

/-- The graph of ordinary natural exponentiation has a finite integer polynomial presentation. -/
theorem natural_power_integer_graph_definable :
    Definable (naturalImage {x : Fin 3 → ℕ | x 0 ^ x 1 = x 2}) :=
  nat_power_graph_definable.naturalImage

end
end Surreal.IntegerDiophantine
