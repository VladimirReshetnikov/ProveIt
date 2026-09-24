import Surreal.Algebra.MathlibDiophantinePolynomials
import Surreal.Algebra.IntegerDiophantineGuards

/-!
# Finite natural Diophantine systems and Mathlib's Dioph

The arithmetic-library bridge for the remaining MRDP step of
`odg:def:thm:ce`. Integer-coefficient polynomials are evaluated on natural
free and witness tuples, cast into Z. The equivalence preserves the full
solution set and eliminates unused witnesses of arbitrary original types.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

/-- Natural-witness solvability for the same native integer-polynomial system. -/
def System.HoldsNat {n : ℕ} (p : System n) (x : Fin n → ℕ) : Prop :=
  ∃ y : Fin p.witnesses → ℕ,
    ∀ j, (p.polynomial j).eval (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = 0

/-- Finite integer-polynomial Diophantine definability over the natural numbers. -/
def NatDefinable {n : ℕ} (D : Set (Fin n → ℕ)) : Prop :=
  ∃ p : System n, ∀ x, p.HoldsNat x ↔ x ∈ D

/-- Reindexing arbitrary finite witness types preserves natural-witness solvability. -/
theorem System.holdsNat_ofFinite_iff {n : ℕ} {ν ε : Type*} [Fintype ν] [Fintype ε]
    (p : ε → MvPolynomial (Fin n ⊕ ν) ℤ) (x : Fin n → ℕ) :
    (ofFinite p).HoldsNat x ↔ ∃ y : ν → ℕ,
      ∀ j, (p j).eval (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = 0 := by
  have he (y : Fin (Fintype.card ν) → ℕ) (j : ε) :
      (rename (Sum.map id (Fintype.equivFin ν)) (p j)).eval
        (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = (p j).eval
          (fun v => ((Sum.elim x (y ∘ Fintype.equivFin ν) v : ℕ) : ℤ)) := by
    rw [eval_rename]
    apply congrArg (fun z => (p j).eval z)
    funext v
    cases v <;> rfl
  change (∃ y : Fin (Fintype.card ν) → ℕ, ∀ j : Fin (Fintype.card ε),
    (rename (Sum.map id (Fintype.equivFin ν)) (p ((Fintype.equivFin ε).symm j))).eval
      (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = 0) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ Fintype.equivFin ν, fun j => ?_⟩
    have h := hy (Fintype.equivFin ε j)
    simpa only [Equiv.symm_apply_apply, he] using h
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ (Fintype.equivFin ν).symm, fun j => ?_⟩
    rw [he]
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using
      hy ((Fintype.equivFin ε).symm j)

/-- Every Mathlib Diophantine set has a finite native single-equation presentation. -/
theorem exists_singleEquation_of_dioph {n : ℕ} {D : Set (Fin n → ℕ)} (hD : Dioph D) :
    ∃ p : System n, p.equations = 1 ∧ ∀ x, p.HoldsNat x ↔ x ∈ D := by
  classical
  obtain ⟨β, f, hf⟩ := hD
  obtain ⟨p, hp⟩ := MathlibDiophantine.exists_mvPolynomial f.isPoly
  obtain ⟨s, q, hq⟩ := MathlibDiophantine.exists_finite_witness_polynomial p
  refine ⟨System.ofFinite (fun _ : Fin 1 => q), by simp [System.ofFinite], fun x => ?_⟩
  rw [System.holdsNat_ofFinite_iff]
  simp only [Fin.forall_fin_one]
  rw [← MathlibDiophantine.finite_witness_solvability s q x, hq, hf]
  exact exists_congr (fun y => by rw [hp])

/-- A finite native system is a Mathlib Diophantine presentation after summing squares. -/
theorem NatDefinable.dioph {n : ℕ} {D : Set (Fin n → ℕ)} (hD : NatDefinable D) : Dioph D := by
  obtain ⟨p, hp⟩ := hD
  let q : MvPolynomial (Fin n ⊕ Fin p.witnesses) ℤ := ∑ j, p.polynomial j ^ 2
  refine ⟨Fin p.witnesses,
    ⟨fun v => q.eval (fun j => (v j : ℤ)), MathlibDiophantine.isPoly_eval q⟩, fun x => ?_⟩
  rw [← hp x]
  change (∃ y : Fin p.witnesses → ℕ, ∀ j, _) ↔ ∃ y, q.eval _ = 0
  apply exists_congr
  intro y
  symm
  simp only [q, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
    ((p.polynomial j).eval (fun v => ((Sum.elim x y v : ℕ) : ℤ))))]
  simp

/-- Mathlib's Dioph and finite native integer-polynomial systems have exactly the same natural sets. -/
theorem natDefinable_iff_dioph {n : ℕ} (D : Set (Fin n → ℕ)) : NatDefinable D ↔ Dioph D := by
  constructor
  · exact NatDefinable.dioph
  · intro h
    obtain ⟨p, _, hp⟩ := exists_singleEquation_of_dioph h
    exact ⟨p, hp⟩

/-- Reuse Mathlib's Matiyasevic theorem as a finite native polynomial presentation of exponentiation. -/
theorem nat_power_graph_definable : NatDefinable {x : Fin 3 → ℕ | x 0 ^ x 1 = x 2} := by
  apply (natDefinable_iff_dioph _).mpr
  have h := Dioph.pow_dioph (Dioph.proj_dioph (0 : Fin 2)) (Dioph.proj_dioph (1 : Fin 2))
  let e : Option (Fin 2) → Fin 3 := Option.elim' 2 Fin.castSucc
  have he := Dioph.reindex_dioph (Fin 3) e h
  exact he.ext (fun x => by rfl)

end
end Surreal.IntegerDiophantine
