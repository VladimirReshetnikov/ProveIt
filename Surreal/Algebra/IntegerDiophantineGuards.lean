import Surreal.Algebra.IntegerDiophantineSystems
import Surreal.Algebra.DiophantineConstants
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite polynomial guards for standard-supported Diophantine sets

The standardness-guard construction in `odg:def:thm:ce`. Finite polynomial
systems are reindexed by Mathlib's finite equivalences, then the integer
guard is imposed on each free coordinate, leaving the original witnesses
unrestricted.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Package polynomial equations with arbitrary finite index types as a native finite system. -/
def System.ofFinite {ν ε : Type*} [Fintype ν] [Fintype ε]
    (p : ε → MvPolynomial (Fin n ⊕ ν) ℤ) : System n where
  witnesses := Fintype.card ν
  equations := Fintype.card ε
  polynomial j := rename (Sum.map id (Fintype.equivFin ν))
    (p ((Fintype.equivFin ε).symm j))

/-- Finite reindexing preserves the exact existential solution condition. -/
theorem System.holds_ofFinite_iff {ν ε : Type*} [Fintype ν] [Fintype ε]
    (p : ε → MvPolynomial (Fin n ⊕ ν) ℤ) (x : Fin n → R) :
    (ofFinite p).Holds x ↔ ∃ y : ν → R,
      ∀ j, (p j).eval₂ (Int.castRingHom R) (Sum.elim x y) = 0 := by
  have he (y : Fin (Fintype.card ν) → R) (j : ε) :
      (rename (Sum.map id (Fintype.equivFin ν)) (p j)).eval₂ (Int.castRingHom R)
        (Sum.elim x y) = (p j).eval₂ (Int.castRingHom R)
          (Sum.elim x (y ∘ Fintype.equivFin ν)) := by
    rw [eval₂_rename, Sum.elim_comp_map, Function.comp_id]
  simp only [System.Holds, ofFinite]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ Fintype.equivFin ν, fun j => ?_⟩
    have h := hy (Fintype.equivFin ε j)
    change (rename _ (p ((Fintype.equivFin ε).symm (Fintype.equivFin ε j)))).eval₂ _ _ = 0 at h
    simpa only [Equiv.symm_apply_apply, he] using h
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ (Fintype.equivFin ν).symm, fun j => ?_⟩
    change (rename _ (p ((Fintype.equivFin ε).symm j))).eval₂ _ _ = 0
    rw [he]
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using
      hy ((Fintype.equivFin ε).symm j)

/-- The original equations and one guard copy per free coordinate, with disjoint witnesses. -/
def System.guarded (p : System n) (g : System 1) : System n :=
  System.ofFinite (ν := Fin p.witnesses ⊕ (Fin n × Fin g.witnesses))
    (ε := Fin p.equations ⊕ (Fin n × Fin g.equations))
    (Sum.elim
      (fun j => rename (Sum.map id Sum.inl) (p.polynomial j))
      (fun j => rename (Sum.elim (fun _ => Sum.inl j.1)
        (fun w => Sum.inr (Sum.inr (j.1, w)))) (g.polynomial j.2)))

/-- The guard construction adds one disjoint witness tuple per free coordinate. -/
@[simp] theorem System.guarded_witnesses (p : System n) (g : System 1) :
    (p.guarded g).witnesses = p.witnesses + n * g.witnesses := by
  simp [System.guarded, System.ofFinite]

/-- The guard construction adds one finite equation family per free coordinate. -/
@[simp] theorem System.guarded_equations (p : System n) (g : System 1) :
    (p.guarded g).equations = p.equations + n * g.equations := by
  simp [System.guarded, System.ofFinite]

/-- Guarding a finite system adds exactly the coordinate guard conditions. -/
theorem System.holds_guarded_iff (p : System n) (g : System 1) (x : Fin n → R) :
    (p.guarded g).Holds x ↔ p.Holds x ∧ ∀ j, g.Holds (fun _ => x j) := by
  rw [guarded, holds_ofFinite_iff]
  have hleft (y : Fin p.witnesses ⊕ (Fin n × Fin g.witnesses) → R) :
      Sum.elim x y ∘ Sum.map id Sum.inl = Sum.elim x (fun w => y (Sum.inl w)) := by
    funext v
    cases v <;> rfl
  have hright (y : Fin p.witnesses ⊕ (Fin n × Fin g.witnesses) → R) (j : Fin n) :
      Sum.elim x y ∘ Sum.elim (fun _ : Fin 1 => Sum.inl j)
        (fun w => Sum.inr (Sum.inr (j, w))) =
      Sum.elim (fun _ => x j) (fun w => y (Sum.inr (j, w))) := by
    funext v
    cases v <;> rfl
  simp only [Sum.forall, Prod.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename, hleft, hright]
  constructor
  · rintro ⟨y, hp, hg⟩
    refine ⟨⟨fun w => y (Sum.inl w), ?_⟩, fun j => ⟨fun w => y (Sum.inr (j, w)), ?_⟩⟩
    · exact hp
    · exact hg j
  · rintro ⟨⟨y, hy⟩, hg⟩
    choose z hz using hg
    exact ⟨Sum.elim y (fun j => z j.1 j.2), hy, hz⟩

/-- The existing three-equation, five-witness integer guard as a finite polynomial system. -/
abbrev integerGuard : System 1 where
  witnesses := 5
  equations := 3
  polynomial :=
    let x : MvPolynomial (Fin 1 ⊕ Fin 5) ℤ := X (Sum.inl 0)
    let v (j : Fin 5) : MvPolynomial (Fin 1 ⊕ Fin 5) ℤ := X (Sum.inr j)
    ![x * (v 0 ^ 2 - 2 * v 1 ^ 2 - 1), x * (v 1 - x * v 2),
      x * (v 1 * v 3 - IntersectivePolynomial.value (v 4))]

/-- Polynomial guard solvability is exactly the previously proved Xi predicate. -/
theorem holds_integerGuard_iff (x : Fin 1 → R) :
    integerGuard.Holds x ↔ DiophantineConstants.Xi (x 0) := by
  have he (y : Fin 5 → R) :
      (∀ j, (integerGuard.polynomial j).eval₂ (Int.castRingHom R) (Sum.elim x y) = 0) ↔
        DiophantineConstants.System (x 0) (y 0) (y 1) (y 2) (y 3) (y 4) := by
    simp [integerGuard, Fin.forall_fin_succ, DiophantineConstants.System,
      IntersectivePolynomial.value]
  change (∃ y : Fin 5 → R, ∀ j : Fin 3,
    (integerGuard.polynomial j).eval₂ (Int.castRingHom R) (Sum.elim x y) = 0) ↔ _
  simp only [he]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y 0, y 1, y 2, y 3, y 4, hy⟩
  · rintro ⟨u, v, w, s, t, h⟩
    exact ⟨![u, v, w, s, t], h⟩

/-- A proved integer guard lifts each integer Diophantine presentation to its standard image. -/
theorem System.guarded_standardImage_iff (p : System n) (g : System 1) (ct : R →+* ℤ)
    (hg : ∀ x : R, g.Holds (fun _ => x) ↔ ∃ z : ℤ, x = (z : R)) (x : Fin n → R) :
    (p.guarded g).Holds x ↔ x ∈ standardImage {z : Fin n → ℤ | p.Holds z} := by
  rw [System.holds_guarded_iff]
  constructor
  · rintro ⟨hp, hx⟩
    have hstd : ∀ j, ∃ z : ℤ, x j = (z : R) := fun j => (hg (x j)).mp (hx j)
    choose z hz using hstd
    have he : (fun j => (z j : R)) = x := funext (fun j => (hz j).symm)
    exact ⟨z, (p.holds_intCast_iff ct z).mp (he.symm ▸ hp), he⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(p.holds_intCast_iff ct z).mpr hz, fun j => (hg _).mpr ⟨z j, rfl⟩⟩

/-- Finite polynomial guards give the reverse transfer for standard-supported definitions. -/
theorem Definable.standardImage (ct : R →+* ℤ) (g : System 1)
    (hg : ∀ x : R, g.Holds (fun _ => x) ↔ ∃ z : ℤ, x = (z : R))
    {D : Set (Fin n → ℤ)} (hD : Definable D) : Definable (standardImage D : Set (Fin n → R)) := by
  obtain ⟨p, hp⟩ := hD
  refine ⟨p.guarded g, fun x => ?_⟩
  rw [p.guarded_standardImage_iff g ct hg]
  exact exists_congr (fun z => and_congr (hp z) Iff.rfl)

/-- Integer and standard-supported Diophantine definability agree once the guard is available. -/
theorem standardImage_definable_iff (ct : R →+* ℤ) (g : System 1)
    (hg : ∀ x : R, g.Holds (fun _ => x) ↔ ∃ z : ℤ, x = (z : R))
    (D : Set (Fin n → ℤ)) : Definable (standardImage D : Set (Fin n → R)) ↔ Definable D :=
  ⟨fun h => h.of_standardImage ct, fun h => h.standardImage ct g hg⟩

end
end Surreal.IntegerDiophantine
