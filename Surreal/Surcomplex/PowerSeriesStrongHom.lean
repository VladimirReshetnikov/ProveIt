import Surreal.HahnSeries.PowerSeriesSummation
import Surreal.Surcomplex.StrongEvaluation
import Surreal.Surcomplex.PowerSeriesHom

/-!
# Unique strongly additive formal evaluation

A strongly additive map preserves all source-summable families indexed in
the permitted birthday universe. Its values on constants and the formal
variable determine it: apply strong additivity to the family of monomials.
The native source-summation bridge makes this an actual Hahn notion rather
than a topology-dependent sum. A lifted natural index type keeps the
universe bound visible in the uniqueness proof.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Preservation of source-summable families in the permitted index universe. -/
def PowerSeriesStronglyAdditive (φ : PowerSeries ℝ →+* SignSequence.{u}) : Prop :=
  ∀ (ι : Type u) (f : ι → PowerSeries ℝ), HahnSeries.PowerSeriesSummable f →
    ∃ hf : StronglySummable (fun i => φ (f i)),
      φ (HahnSeries.powerSeriesSum f) = strongSum (fun i => φ (f i)) hf

/-- Canonical evaluation preserves every permitted source strong sum. -/
theorem powerSeriesEvaluation_stronglyAdditive (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    PowerSeriesStronglyAdditive (powerSeriesEvaluation x hx) := by
  intro ι f hf
  exact ⟨stronglySummable_powerSeriesEvaluation x hx f hf,
    powerSeriesEvaluation_powerSeriesSum x hx f hf⟩

/-- The variable and ordinary coefficients uniquely determine a strongly additive map. -/
theorem powerSeriesHom_eq_of_stronglyAdditive (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (φ : PowerSeries ℝ →+* SignSequence.{u}) (hX : φ PowerSeries.X = x)
    (hC : ∀ c, φ (PowerSeries.C c) = ofReal c) (hφ : PowerSeriesStronglyAdditive φ) :
    φ = powerSeriesEvaluation x hx := by
  apply RingHom.ext
  intro F
  let f : ULift.{u} ℕ → PowerSeries ℝ :=
    fun n => PowerSeries.monomial n.down (F.coeff n.down)
  have hf : HahnSeries.PowerSeriesSummable f :=
    (HahnSeries.powerSeriesSummable_monomials F).reindex Equiv.ulift
  have hs : HahnSeries.powerSeriesSum f = F :=
    (HahnSeries.powerSeriesSum_reindex
      (fun n => PowerSeries.monomial n (F.coeff n)) Equiv.ulift).trans
      (HahnSeries.powerSeriesSum_monomials F)
  obtain ⟨hφf, hsum⟩ := hφ (ULift.{u} ℕ) f hf
  have heval := powerSeriesEvaluation_powerSeriesSum x hx f hf
  rw [hs] at hsum heval
  have ht : (fun n => φ (f n)) = (fun n => powerSeriesEvaluation x hx (f n)) := by
    funext n
    simp only [f, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow,
      hC, hX, powerSeriesEvaluation_C, powerSeriesEvaluation_X]
  calc
    φ F = strongSum (fun n => φ (f n)) hφf := hsum
    _ = strongSum (fun n => powerSeriesEvaluation x hx (f n))
        (stronglySummable_powerSeriesEvaluation x hx f hf) := by congr 1
    _ = powerSeriesEvaluation x hx F := heval.symm

/-- Canonical evaluation is the unique coefficient-fixing strongly additive homomorphism
with the specified infinitesimal variable image. -/
theorem existsUnique_powerSeriesStrongHom (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    ∃! φ : PowerSeries ℝ →+* SignSequence.{u},
      φ PowerSeries.X = x ∧ (∀ c, φ (PowerSeries.C c) = ofReal c) ∧
        PowerSeriesStronglyAdditive φ := by
  refine ⟨powerSeriesEvaluation x hx,
    ⟨powerSeriesEvaluation_X x hx, powerSeriesEvaluation_C x hx,
      powerSeriesEvaluation_stronglyAdditive x hx⟩, ?_⟩
  intro φ hφ
  exact powerSeriesHom_eq_of_stronglyAdditive x hx φ hφ.1 hφ.2.1 hφ.2.2

/-- The strongly additive clause of `thm:exact`, including the zero argument. -/
theorem exists_powerSeriesStrongHom_iff (x : SignSequence.{u}) :
    (∃ φ : PowerSeries ℝ →+* SignSequence.{u},
      φ PowerSeries.X = x ∧ (∀ c, φ (PowerSeries.C c) = ofReal c) ∧
        PowerSeriesStronglyAdditive φ) ↔ IsInfinitesimal x := by
  constructor
  · rintro ⟨φ, hX, _, _⟩
    rw [← hX]
    exact isInfinitesimal_map_powerSeries_X φ
  · intro hx
    exact (existsUnique_powerSeriesStrongHom x hx).exists

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Preservation of source-summable families in the permitted index universe. -/
def PowerSeriesStronglyAdditive (φ : PowerSeries ℂ →+* Surcomplex.{u}) : Prop :=
  ∀ (ι : Type u) (f : ι → PowerSeries ℂ), HahnSeries.PowerSeriesSummable f →
    ∃ hf : StronglySummable (fun i => φ (f i)),
      φ (HahnSeries.powerSeriesSum f) = strongSum (fun i => φ (f i)) hf

/-- Canonical evaluation preserves every permitted source strong sum. -/
theorem powerSeriesEvaluation_stronglyAdditive (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    PowerSeriesStronglyAdditive (powerSeriesEvaluation x hx) := by
  intro ι f hf
  exact ⟨stronglySummable_powerSeriesEvaluation x hx f hf,
    powerSeriesEvaluation_powerSeriesSum x hx f hf⟩

/-- The variable and ordinary coefficients uniquely determine a strongly additive map. -/
theorem powerSeriesHom_eq_of_stronglyAdditive (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (φ : PowerSeries ℂ →+* Surcomplex.{u}) (hX : φ PowerSeries.X = x)
    (hC : ∀ c, φ (PowerSeries.C c) = ofComplex c) (hφ : PowerSeriesStronglyAdditive φ) :
    φ = powerSeriesEvaluation x hx := by
  apply RingHom.ext
  intro F
  let f : ULift.{u} ℕ → PowerSeries ℂ :=
    fun n => PowerSeries.monomial n.down (F.coeff n.down)
  have hf : HahnSeries.PowerSeriesSummable f :=
    (HahnSeries.powerSeriesSummable_monomials F).reindex Equiv.ulift
  have hs : HahnSeries.powerSeriesSum f = F :=
    (HahnSeries.powerSeriesSum_reindex
      (fun n => PowerSeries.monomial n (F.coeff n)) Equiv.ulift).trans
      (HahnSeries.powerSeriesSum_monomials F)
  obtain ⟨hφf, hsum⟩ := hφ (ULift.{u} ℕ) f hf
  have heval := powerSeriesEvaluation_powerSeriesSum x hx f hf
  rw [hs] at hsum heval
  have ht : (fun n => φ (f n)) = (fun n => powerSeriesEvaluation x hx (f n)) := by
    funext n
    simp only [f, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow,
      hC, hX, powerSeriesEvaluation_C, powerSeriesEvaluation_X]
  calc
    φ F = strongSum (fun n => φ (f n)) hφf := hsum
    _ = strongSum (fun n => powerSeriesEvaluation x hx (f n))
        (stronglySummable_powerSeriesEvaluation x hx f hf) := by congr 1
    _ = powerSeriesEvaluation x hx F := heval.symm

/-- Canonical evaluation is the unique coefficient-fixing strongly additive homomorphism
with the specified infinitesimal variable image. -/
theorem existsUnique_powerSeriesStrongHom (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    ∃! φ : PowerSeries ℂ →+* Surcomplex.{u},
      φ PowerSeries.X = x ∧ (∀ c, φ (PowerSeries.C c) = ofComplex c) ∧
        PowerSeriesStronglyAdditive φ := by
  refine ⟨powerSeriesEvaluation x hx,
    ⟨powerSeriesEvaluation_X x hx, powerSeriesEvaluation_C x hx,
      powerSeriesEvaluation_stronglyAdditive x hx⟩, ?_⟩
  intro φ hφ
  exact powerSeriesHom_eq_of_stronglyAdditive x hx φ hφ.1 hφ.2.1 hφ.2.2

end
end Surreal.Surcomplex
