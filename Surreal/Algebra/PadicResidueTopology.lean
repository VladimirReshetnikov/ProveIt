import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Residue neighborhoods in the usual p-adic topology

Prerequisites for the p-adic topological isomorphism in `odg:eq:profinite`.
The metric topology on Mathlib's p-adic integers is determined by its
prime-power residues. This compares the existing metric topology with
inverse-limit and ideal-adic constructions without transporting a topology
along a ring isomorphism.
-/

namespace Surreal.PadicResidueTopology

open Topology

variable (p : ℕ) [Fact p.Prime]

/-- Equality of one residue is exactly a closed p-adic ball. -/
theorem residue_eq_iff (n : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow n y = PadicInt.toZModPow n x ↔
      dist y x ≤ ((p : ℝ)⁻¹) ^ n := by
  rw [dist_eq_norm, inv_pow, ← zpow_natCast, ← zpow_neg,
    PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]

/-- Congruence classes modulo prime powers form a basis of the metric neighborhoods. -/
theorem hasBasis_nhds (x : ℤ_[p]) :
    (𝓝 x).HasBasis (fun _ : ℕ => True)
      (fun n => {y | PadicInt.toZModPow n y = PadicInt.toZModPow n x}) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  apply (Metric.nhds_basis_closedBall_pow (inv_pos.mpr (lt_trans zero_lt_one hp))
    (inv_lt_one_of_one_lt₀ hp)).congr (fun _ => Iff.rfl)
  intro n _
  ext y
  exact (residue_eq_iff p n x y).symm

/-- The ordinary ideal-adic topology on integers is induced by their p-adic embedding. -/
theorem isInducing_intCast :
    @IsInducing ℤ ℤ_[p] (Ideal.span {(p : ℤ)}).adicTopology inferInstance Int.cast := by
  letI := (Ideal.span {(p : ℤ)}).adicTopology
  apply isInducing_iff_nhds.mpr
  intro x
  apply ((Ideal.span {(p : ℤ)}).hasBasis_nhds_adic x).eq_of_same_basis
  apply ((hasBasis_nhds p (x : ℤ_[p])).comap (Int.cast : ℤ → ℤ_[p])).congr
    (fun _ => Iff.rfl)
  intro n _
  ext y
  change PadicInt.toZModPow n (y : ℤ_[p]) = PadicInt.toZModPow n (x : ℤ_[p]) ↔ _
  rw [map_intCast, map_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [Nat.cast_pow]
  rw [dvd_sub_comm]
  constructor
  · intro hy
    refine ⟨y - x, ?_, add_sub_cancel _ _⟩
    change y - x ∈ (Ideal.span {(p : ℤ)}) ^ n
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  · rintro ⟨z, hz, rfl⟩
    change (p : ℤ) ^ n ∣ x + z - x
    rw [add_sub_cancel_left]
    change z ∈ (Ideal.span {(p : ℤ)}) ^ n at hz
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz

end Surreal.PadicResidueTopology
