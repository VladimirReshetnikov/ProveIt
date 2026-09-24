import Surreal.Foundations.OmnificSupportBounds
import Surreal.Algebra.HomogeneousScaling
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective omnific coordinates and small-family common multiples

The full assertions `odg:cor:projectiveclear` and `odg:cor:commonmultiples`.
One positive Conway monomial clears a small family of coordinate tuples,
including tuples of different dimensions. Homogeneous equations survive
this rescaling, and actual projective points acquire purely infinite
omnific representatives. A second application clears all reciprocal
powers of a small family of nonzero omnific integers simultaneously.
-/

universe u v w
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A single positive monomial clears every coordinate in a small family of tuples. -/
theorem omnific_coordinate_clearing {ι : Type v} {κ : ι → Type w}
    [Small.{u} ι] [∀ i, Small.{u} (κ i)] (x : ∀ i, κ i → SignSequence.{u}) :
    ∃ (h : SignSequence.{u}) (_ : 0 < h) (z : ∀ i, κ i → OmnificInteger.{u}),
      (∀ i j, z i j ∈ omnificPurelyInfiniteIdeal) ∧
      ∀ i j, omnificToSurreal (z i j) = omegaPower h * x i j := by
  obtain ⟨h, hh, hz⟩ := omnific_monomial_clearing (fun a : Sigma κ => x a.1 a.2)
  choose z hzi hze using hz
  exact ⟨h, hh, fun i j => z ⟨i, j⟩, fun i j => hzi ⟨i, j⟩, fun i j => hze ⟨i, j⟩⟩

/-- Clearing coordinates preserves every homogeneous equation satisfied by each tuple. -/
theorem omnific_coordinate_clearing_homogeneous {ι : Type v} {κ : ι → Type w}
    [Small.{u} ι] [∀ i, Small.{u} (κ i)] (x : ∀ i, κ i → SignSequence.{u}) :
    ∃ (h : SignSequence.{u}) (_ : 0 < h) (z : ∀ i, κ i → OmnificInteger.{u}),
      (∀ i j, z i j ∈ omnificPurelyInfiniteIdeal) ∧
      (∀ i j, omnificToSurreal (z i j) = omegaPower h * x i j) ∧
      ∀ i (p : MvPolynomial (κ i) SignSequence.{u}) (d : ℕ), p.IsHomogeneous d →
        p.eval (x i) = 0 → p.eval (fun j => omnificToSurreal (z i j)) = 0 := by
  obtain ⟨h, hh, z, hz, he⟩ := omnific_coordinate_clearing x
  refine ⟨h, hh, z, hz, he, fun i p d hp hx => ?_⟩
  simp only [he]
  exact Surreal.homogeneous_eval_mul_eq_zero hp (omegaPower h) hx

/-- Every actual surreal projective point has purely infinite omnific coordinates. -/
theorem omnific_projective_representative {σ : Type v} [Small.{u} σ]
    (p : Projectivization SignSequence.{u} (σ → SignSequence.{u})) :
    ∃ (z : σ → OmnificInteger.{u}) (hz : (fun j => omnificToSurreal (z j)) ≠ 0),
      (∀ j, z j ∈ omnificPurelyInfiniteIdeal) ∧
      Projectivization.mk SignSequence (fun j => omnificToSurreal (z j)) hz = p := by
  obtain ⟨h, hh, hz⟩ := omnific_monomial_clearing p.rep
  choose z hzi hze using hz
  have he : (fun j => omnificToSurreal (z j)) = omegaPower h • p.rep := by
    funext j
    exact hze j
  have hn : (fun j => omnificToSurreal (z j)) ≠ 0 := by
    rw [he]
    exact smul_ne_zero (omegaPower_ne_zero h) p.rep_nonzero
  refine ⟨z, hn, hzi, ?_⟩
  rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr ⟨omegaPower h, he.symm⟩

/-- One nonzero monomial is divisible by every ordinary power in a small nonzero family,
with all the quotients purely infinite. This includes the zeroth powers. -/
theorem omnific_common_multiple_all_powers {ι : Type v} [Small.{u} ι]
    (a : ι → OmnificInteger.{u}) (ha : ∀ i, a i ≠ 0) :
    ∃ (h : SignSequence.{u}) (hh : 0 < h),
      omnificMonomial h hh ≠ 0 ∧ ∀ i (k : ℕ), ∃ q ∈ omnificPurelyInfiniteIdeal,
        omnificMonomial h hh = a i ^ k * q := by
  obtain ⟨h, hh, hz⟩ := omnific_monomial_clearing
    (fun t : ι × ℕ => (omnificToSurreal (a t.1) ^ t.2)⁻¹)
  refine ⟨h, hh, omnificMonomial_ne_zero h hh, fun i k => ?_⟩
  obtain ⟨q, hq, he⟩ := hz (i, k)
  refine ⟨q, hq, omnificToSurreal_injective ?_⟩
  have hn : omnificToSurreal (a i) ^ k ≠ 0 :=
    pow_ne_zero _ (fun e => ha i (omnificToSurreal_injective (by simpa using e)))
  rw [omnificToSurreal_monomial, map_mul, map_pow, he]
  rw [mul_left_comm, mul_inv_cancel₀ hn, mul_one]

/-- Every small set of nonzero omnific integers has a nonzero common multiple of all powers. -/
theorem omnific_set_common_multiple (S : Set OmnificInteger.{u}) [Small.{u} S]
    (hS : ∀ a ∈ S, a ≠ 0) :
    ∃ M : OmnificInteger.{u}, M ≠ 0 ∧ M ∈ omnificPurelyInfiniteIdeal ∧
      ∀ a ∈ S, ∀ k : ℕ, a ^ k ∣ M := by
  obtain ⟨h, hh, hn, hm⟩ := omnific_common_multiple_all_powers
    (fun a : S => a.val) (fun a => hS a.val a.property)
  refine ⟨omnificMonomial h hh, hn, omnificMonomial_mem_purelyInfinite h hh, ?_⟩
  intro a ha k
  obtain ⟨q, _, hq⟩ := hm ⟨a, ha⟩ k
  exact ⟨q, hq⟩

end
end Surreal.Foundations.SignSequence
