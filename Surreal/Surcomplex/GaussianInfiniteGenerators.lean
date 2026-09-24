import Surreal.Surcomplex.GaussianPrincipalGrowth

/-!
# The Gaussian infinite ideal has no small generating set

The actual Gaussian instances of `osq:prop:common`(ii)-(iv), used in
`osq:prop:principal`. The common real monomial divisor of a small family
cannot divide a positive monomial of half its exponent.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Every Gaussian purely infinite element is one product of two elements of that ideal. -/
theorem gaussianOmnific_purelyInfinite_single_product (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal.{u}) :
    ∃ a ∈ gaussianOmnificPurelyInfiniteIdeal.{u},
      ∃ b ∈ gaussianOmnificPurelyInfiniteIdeal.{u}, x = a * b := by
  obtain ⟨c, hc, h⟩ := gaussianOmnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, hq, he⟩ := h PUnit.unit
  exact ⟨omnificToGaussian (SignSequence.omnificMonomial c hc),
    omnificToGaussian_mem_purelyInfinite _ (SignSequence.omnificMonomial_mem_purelyInfinite c hc),
    q, hq, he⟩

/-- The Gaussian purely infinite ideal is idempotent. -/
theorem gaussianOmnificPurelyInfiniteIdeal_idempotent :
    IsIdempotentElem gaussianOmnificPurelyInfiniteIdeal.{u} := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := gaussianOmnific_purelyInfinite_single_product x hx
  exact Ideal.mul_mem_mul ha hb

/-- No birthday-universe-small family generates the Gaussian purely infinite ideal. -/
theorem gaussianOmnificPurelyInfiniteIdeal_ne_span_small (S : Set GaussianOmnificInteger.{u})
    [Small.{u} S] : Ideal.span S ≠ gaussianOmnificPurelyInfiniteIdeal.{u} := by
  intro hS
  have hs : ∀ x : S, x.val ∈ gaussianOmnificPurelyInfiniteIdeal.{u} :=
    fun x => hS ▸ Ideal.subset_span x.property
  obtain ⟨c, hc, h⟩ := gaussianOmnific_common_monomial_divisor (fun x : S => x.val) hs
  have hle : Ideal.span S ≤ Ideal.span {omnificToGaussian (SignSequence.omnificMonomial c hc)} := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨q, _, he⟩ := h ⟨x, hx⟩
    exact Ideal.mem_span_singleton.mpr ⟨q, he⟩
  have hh : 0 < c / 2 := half_pos hc
  have hm := omnificToGaussian_mem_purelyInfinite _
    (SignSequence.omnificMonomial_mem_purelyInfinite (c / 2) hh)
  have hd := Ideal.mem_span_singleton.mp (hle (hS ▸ hm))
  exact (half_lt_self hc).not_ge (gaussianOmnificMonomial_le_of_dvd hc hh hd)

/-- The positive real monomial principal ideals form an upward directed family. -/
theorem gaussianOmnific_monomial_ideals_directed :
    Directed (· ≤ ·) (fun a : Set.Ioi (0 : SignSequence.{u}) =>
      Ideal.span {omnificToGaussian (SignSequence.omnificMonomial a.val a.property)}) := by
  intro a b
  let s : Bool → GaussianOmnificInteger.{u} := fun t =>
    if t then omnificToGaussian (SignSequence.omnificMonomial a.val a.property)
    else omnificToGaussian (SignSequence.omnificMonomial b.val b.property)
  have hs : ∀ t, s t ∈ gaussianOmnificPurelyInfiniteIdeal.{u} := by
    intro t
    dsimp [s]
    split_ifs <;> exact omnificToGaussian_mem_purelyInfinite _
      (SignSequence.omnificMonomial_mem_purelyInfinite _ _)
  obtain ⟨c, hc, h⟩ := gaussianOmnific_common_monomial_divisor s hs
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · obtain ⟨q, _, he⟩ := h true
    exact Ideal.span_singleton_le_span_singleton.mpr ⟨q, he⟩
  · obtain ⟨q, _, he⟩ := h false
    exact Ideal.span_singleton_le_span_singleton.mpr ⟨q, he⟩

/-- The ideal is the literal union of its positive real monomial principal ideals. -/
theorem gaussianOmnificPurelyInfiniteIdeal_eq_iUnion :
    (gaussianOmnificPurelyInfiniteIdeal.{u} : Set GaussianOmnificInteger) =
      ⋃ a : Set.Ioi (0 : SignSequence.{u}),
        (Ideal.span {omnificToGaussian (SignSequence.omnificMonomial a.val a.property)} :
          Set GaussianOmnificInteger) := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨a, ha, h⟩ := gaussianOmnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
    obtain ⟨q, _, he⟩ := h PUnit.unit
    exact ⟨⟨a, ha⟩, Ideal.mem_span_singleton.mpr ⟨q, he⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
    exact gaussianOmnificPurelyInfiniteIdeal.mul_mem_right q (omnificToGaussian_mem_purelyInfinite _
      (SignSequence.omnificMonomial_mem_purelyInfinite a.val a.property))

/-- Every nonzero Gaussian constant divides the infinite ideal without leaving that ideal. -/
theorem gaussianOmnific_purelyInfinite_constant_division (d : GaussianInt) (hd : d ≠ 0)
    (x : GaussianOmnificInteger.{u}) (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal.{u}) :
    ∃ q ∈ gaussianOmnificPurelyInfiniteIdeal.{u}, x = gaussianOmnificConstants.{u} d * q := by
  change gaussianOmnificConstantCoeff.{u} x = 0 at hx
  obtain ⟨q, he⟩ := (gaussianOmnific_constant_dvd_iff d hd x).mpr (by rw [hx]; exact dvd_zero d)
  refine ⟨q, ?_, he⟩
  change gaussianOmnificConstantCoeff.{u} q = 0
  have h := congrArg gaussianOmnificConstantCoeff.{u} he
  rw [hx, map_mul, gaussianOmnificConstantCoeff_constants] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hd

/-- Multiplication by a nonzero ordinary Gaussian constant preserves the entire infinite ideal. -/
theorem gaussianOmnific_constant_mul_purelyInfinite (d : GaussianInt) (hd : d ≠ 0) :
    Ideal.span {gaussianOmnificConstants.{u} d} * gaussianOmnificPurelyInfiniteIdeal.{u} =
      gaussianOmnificPurelyInfiniteIdeal.{u} := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨q, hq, rfl⟩ := gaussianOmnific_purelyInfinite_constant_division d hd x hx
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hq

/-- In particular this ideal is not finitely generated. -/
theorem gaussianOmnificPurelyInfiniteIdeal_not_fg : ¬ gaussianOmnificPurelyInfiniteIdeal.{u}.FG := by
  rintro ⟨S, hS⟩
  exact gaussianOmnificPurelyInfiniteIdeal_ne_span_small (S : Set GaussianOmnificInteger) hS

/-- The purely infinite ideal is nonzero. -/
theorem gaussianOmnificPurelyInfiniteIdeal_ne_bot : gaussianOmnificPurelyInfiniteIdeal.{u} ≠ ⊥ := by
  intro h
  apply gaussianOmnificPurelyInfiniteIdeal_not_fg
  rw [h]
  exact Submodule.fg_bot

end
end Surreal.Surcomplex
