import Surreal.Foundations.OmnificSupportBounds
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The idempotent, non-small-generated purely infinite ideal

The ideal and factorization assertions of `odg:cor:Pglobal` (also
`odg:cor:Jglobal`) and the nilpotent test `odg:cor:nilpotent`. The small-family
monomial theorem implies idempotence and rules out every lower-universe-small
set of ideal generators. Nilpotent tests are proved for arbitrary target
rings, without asserting that the image is an ideal of the target.
-/

universe u v
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Every purely infinite element, including zero, is a single product inside the ideal. -/
theorem omnific_purelyInfinite_single_product (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) :
    ∃ a ∈ omnificPurelyInfiniteIdeal, ∃ b ∈ omnificPurelyInfiniteIdeal, x = a * b := by
  obtain ⟨δ, hδ, h⟩ := omnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, hq, he⟩ := h PUnit.unit
  exact ⟨omnificMonomial δ hδ, omnificMonomial_mem_purelyInfinite _ _, q, hq, he⟩

/-- The purely infinite ideal is idempotent under ideal multiplication. -/
theorem omnificPurelyInfiniteIdeal_idempotent : IsIdempotentElem omnificPurelyInfiniteIdeal.{u} := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := omnific_purelyInfinite_single_product x hx
  exact Ideal.mul_mem_mul ha hb

/-- Every positive ordinary power of the purely infinite ideal is the ideal itself. -/
theorem omnificPurelyInfiniteIdeal_pow (k : ℕ) (hk : 0 < k) :
    omnificPurelyInfiniteIdeal.{u} ^ k = omnificPurelyInfiniteIdeal :=
  omnificPurelyInfiniteIdeal_idempotent.pow_eq hk.ne'

/-- The actual cotangent module `Pi / Pi²` is zero, despite `Pi` being nonzero. -/
instance omnificPurelyInfiniteCotangentSubsingleton :
    Subsingleton omnificPurelyInfiniteIdeal.{u}.Cotangent :=
  (Ideal.cotangent_subsingleton_iff _).mpr omnificPurelyInfiniteIdeal_idempotent

/-- Quotienting by any positive power of the purely infinite ideal gives ordinary integers. -/
def omnificPurelyInfinitePowerQuotientEquiv (k : ℕ) (hk : 0 < k) :
    OmnificInteger.{u} ⧸ omnificPurelyInfiniteIdeal ^ k ≃+* ℤ :=
  (Ideal.quotEquivOfEq (omnificPurelyInfiniteIdeal_pow k hk)).trans omnificQuotientEquiv

/-- Each positive-power quotient map is exactly integer constant extraction. -/
@[simp] theorem omnificPurelyInfinitePowerQuotientEquiv_mk (k : ℕ) (hk : 0 < k)
    (x : OmnificInteger.{u}) :
    omnificPurelyInfinitePowerQuotientEquiv k hk (Ideal.Quotient.mk _ x) =
      omnificConstantCoeff x := by
  simp only [omnificPurelyInfinitePowerQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, omnificQuotientEquiv]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk omnificConstantCoeff_surjective x

/-- Divisibility between positive monomials forces the same order on their growth exponents. -/
theorem omnificMonomial_le_of_dvd {a b : SignSequence.{u}} (ha : 0 < a) (hb : 0 < b)
    (h : omnificMonomial a ha ∣ omnificMonomial b hb) : a ≤ b := by
  obtain ⟨q, hq⟩ := h
  have he := congrArg omnificToSurreal hq
  rw [map_mul, omnificToSurreal_monomial, omnificToSurreal_monomial] at he
  have hq0 : omnificToSurreal q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact omegaPower_ne_zero b he
  have hdeg := nonnegativeSupport_leadingExponent_nonneg q.val hq0
  have hlead := congrArg leadingExponent he
  rw [leadingExponent_mul (omegaPower_ne_zero a) hq0,
    leadingExponent_omegaPower, leadingExponent_omegaPower] at hlead
  exact hlead ▸ le_add_of_nonneg_right hdeg

/-- No lower-universe-small set generates the purely infinite ideal. -/
theorem omnificPurelyInfiniteIdeal_ne_span_small (S : Set OmnificInteger.{u}) [Small.{u} S] :
    Ideal.span S ≠ omnificPurelyInfiniteIdeal := by
  intro hS
  have hs : ∀ x : S, x.val ∈ omnificPurelyInfiniteIdeal := fun x =>
    hS ▸ Ideal.subset_span x.property
  obtain ⟨δ, hδ, h⟩ := omnific_common_monomial_divisor (fun x : S => x.val) hs
  have hle : Ideal.span S ≤ Ideal.span {omnificMonomial δ hδ} := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨q, _, hq⟩ := h ⟨x, hx⟩
    exact Ideal.mem_span_singleton.mpr ⟨q, hq⟩
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hdvd : omnificMonomial δ hδ ∣ omnificMonomial (δ / 2) hhalf :=
    Ideal.mem_span_singleton.mp (hle (hS ▸ omnificMonomial_mem_purelyInfinite _ _))
  exact (not_le_of_gt (half_lt_self hδ)) (omnificMonomial_le_of_dvd hδ hhalf hdvd)

/-- In particular, the purely infinite ideal is not finitely generated. -/
theorem omnificPurelyInfiniteIdeal_not_fg : ¬ omnificPurelyInfiniteIdeal.{u}.FG := by
  rintro ⟨S, hS⟩
  exact omnificPurelyInfiniteIdeal_ne_span_small (S : Set OmnificInteger) hS

/-- A purely infinite omnific integer cannot be irreducible. -/
theorem omnific_not_irreducible_of_purelyInfinite (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : ¬ Irreducible x := by
  intro h
  obtain ⟨a, b, _, _, _, _, ha, hb, he⟩ := omnific_purelyInfinite_factorization x hx h.ne_zero
  exact (h.isUnit_or_isUnit he).elim ha hb

/-- Every irreducible has nonzero integer constant coefficient. -/
theorem omnific_irreducible_constant_ne_zero (x : OmnificInteger.{u}) (hx : Irreducible x) :
    omnificConstantCoeff x ≠ 0 := fun h => omnific_not_irreducible_of_purelyInfinite x h hx

/-- No product of a finite list of irreducibles belongs to the purely infinite ideal. -/
theorem omnific_irreducible_prod_not_purelyInfinite (s : List OmnificInteger.{u})
    (hs : ∀ x ∈ s, Irreducible x) : s.prod ∉ omnificPurelyInfiniteIdeal := by
  change omnificConstantCoeff s.prod ≠ 0
  induction s with
  | nil => simp only [List.prod_nil, map_one, ne_eq, one_ne_zero, not_false_eq_true]
  | cons x s ih =>
    rw [List.prod_cons, map_mul]
    exact mul_ne_zero (omnific_irreducible_constant_ne_zero x (hs x (List.mem_cons_self)))
      (ih (fun y hy => hs y (List.mem_cons_of_mem x hy)))

/-- A homomorphism whose purely infinite image lies in a nilpotent ideal kills that image. -/
theorem omnific_nilpotent_test {R : Type v} [Ring R] (f : OmnificInteger.{u} →+* R)
    (J : Ideal R) (hJ : IsNilpotent J)
    (hf : ∀ x ∈ omnificPurelyInfiniteIdeal, f x ∈ J) :
    ∀ x ∈ omnificPurelyInfiniteIdeal, f x = 0 := by
  have hp : ∀ n : ℕ, ∀ x ∈ omnificPurelyInfiniteIdeal, f x ∈ J ^ n := by
    intro n
    induction n with
    | zero => intro x _; simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | succ n ih =>
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := omnific_purelyInfinite_single_product x hx
      rw [map_mul, Submodule.pow_succ]
      exact Ideal.mul_mem_mul (ih a ha) (hf b hb)
  obtain ⟨n, hn⟩ := hJ
  intro x hx
  have h := hp n x hx
  rw [hn] at h
  exact h

end
end Surreal.Foundations.SignSequence
