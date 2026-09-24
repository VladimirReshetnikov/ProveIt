import Surreal.Algebra.CoefficientPullback
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# A quadratic equation defining the constant-term kernel

The algebraic mechanism of `odg:def:thm:ideal` and `odg:def:rem:delta`.
A nonsquare in the fraction field forbids nonzero constant coordinates;
a square root in the ambient coefficient field supplies the purely
infinite witness. The ambient ring needs only a coefficient-algebra
retraction, not an order or a degree function.
-/

namespace Surreal.QuadraticIdeal

noncomputable section

/-- A nonsquare in the fraction field has no nonzero quadratic proportionality in the ring. -/
theorem zero_of_nonsquare_fraction {O Q : Type*} [CommRing O] [IsDomain O] [Field Q]
    [Algebra O Q] [IsFractionRing O Q] (δ : O) (hn : ¬ IsSquare (algebraMap O Q δ))
    (a b : O) (h : a ^ 2 = δ * b ^ 2) : a = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb' : algebraMap O Q b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O Q)).mpr hb
    have he : (algebraMap O Q a / algebraMap O Q b) ^ 2 = algebraMap O Q δ := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
      simpa only [map_pow, map_mul] using congrArg (algebraMap O Q) h
    exact hn ⟨algebraMap O Q a / algebraMap O Q b, by simpa only [pow_two] using he.symm⟩
  rw [hb, zero_pow (by decide), mul_zero] at h
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h

/-- In a full coefficient pullback, the quadratic equation detects exactly the retraction
kernel. The hypothesis on constant solutions is supplied by the fraction-field lemma. -/
theorem kernel_iff_quadratic {O K B : Type*} [CommRing O] [Field K] [CommRing B] [Algebra K B]
    (ct : B →ₐ[K] K) (i : O →+* K) (hi : Function.Injective i)
    (δ : O) (r : K) (hr : r ^ 2 = i δ) (hr0 : r ≠ 0)
    (hzero : ∀ a b : O, a ^ 2 = δ * b ^ 2 → a = 0)
    (d : CoefficientPullback.subring ct.toRingHom i) (hd : d.val = algebraMap K B (i δ))
    (x : CoefficientPullback.subring ct.toRingHom i) :
    ct x.val = 0 ↔ ∃ y : CoefficientPullback.subring ct.toRingHom i, x ^ 2 = d * y ^ 2 := by
  constructor
  · intro hx
    let y : CoefficientPullback.subring ct.toRingHom i :=
      ⟨algebraMap K B r⁻¹ * x.val, by
        refine ⟨0, ?_⟩
        change i 0 = ct (algebraMap K B r⁻¹ * x.val)
        simp only [map_zero, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply, hx, mul_zero]⟩
    refine ⟨y, Subtype.ext ?_⟩
    change x.val ^ 2 = d.val * (algebraMap K B r⁻¹ * x.val) ^ 2
    rw [hd, ← hr]
    calc
      x.val ^ 2 = algebraMap K B (r ^ 2 * (r⁻¹) ^ 2) * x.val ^ 2 := by
        rw [← mul_pow, mul_inv_cancel₀ hr0, one_pow, map_one, one_mul]
      _ = _ := by simp only [map_mul, map_pow]; ring
  · rintro ⟨y, h⟩
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    change i a = ct x.val at ha
    change i b = ct y.val at hb
    have he := congrArg (fun z : CoefficientPullback.subring ct.toRingHom i => ct z.val) h
    change ct (x.val ^ 2) = ct (d.val * y.val ^ 2) at he
    rw [hd, map_pow, map_mul, map_pow, AlgHom.commutes, Algebra.algebraMap_self_apply,
      ← ha, ← hb] at he
    have hab : a ^ 2 = δ * b ^ 2 := hi (by simpa only [map_pow, map_mul] using he)
    rw [← ha, hzero a b hab, map_zero]

/-- The parameter-free quadratic predicate is preserved by every unital ring homomorphism. -/
theorem map_quadratic_witness {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (x : R) (hx : ∃ y : R, x ^ 2 = 2 * y ^ 2) :
    ∃ y : S, (φ x) ^ 2 = 2 * y ^ 2 := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨φ y, by simpa only [map_pow, map_mul, map_ofNat] using congrArg φ hy⟩

end
end Surreal.QuadraticIdeal
