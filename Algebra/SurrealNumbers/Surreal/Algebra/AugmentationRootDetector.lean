import Surreal.Algebra.CoefficientPullback
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# A polynomial root detector for an augmentation

Proves `odg:def:thm:augdetector` and `odg:def:eq:augdetector` over an
arbitrary commutative coefficient-field algebra. The ambient algebra may
have zero divisors. Only a nonzero scalar is divided by in the construction
`odg:def:eq:witness`; neither inversion of the input nor completeness is used.
-/

namespace Surreal.AugmentationRootDetector

open Polynomial

noncomputable section

variable {K H O : Type*} [Field K] [CommRing H] [Algebra K H] [CommRing O]

/-- The full coefficient pullback is exactly the ordinary constants plus the augmentation kernel. -/
theorem mem_pullback_iff (ε : H →ₐ[K] K) (i : O →+* K) (a : H) :
    a ∈ CoefficientPullback.subring ε.toRingHom i ↔
      ∃ c : O, ∃ p : H, ε p = 0 ∧ a = algebraMap K H (i c) + p := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, a - algebraMap K H (i c), ?_, by ring⟩
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact sub_eq_zero.mpr hc.symm
  · rintro ⟨c, p, hp, rfl⟩
    refine ⟨c, ?_⟩
    change i c = ε (algebraMap K H (i c) + p)
    simp [hp]

/-- The affine witness t = r + αa. -/
def affineWitness (r α : K) (a : H) : H :=
  algebraMap K H r + algebraMap K H α * a

/-- The witness s = αQ(t), where f = (T-r)Q. -/
def quotientWitness (Q : K[X]) (α : K) (t : H) : H :=
  algebraMap K H α * Q.eval₂ (algebraMap K H) t

/-- The factorization gives the certificate in any commutative algebra. -/
theorem witness_identity (f Q : K[X]) (r α : K) (a : H)
    (hQ : f = (X - C r) * Q) :
    a * quotientWitness Q α (affineWitness r α a) =
      f.eval₂ (algebraMap K H) (affineWitness r α a) := by
  rw [hQ, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]
  unfold affineWitness quotientWitness
  ring

/-- With α = (b-r)/c and ε(a)=c, the affine witness has constant coefficient b. -/
theorem affineWitness_augmentation (ε : H →ₐ[K] K) (r b c : K) (hc : c ≠ 0)
    (a : H) (ha : ε a = c) : ε (affineWitness r ((b - r) / c) a) = b := by
  simp only [affineWitness, map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self, ha,
    RingHom.id_apply]
  rw [div_mul_cancel₀ _ hc]
  ring

private theorem augmentation_comp (ε : H →ₐ[K] K) (i : O →+* K) :
    ε.toRingHom.comp ((algebraMap K H).comp i) = i := by
  ext b
  simp

/-- The detector, written in the ambient algebra with explicit pullback membership. -/
theorem ambient_certificate_iff (ε : H →ₐ[K] K) (i : O →+* K)
    (hi : Function.Injective i) (f : O[X]) (hno : ∀ b : O, f.eval b ≠ 0)
    (r : K) (hr : f.eval₂ i r = 0)
    (hmod : ∀ c : O, c ≠ 0 → ∃ b d : O, f.eval b = c * d)
    (a : H) (ha : ε a ∈ i.range) :
    ε a ≠ 0 ↔ ∃ s t : H, ε s ∈ i.range ∧ ε t ∈ i.range ∧
      a * s = f.eval₂ ((algebraMap K H).comp i) t := by
  constructor
  · intro hc
    obtain ⟨c, hca⟩ := ha
    have hc' : c ≠ 0 := by intro hz; rw [hz, map_zero] at hca; exact hc hca.symm
    obtain ⟨b, d, hbd⟩ := hmod c hc'
    have hr' : (f.map i).IsRoot r := by simpa only [IsRoot, eval_map] using hr
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hr'
    let α : K := (i b - r) / i c
    let t : H := affineWitness r α a
    let s : H := quotientWitness Q α t
    have ht : ε t = i b :=
      affineWitness_augmentation ε r (i b) (i c) (hca ▸ hc) a hca.symm
    have he : a * s = f.eval₂ ((algebraMap K H).comp i) t := by
      simpa only [eval₂_map] using witness_identity (f.map i) Q r α a hQ
    have hs : ε s = i d := by
      have h := congrArg ε.toRingHom he
      simp only [map_mul, Polynomial.hom_eval₂, augmentation_comp] at h
      change ε a * ε s = f.eval₂ i (ε t) at h
      rw [ht, eval₂_at_apply, hbd, map_mul, ← hca] at h
      exact mul_left_cancel₀ (hca ▸ hc) h
    exact ⟨s, t, ⟨d, hs.symm⟩, ⟨b, ht.symm⟩, he⟩
  · rintro ⟨s, t, _, ⟨b, hb⟩, he⟩ hz
    have h := congrArg ε.toRingHom he
    simp only [map_mul, Polynomial.hom_eval₂, augmentation_comp] at h
    change ε a * ε s = f.eval₂ i (ε t) at h
    rw [hz, zero_mul, ← hb, eval₂_at_apply] at h
    exact hno b (hi (h.symm.trans (map_zero i).symm))

/-- The ordinary constants embedded in the full coefficient pullback. -/
def constants (ε : H →ₐ[K] K) (i : O →+* K) :
    O →+* CoefficientPullback.subring ε.toRingHom i :=
  CoefficientPullback.sectionMap ε.toRingHom i (algebraMap K H) (by intro b; simp)

/-- The native existential polynomial equation on the full pullback ring. -/
def Certificate (ε : H →ₐ[K] K) (i : O →+* K) (f : O[X])
    (a : CoefficientPullback.subring ε.toRingHom i) : Prop :=
  ∃ s t : CoefficientPullback.subring ε.toRingHom i, a * s = f.eval₂ (constants ε i) t

/-- A polynomial with the three source hypotheses detects nonzero augmentation. -/
theorem certificate_iff (ε : H →ₐ[K] K) (i : O →+* K)
    (hi : Function.Injective i) (f : O[X]) (hno : ∀ b : O, f.eval b ≠ 0)
    (r : K) (hr : f.eval₂ i r = 0)
    (hmod : ∀ c : O, c ≠ 0 → ∃ b d : O, f.eval b = c * d)
    (a : CoefficientPullback.subring ε.toRingHom i) :
    Certificate ε i f a ↔ ε a.val ≠ 0 := by
  rw [ambient_certificate_iff ε i hi f hno r hr hmod a.val a.property]
  have hcomp : (CoefficientPullback.subring ε.toRingHom i).subtype.comp
      (constants ε i) = (algebraMap K H).comp i := rfl
  constructor
  · rintro ⟨s, t, he⟩
    refine ⟨s.val, t.val, s.property, t.property, ?_⟩
    have h := congrArg (CoefficientPullback.subring ε.toRingHom i).subtype he
    simp only [map_mul, Polynomial.hom_eval₂, hcomp] at h
    exact h
  · rintro ⟨s, t, hs, ht, he⟩
    refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change a.val * s = (CoefficientPullback.subring ε.toRingHom i).subtype
      (f.eval₂ (constants ε i) ⟨t, ht⟩)
    rw [Polynomial.hom_eval₂, hcomp]
    exact he

end
end Surreal.AugmentationRootDetector
