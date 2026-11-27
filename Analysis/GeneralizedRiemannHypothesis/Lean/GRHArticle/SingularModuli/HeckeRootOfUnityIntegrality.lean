import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Integral coefficients in a prime root-of-unity orbit product

The product is first formed in the integral additive group ring of
`ZMod p`. It is fixed under the permutations induced by nonzero scalars.
Every fixed coefficient has equal weight at all nonzero group elements,
whose images under the standard additive character sum to `-1`.
-/

namespace GRHArticle.SingularModuli

open PowerSeries
open scoped PowerSeries

private abbrev primeGroupRing (p : ℕ) := AddMonoidAlgebra ℤ (ZMod p)

private def indexMulEquiv {p : ℕ} [Fact (Nat.Prime p)] (c : ZMod p) (hc : c ≠ 0) :
    ZMod p ≃+ ZMod p :=
  { Equiv.mulLeft₀ c hc with
    map_add' := fun x y ↦ mul_add c x y }

private noncomputable def permutePrimeGroupRing {p : ℕ} [Fact (Nat.Prime p)] (c : ZMod p)
    (hc : c ≠ 0) : primeGroupRing p ≃ₐ[ℤ] primeGroupRing p :=
  AddMonoidAlgebra.domCongr ℤ ℤ (indexMulEquiv c hc)

private noncomputable def evaluatePrimeGroupRing (p : ℕ) [NeZero p] :
    primeGroupRing p →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ (ZMod p) ZMod.stdAddChar.toMonoidHom

private theorem fixed_primeGroupRing_coeff {p : ℕ} [Fact (Nat.Prime p)]
    (g : primeGroupRing p) (hg : ∀ c hc, permutePrimeGroupRing c hc g = g)
    (t : ZMod p) (ht : t ≠ 0) : g.coeff t = g.coeff 1 := by
  have h := congrArg (fun x : primeGroupRing p ↦ x.coeff t) (hg t ht)
  change (AddMonoidAlgebra.domCongr ℤ ℤ (indexMulEquiv t ht) g).coeff t = _ at h
  rw [AddMonoidAlgebra.coeff_domCongr] at h
  have ht₁ : (indexMulEquiv t ht).symm t = 1 := by
    apply (indexMulEquiv t ht).injective
    rw [AddEquiv.apply_symm_apply]
    change t = t * 1
    rw [mul_one]
  simpa only [ht₁] using h.symm

private theorem evaluate_fixed_primeGroupRing {p : ℕ} [Fact (Nat.Prime p)]
    (g : primeGroupRing p) (hg : ∀ c hc, permutePrimeGroupRing c hc g = g) :
    evaluatePrimeGroupRing p g = ((g.coeff 0 - g.coeff 1 : ℤ) : ℂ) := by
  classical
  let e : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have he : e ≠ 0 := by
    intro h0
    have hh : e 1 = e 0 := by rw [h0]; simp
    exact one_ne_zero (ZMod.injective_stdAddChar hh)
  have hsum : (∑ t : ZMod p, e t) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr he
  have hsum' : (∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0, e t) = -1 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) e (Finset.mem_univ 0)
    rw [hsum, AddChar.map_zero_eq_one] at h
    linear_combination h
  have hg' : g = ∑ t : ZMod p, AddMonoidAlgebra.single t (g.coeff t) := by
    ext t
    simp [AddMonoidAlgebra.coeff_single]
  calc
    evaluatePrimeGroupRing p g =
        ∑ t : ZMod p, (g.coeff t : ℂ) * e t := by
      conv_lhs => rw [hg']
      simp only [map_sum, evaluatePrimeGroupRing, AddMonoidAlgebra.lift_single, e,
        AddChar.toMonoidHom_apply, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
      rfl
    _ = (∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0, (g.coeff t : ℂ) * e t) +
        (g.coeff 0 : ℂ) * e 0 := (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm
    _ = (g.coeff 1 : ℂ) * (∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0, e t) +
        (g.coeff 0 : ℂ) * e 0 := by
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun t ht ↦ by rw [fixed_primeGroupRing_coeff g hg t
        (Finset.mem_erase.mp ht).1])
    _ = _ := by rw [hsum', AddChar.map_zero_eq_one, Int.cast_sub]; ring

private noncomputable def primeGroupFactor {p : ℕ} (A J : ℤ⟦X⟧) (d : ℕ) (t : ZMod p) :
    PowerSeries (primeGroupRing p) :=
  PowerSeries.map (Int.castRingHom _) A -
    C (AddMonoidAlgebra.of' ℤ (ZMod p) (-t)) * X ^ d *
      rescale (AddMonoidAlgebra.of' ℤ (ZMod p) t) (PowerSeries.map (Int.castRingHom _) J)

private theorem map_permutePrimeGroupFactor {p : ℕ} [Fact (Nat.Prime p)]
    (A J : ℤ⟦X⟧) (d : ℕ) (t c : ZMod p) (hc : c ≠ 0) :
    PowerSeries.map (permutePrimeGroupRing c hc).toRingHom (primeGroupFactor A J d t) =
      primeGroupFactor A J d (indexMulEquiv c hc t) := by
  let e := permutePrimeGroupRing c hc
  have hcast (f : ℤ⟦X⟧) :
      PowerSeries.map e.toRingHom (PowerSeries.map (Int.castRingHom _) f) =
      PowerSeries.map (Int.castRingHom _) f := by
    ext1 n
    simp only [coeff_map, Int.coe_castRingHom]
    exact map_intCast e.toRingHom _
  have hb (s : ZMod p) :
      e.toRingHom (AddMonoidAlgebra.of' ℤ _ s) = AddMonoidAlgebra.of' ℤ _ (indexMulEquiv c hc s) :=
    AddMonoidAlgebra.domCongr_single (R := ℤ) (indexMulEquiv c hc) s 1
  change PowerSeries.map e.toRingHom (primeGroupFactor A J d t) = _
  simp only [primeGroupFactor, map_sub, map_mul, map_pow, map_C, map_X, hcast]
  rw [← rescale_map, hcast]
  simp only [hb, AddEquiv.map_neg]

private theorem map_evaluatePrimeGroupFactor {p : ℕ} [NeZero p]
    (A J : ℤ⟦X⟧) (d : ℕ) (t : ZMod p) :
    PowerSeries.map (evaluatePrimeGroupRing p).toRingHom (primeGroupFactor A J d t) =
      PowerSeries.map (Int.castRingHom ℂ) A - C (ZMod.stdAddChar (-t)) * X ^ d *
        rescale (ZMod.stdAddChar t) (PowerSeries.map (Int.castRingHom ℂ) J) := by
  let e := evaluatePrimeGroupRing p
  have hcast (f : ℤ⟦X⟧) :
      PowerSeries.map e.toRingHom (PowerSeries.map (Int.castRingHom _) f) =
      PowerSeries.map (Int.castRingHom ℂ) f := by
    ext1 n
    simp only [coeff_map, Int.coe_castRingHom]
    exact map_intCast e.toRingHom _
  have hb (s : ZMod p) : e.toRingHom (AddMonoidAlgebra.of' ℤ _ s) = ZMod.stdAddChar s :=
    AddMonoidAlgebra.lift_of' ZMod.stdAddChar.toMonoidHom s
  change PowerSeries.map e.toRingHom (primeGroupFactor A J d t) = _
  simp only [primeGroupFactor, map_sub, map_mul, map_pow, map_C, map_X, hcast]
  rw [← rescale_map, hcast]
  simp only [hb]

/-- The prime orbit product of rescaled integral series has integral
coefficients. The prefactor of each rescaled series is the negative
character value times `X^d`. -/
theorem exists_integral_primeRootProduct (p : ℕ) [Fact (Nat.Prime p)]
    (A J : ℤ⟦X⟧) (d : ℕ) :
    ∃ F : ℤ⟦X⟧, PowerSeries.map (Int.castRingHom ℂ) F =
      ∏ t : ZMod p, (PowerSeries.map (Int.castRingHom ℂ) A -
        C (ZMod.stdAddChar (-t)) * X ^ d *
          rescale (ZMod.stdAddChar t) (PowerSeries.map (Int.castRingHom ℂ) J)) := by
  let G : PowerSeries (primeGroupRing p) := ∏ t : ZMod p, primeGroupFactor A J d t
  have hfixed (c : ZMod p) (hc : c ≠ 0) :
      PowerSeries.map (permutePrimeGroupRing c hc).toRingHom G = G := by
    simp only [G, map_prod, map_permutePrimeGroupFactor]
    exact (indexMulEquiv c hc).toEquiv.prod_comp (primeGroupFactor A J d)
  have hfixedCoeff (n : ℕ) (c : ZMod p) (hc : c ≠ 0) :
      permutePrimeGroupRing c hc (G.coeff n) = G.coeff n := by
    have h := congrArg (fun s : PowerSeries (primeGroupRing p) ↦ s.coeff n) (hfixed c hc)
    rw [coeff_map] at h
    exact h
  refine ⟨PowerSeries.mk fun n ↦ (G.coeff n).coeff 0 - (G.coeff n).coeff 1, ?_⟩
  have hresult : PowerSeries.map (evaluatePrimeGroupRing p).toRingHom G =
      ∏ t : ZMod p, (PowerSeries.map (Int.castRingHom ℂ) A -
        C (ZMod.stdAddChar (-t)) * X ^ d *
          rescale (ZMod.stdAddChar t) (PowerSeries.map (Int.castRingHom ℂ) J)) := by
    simp only [G, map_prod, map_evaluatePrimeGroupFactor]
  rw [← hresult]
  ext n
  simp only [coeff_map, coeff_mk]
  exact (evaluate_fixed_primeGroupRing (G.coeff n) (hfixedCoeff n)).symm

end GRHArticle.SingularModuli
