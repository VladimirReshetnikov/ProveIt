import GRHArticle.SingularModuli.CMHeckeDiagonal
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Modular invariance of the prime Hecke orbit polynomial

Translation cycles the shifts. Inversion exchanges the scaled translate with
the zero shift and sends each nonzero shift to its negative inverse modulo
the prime.
-/

namespace GRHArticle.SingularModuli

open Polynomial UpperHalfPlane ModularGroup
open scoped MatrixGroups BigOperators

private theorem cast_p_ne_zero (p : ℕ+) : ((p : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < p by positivity).ne'

private theorem scaled_T (p : ℕ+) (z : ℍ) :
    heckeScaledPoint p (T • z) = T ^ (p : ℤ) • heckeScaledPoint p z := by
  simp only [UpperHalfPlane.ext_iff, modular_T_smul, modular_T_zpow_smul, heckeScaledPoint,
    coe_vadd, Complex.ofReal_one, Complex.ofReal_intCast]
  push_cast
  ring

private theorem shift_T (p : ℕ+) (t : ℕ) (z : ℍ) :
    heckeShiftPoint p t (T • z) = heckeShiftPoint p (t + 1) z := by
  simp only [UpperHalfPlane.ext_iff, modular_T_smul, heckeShiftPoint, coe_vadd,
    Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
  ring

private theorem shift_top_T (p : ℕ+) (n : ℕ) (hn : (p : ℕ) = n + 1) (z : ℍ) :
    heckeShiftPoint p n (T • z) = T • heckeShiftPoint p 0 z := by
  rw [shift_T, modular_T_smul]
  simp only [UpperHalfPlane.ext_iff, heckeShiftPoint, coe_vadd, Complex.ofReal_one,
    Nat.cast_zero, add_zero, ← hn]
  have hcast : ((p : ℝ) : ℂ) = ((p : ℕ) : ℂ) := Complex.ofReal_natCast (p : ℕ)
  rw [← hcast, add_div, div_self (cast_p_ne_zero p), add_comm]

/-- Translation preserves the entire prime-level orbit polynomial. -/
theorem analyticPrimeHeckePolynomial_T (p : ℕ+) (z : ℍ) :
    analyticPrimeHeckePolynomial p (T • z) = analyticPrimeHeckePolynomial p z := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero p.pos.ne'
  let F (t : ℕ) : ℂ[X] := X - C (modularInvariant (heckeShiftPoint p t z))
  let G (t : ℕ) : ℂ[X] := X - C (modularInvariant (heckeShiftPoint p t (T • z)))
  have hlast : G n = F 0 := by
    change X - C (modularInvariant (heckeShiftPoint p n (T • z))) =
      X - C (modularInvariant (heckeShiftPoint p 0 z))
    exact congrArg (fun y : ℂ => X - C y)
      ((congrArg modularInvariant (shift_top_T p n hn z)).trans
        (modularInvariant_smul T (heckeShiftPoint p 0 z)))
  have hremaining : (∏ t ∈ Finset.range n, G t) = ∏ t ∈ Finset.range n, F (t + 1) :=
    Finset.prod_congr rfl fun t _ ↦
      congrArg (fun w : ℍ => X - C (modularInvariant w)) (shift_T p t z)
  have hprod : (∏ t ∈ Finset.range (p : ℕ), G t) = ∏ t ∈ Finset.range (p : ℕ), F t := by
    rw [hn, Finset.prod_range_succ G, Finset.prod_range_succ' F, hlast, hremaining]
  have hs := (congrArg modularInvariant (scaled_T p z)).trans
    (modularInvariant_smul (T ^ (p : ℤ)) (heckeScaledPoint p z))
  change (X - C (modularInvariant (heckeScaledPoint p (T • z)))) *
      (∏ t ∈ Finset.range (p : ℕ), G t) =
    (X - C (modularInvariant (heckeScaledPoint p z))) * (∏ t ∈ Finset.range (p : ℕ), F t)
  exact congrArg₂ (· * ·) (congrArg (fun y : ℂ => X - C y) hs) hprod

private theorem scaled_S (p : ℕ+) (z : ℍ) :
    heckeScaledPoint p (S • z) = S • heckeShiftPoint p 0 z := by
  simp only [UpperHalfPlane.ext_iff, modular_S_smul, heckeScaledPoint, heckeShiftPoint,
    coe_mk, Nat.cast_zero, add_zero, inv_neg]
  field_simp [cast_p_ne_zero p, z.ne_zero]

private theorem shift_zero_S (p : ℕ+) (z : ℍ) :
    heckeShiftPoint p 0 (S • z) = S • heckeScaledPoint p z := by
  simp only [UpperHalfPlane.ext_iff, modular_S_smul, heckeScaledPoint, heckeShiftPoint,
    coe_mk, Nat.cast_zero, add_zero, inv_neg]
  field_simp [cast_p_ne_zero p, z.ne_zero]

private theorem shift_S_smul (p : ℕ+) (z : ℍ) (t b : ℕ) (k : ℤ)
    (hk : (p : ℤ) * k + (t : ℤ) * (b : ℤ) = -1) :
    ∃ g : SL(2, ℤ), heckeShiftPoint p t (S • z) = g • heckeShiftPoint p b z := by
  let g : SL(2, ℤ) := ⟨!![(t : ℤ), k; (p : ℤ), -(b : ℤ)], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hk]⟩
  refine ⟨g, ?_⟩
  rw [UpperHalfPlane.ext_iff, coe_specialLinearGroup_apply]
  change ((((S • z : ℍ) : ℂ)) + (t : ℂ)) / ((p : ℝ) : ℂ) =
    (((Int.castRingHom ℝ) (t : ℤ) : ℂ) * (((z : ℂ) + b) / ((p : ℝ) : ℂ)) +
      ((Int.castRingHom ℝ) k : ℂ)) /
    (((Int.castRingHom ℝ) (p : ℤ) : ℂ) * (((z : ℂ) + b) / ((p : ℝ) : ℂ)) +
      ((Int.castRingHom ℝ) (-(b : ℤ)) : ℂ))
  rw [modular_S_smul]
  simp only [Int.coe_castRingHom, Complex.ofReal_intCast]
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  have hk' : (p : ℂ) * (k : ℂ) + (t : ℂ) * (b : ℂ) = -1 := by exact_mod_cast hk
  have hk'' : (t : ℂ) * (b : ℂ) + (p : ℂ) * (k : ℂ) = -1 := by simpa only [add_comm] using hk'
  have hden : (p : ℂ) * (((z : ℂ) + (b : ℂ)) / (p : ℂ)) - (b : ℂ) = (z : ℂ) := by
    rw [mul_comm, div_mul_cancel₀ _ hp, add_sub_cancel_right]
  have hnum : (t : ℂ) * (((z : ℂ) + (b : ℂ)) / (p : ℂ)) + (k : ℂ) =
      ((t : ℂ) * (z : ℂ) - 1) / (p : ℂ) := by
    apply (eq_div_iff hp).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hp, mul_add]
    linear_combination hk''
  rw [← sub_eq_add_neg, hden, hnum]
  rw [inv_neg]
  field_simp [hp, z.ne_zero]
  ring

/-- Inversion preserves the entire prime-level orbit polynomial. -/
theorem analyticPrimeHeckePolynomial_S (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (z : ℍ) :
    analyticPrimeHeckePolynomial p (S • z) = analyticPrimeHeckePolynomial p z := by
  let U := (Finset.range (p : ℕ)).erase 0
  let b (t : ℕ) := (-(t : ZMod (p : ℕ))⁻¹).val
  have hb (t : ℕ) : (b t : ZMod (p : ℕ)) = -(t : ZMod (p : ℕ))⁻¹ :=
    ZMod.natCast_zmod_val _
  have hbound (t : ℕ) : b t < (p : ℕ) := ZMod.val_lt _
  have hinv {t : ℕ} (ht : t < (p : ℕ)) : b (b t) = t := by
    change (-(b t : ZMod (p : ℕ))⁻¹).val = t
    rw [hb, inv_neg, inv_inv, neg_neg, ZMod.val_natCast_of_lt ht]
  have hzero : b 0 = 0 := by simp [b]
  have hrestrict {t : ℕ} (ht : t ∈ U) : b t ∈ U := by
    obtain ⟨ht₀, ht₁⟩ := Finset.mem_erase.mp ht
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (hbound t)⟩
    intro h
    exact ht₀ (by rw [← hinv (Finset.mem_range.mp ht₁), h, hzero])
  have hsame {t : ℕ} (ht : t ∈ U) :
      modularInvariant (heckeShiftPoint p t (S • z)) =
        modularInvariant (heckeShiftPoint p (b t) z) := by
    obtain ⟨ht₀, ht₁⟩ := Finset.mem_erase.mp ht
    have htZ : (t : ZMod (p : ℕ)) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ht₁), ZMod.val_zero] at hv
      exact ht₀ hv
    have hzmod : ((-(t : ℤ) * (b t : ℤ) - 1 : ℤ) : ZMod (p : ℕ)) = 0 := by
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_one]
      rw [hb, mul_neg, neg_mul, neg_neg, mul_inv_cancel₀ htZ, sub_self]
    obtain ⟨k, hk⟩ :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p : ℕ)).1 hzmod
    obtain ⟨g, hg⟩ := shift_S_smul p z t (b t) k (by linear_combination -hk)
    rw [hg, modularInvariant_smul]
  have hprod : (∏ t ∈ U, (X - C (modularInvariant (heckeShiftPoint p t (S • z))))) =
      ∏ t ∈ U, (X - C (modularInvariant (heckeShiftPoint p t z))) := by
    refine Finset.prod_bij (fun t _ ↦ b t) (fun _ ht ↦ hrestrict ht) ?_ ?_ ?_
    · intro t ht u hu h
      have ht' := hinv (Finset.mem_range.mp (Finset.mem_erase.mp ht).2)
      have hu' := hinv (Finset.mem_range.mp (Finset.mem_erase.mp hu).2)
      exact ht'.symm.trans ((congrArg b h).trans hu')
    · intro t ht
      exact ⟨b t, hrestrict ht, hinv (Finset.mem_range.mp (Finset.mem_erase.mp ht).2)⟩
    · intro t ht
      rw [hsame ht]
  let F (t : ℕ) : ℂ[X] := X - C (modularInvariant (heckeShiftPoint p t z))
  let G (t : ℕ) : ℂ[X] := X - C (modularInvariant (heckeShiftPoint p t (S • z)))
  have h0 : 0 ∈ Finset.range (p : ℕ) := Finset.mem_range.mpr p.pos
  have hF := Finset.prod_erase_mul (Finset.range (p : ℕ)) F h0
  have hG := Finset.prod_erase_mul (Finset.range (p : ℕ)) G h0
  have hfirst :
      X - C (modularInvariant (heckeScaledPoint p (S • z))) = F 0 := by
    change X - C (modularInvariant (heckeScaledPoint p (S • z))) =
      X - C (modularInvariant (heckeShiftPoint p 0 z))
    exact congrArg (fun y : ℂ => X - C y)
      ((congrArg modularInvariant (scaled_S p z)).trans
        (modularInvariant_smul S (heckeShiftPoint p 0 z)))
  have hlast : G 0 = X - C (modularInvariant (heckeScaledPoint p z)) := by
    change X - C (modularInvariant (heckeShiftPoint p 0 (S • z))) =
      X - C (modularInvariant (heckeScaledPoint p z))
    exact congrArg (fun y : ℂ => X - C y)
      ((congrArg modularInvariant (shift_zero_S p z)).trans
        (modularInvariant_smul S (heckeScaledPoint p z)))
  change (X - C (modularInvariant (heckeScaledPoint p (S • z)))) *
      (∏ t ∈ Finset.range (p : ℕ), G t) = (X - C (modularInvariant (heckeScaledPoint p z))) *
        ∏ t ∈ Finset.range (p : ℕ), F t
  rw [hfirst, ← hG, ← hF, hlast]
  change F 0 * ((∏ t ∈ U, G t) * _) = _
  rw [show (∏ t ∈ U, G t) = ∏ t ∈ U, F t from hprod]
  ring

/-- The entire orbit polynomial is invariant under the full modular group. -/
theorem analyticPrimeHeckePolynomial_smul (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (g : SL(2, ℤ)) (z : ℍ) : analyticPrimeHeckePolynomial p (g • z) =
      analyticPrimeHeckePolynomial p z := by
  have hg : g ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing z with
  | one => rw [one_smul]
  | mem g hg =>
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg :
        g = S ∨ g = T) with rfl | rfl
    · exact analyticPrimeHeckePolynomial_S p z
    · exact analyticPrimeHeckePolynomial_T p z
  | mul a b _ _ ha hb => rw [mul_smul, ha, hb]
  | inv a _ h =>
    have he := h (a⁻¹ • z)
    simpa only [smul_inv_smul] using he.symm

end GRHArticle.SingularModuli
