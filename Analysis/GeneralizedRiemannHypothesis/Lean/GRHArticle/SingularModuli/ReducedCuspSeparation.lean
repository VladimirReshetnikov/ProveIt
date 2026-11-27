import GRHArticle.SingularModuli.CuspEstimate
import GRHArticle.SingularModuli.ReducedForms
import GRHArticle.SingularModuli.CuspSeparation
import GRHArticle.SingularModuli.Binomial
import Mathlib.RingTheory.AdjoinRoot

/-!
# Cusp separation for the invariants of reduced forms
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- The analytic value attached to a reduced form of discriminant `-D`. -/
noncomputable def reducedFormInvariant (D : ℕ+) (f : FormCoefficients) : ℂ :=
  modularInvariant (quadraticPoint D f.a f.b)

theorem reducedFormInvariant_cusp {D : ℕ+} {f : FormCoefficients} (hf : f ∈ reducedForms D) :
    |‖reducedFormInvariant D f‖ - Real.exp (Real.pi * √(D : ℝ) / f.a)| ≤ 2079 := by
  have h := (mem_reducedForms_iff D f).mp hf
  exact modularInvariant_reduced_cusp D f.a f.b f.c h.1 h.2.1 h.2.2.1

/-- The two integer inequalities of `smd:eq:septest` give separation by a
factor of sixteen for actual analytic values of primitive reduced forms. -/
theorem sixteen_mul_norm_reducedFormInvariant_lt {D : ℕ+} {f g : FormCoefficients}
    (hf : f ∈ reducedForms D) (hg : g ∈ reducedForms D) (ha : (f.a : ℕ) < g.a)
    (hsize : 16 * (f.a : ℕ) ^ 2 ≤ D)
    (hgap : 16 * (f.a : ℕ) ^ 2 * (g.a : ℕ) ^ 2 ≤
      9 * (D : ℕ) * ((g.a : ℕ) - f.a) ^ 2) :
    16 * ‖reducedFormInvariant D g‖ < ‖reducedFormInvariant D f‖ :=
  sixteen_mul_norm_lt_of_cusp_estimates f.a.pos ha hsize hgap _ _
    (reducedFormInvariant_cusp hf) (reducedFormInvariant_cusp hg)

private theorem leading_one_middle {D : ℕ+} {f : FormCoefficients}
    (hf : IsPrimitiveReducedForm D f) (ha : f.a = 1) : f.b = 0 ∨ f.b = 1 := by
  have h := abs_le.mp hf.2.1
  rw [ha] at h
  norm_num at h
  have hn : 0 ≤ f.b := by
    by_contra! hn
    have he : f.b = -1 := by omega
    have hb : |f.b| = (f.a : ℤ) := by rw [he, ha]; norm_num
    exact (not_le_of_gt hn) (hf.2.2.2.1 (Or.inl hb))
  omega

/-- The boundary sign convention and the discriminant determine the single
primitive reduced form of leading coefficient one. -/
theorem reducedForms_eq_of_leading_one {D : ℕ+} {f g : FormCoefficients}
    (hf : f ∈ reducedForms D) (hg : g ∈ reducedForms D) (ha : f.a = 1) (hb : g.a = 1) : f = g := by
  have hf' := (mem_reducedForms_iff D f).mp hf
  have hg' := (mem_reducedForms_iff D g).mp hg
  have hdisc₁ := hf'.1
  have hdisc₂ := hg'.1
  rw [ha] at hdisc₁
  rw [hb] at hdisc₂
  norm_num at hdisc₁ hdisc₂
  have hdiff : f.b ^ 2 - g.b ^ 2 = 4 * (f.c - g.c) := by linarith only [hdisc₁, hdisc₂]
  have heq : f.b = g.b := by
    rcases leading_one_middle hf' ha with hf0 | hf1 <;>
      rcases leading_one_middle hg' hb with hg0 | hg1 <;> simp_all <;> omega
  have hlast : f.c = g.c := by rw [heq] at hdiff; omega
  have haeq : f.a = g.a := ha.trans hb.symm
  cases f
  cases g
  simp_all

/-- The principal form exists whenever the reduced-form enumeration is nonempty
and `D ≥ 15`. -/
theorem reducedForms_exists_leading_one {D : ℕ+} (hD : 15 ≤ (D : ℕ))
    (h : (reducedForms D).Nonempty) : ∃ f ∈ reducedForms D, f.a = 1 := by
  obtain ⟨f, hf⟩ := h
  have hdisc := ((mem_reducedForms_iff D f).mp hf).1
  let b := f.b % 2
  let k := f.b / 2
  let c := (f.a : ℤ) * f.c - (k ^ 2 + k * b)
  have hb₀ : 0 ≤ b := Int.emod_nonneg _ (by decide)
  have hb₂ : b < 2 := Int.emod_lt_of_pos _ (by decide)
  have heq : f.b = b + 2 * k := by dsimp [b, k]; omega
  have hdisc' : b ^ 2 - 4 * c = -(D : ℤ) := by
    rw [heq] at hdisc
    dsimp only [c]
    nlinarith only [hdisc]
  have hD' : (15 : ℤ) ≤ D := by exact_mod_cast hD
  have hc : (1 : ℤ) ≤ c := by nlinarith only [hdisc', hD', sq_nonneg b]
  refine ⟨⟨1, b, c⟩, (mem_reducedForms_iff D _).mpr ?_, rfl⟩
  refine ⟨by simpa using hdisc', ?_, by simpa using hc, fun _ => hb₀, by simp⟩
  rw [abs_of_nonneg hb₀]
  norm_num
  omega

/-- At discriminant magnitude at least fifteen, the principal analytic value
has strictly greater modulus than the value of any other reduced form. -/
theorem norm_reducedFormInvariant_lt_principal {D : ℕ+} {f g : FormCoefficients}
    (hD : 15 ≤ (D : ℕ)) (hf : f ∈ reducedForms D) (hg : g ∈ reducedForms D)
    (ha : f.a = 1) (hne : f ≠ g) : ‖reducedFormInvariant D g‖ < ‖reducedFormInvariant D f‖ := by
  have hga : 2 ≤ (g.a : ℕ) := by
    by_contra! hg₂
    have hga₁ : (g.a : ℕ) = 1 := by have hp := g.a.pos; omega
    have hga' : g.a = 1 := Subtype.ext hga₁
    exact hne (reducedForms_eq_of_leading_one hf hg ha hga')
  apply norm_lt_principal_of_cusp_estimates hD hga
  · simpa [ha] using reducedFormInvariant_cusp hf
  · exact reducedFormInvariant_cusp hg


private theorem not_binomial_of_minpoly_norm_ne {x z w : ℂ} (hx : IsIntegral ℚ x)
    (hz : aeval z (minpoly ℚ x) = 0) (hw : aeval w (minpoly ℚ x) = 0)
    (hne : ‖z‖ ≠ ‖w‖) : ¬ HasSparseAnnihilator ℚ x 2 := by
  let p := minpoly ℚ x
  letI : Fact (Irreducible p) := ⟨minpoly.irreducible hx⟩
  let y := AdjoinRoot.root p
  let f (u : ℂ) (hu : aeval u p = 0) : AdjoinRoot p →ₐ[ℚ] ℂ :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ ℂ) u hu
  have hroot (u : ℂ) (hu : aeval u p = 0) : f u hu y = u :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  have hnorm : ‖f z hz y‖ ≠ ‖f w hw y‖ := by simpa only [hroot] using hne
  have hn := not_hasSparseAnnihilator_two_of_norm_ne (f z hz) (f w hw) y hnorm
  rwa [← hroot x (minpoly.aeval ℚ x), hasSparseAnnihilator_algHom_iff]

/-- Discriminants below fifteen have at most one primitive reduced form. -/
theorem fifteen_le_of_reducedForms_card_eq_two {D : ℕ+} (hcard : (reducedForms D).card = 2) :
    15 ≤ (D : ℕ) := by
  have hp := D.pos
  by_contra! hD
  let k : Fin 14 := ⟨(D : ℕ) - 1, by omega⟩
  have hsmall : ∀ i : Fin 14, (reducedForms i.val.succPNat).card ≤ 1 := by decide +kernel
  have hval : (k.val.succPNat : ℕ) = (D : ℕ) := by
    change (D : ℕ) - 1 + 1 = (D : ℕ)
    omega
  have he : k.val.succPNat = D := Subtype.ext hval
  have hle := hsmall k
  rw [he, hcard] at hle
  omega

/-- In degree two, identification of the rational minimal polynomial with the
analytic class polynomial gives exact minimum support three. -/
theorem minimumSupport_eq_three_of_analyticClassPolynomial {D : ℕ+}
    (hcard : (reducedForms D).card = 2) {x : ℂ} (hx : IsIntegral ℚ x)
    (hmin : (minpoly ℚ x).map (algebraMap ℚ ℂ) = analyticClassPolynomial D) :
    minimumSupport hx = 3 := by
  have hD := fifteen_le_of_reducedForms_card_eq_two hcard
  have hnonempty : (reducedForms D).Nonempty :=
    Finset.card_pos.mp (by simp [hcard])
  obtain ⟨f, hf, ha⟩ := reducedForms_exists_leading_one hD hnonempty
  have htwo : 1 < (reducedForms D).card := by simp [hcard]
  obtain ⟨g, hg, j, hj, hne⟩ := Finset.one_lt_card.mp htwo
  have hother : ∃ g ∈ reducedForms D, f ≠ g := by
    by_cases h : f = g
    · exact ⟨j, hj, h ▸ hne⟩
    · exact ⟨g, hg, h⟩
  obtain ⟨g, hg, hfg⟩ := hother
  have hnorm := norm_reducedFormInvariant_lt_principal hD hf hg ha hfg
  have hroot (u : FormCoefficients) (hu : u ∈ reducedForms D) :
      aeval (reducedFormInvariant D u) (minpoly ℚ x) = 0 := by
    rw [← eval_map_algebraMap, hmin]
    exact (analyticClassPolynomial_eval_eq_zero_iff D _).mpr
      ⟨u, (mem_reducedForms_iff D u).mp hu, rfl⟩
  have hdeg : (minpoly ℚ x).natDegree = 2 := by
    rw [← natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, hmin,
      analyticClassPolynomial_natDegree, hcard]
  have hupper := minimumSupport_le_natDegree_add_one hx
  rw [hdeg] at hupper
  have hlower := not_binomial_of_minpoly_norm_ne hx (hroot f hf) (hroot g hg) (ne_of_gt hnorm)
  rw [← minimumSupport_le_iff hx] at hlower
  omega

end GRHArticle.SingularModuli
