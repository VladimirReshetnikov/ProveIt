import Surreal.Surcomplex.InfinitesimalTrigonometry
import Surreal.Surcomplex.QuadraticCollisionPoints

/-!
# Roots of the actual complex cosine fold

The infinitesimal sine equivalence reduces the equation `cos θ = 1-τ`
to `s^2=τ/2`. These are the exact two branches and valuation assertions
of `trigonometry:thm:fold` and the inverse-germ formula in
`trigonometry:eq:foldroots`. Formal angular multiplicities and the
reorganized full endpoint series are separate obligations.
-/

universe u

namespace Surreal.Surcomplex.CosineFold

open Foundations

noncomputable section

/-- Multiplication by two stays inside the infinitesimal monad. -/
theorem infinitesimal_two_mul {z : Surcomplex.{u}} (hz : IsInfinitesimal z) :
    IsInfinitesimal (2 * z) := by
  simpa only [map_ofNat] using infinitesimal_ofComplex_mul 2 hz

/-- Division by two stays inside the infinitesimal monad. -/
theorem infinitesimal_div_two {z : Surcomplex.{u}} (hz : IsInfinitesimal z) :
    IsInfinitesimal (z / 2) := by
  have hc : (ofComplex (1 / 2 : ℂ) : Surcomplex.{u}) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have h := infinitesimal_ofComplex_mul (1 / 2) hz
  rw [hc] at h
  simpa only [one_div, mul_comm, ← div_eq_mul_inv] using h

/-- The chosen positive label refers to a chosen complex square root. -/
def branch (s : Surcomplex.{u}) (hs : IsInfinitesimal s) : Surcomplex.{u} :=
  2 * infArcsin s hs

theorem infinitesimal_branch (s : Surcomplex.{u}) (hs : IsInfinitesimal s) :
    IsInfinitesimal (branch s hs) := infinitesimal_two_mul (infinitesimal_infArcsin s hs)

/-- Both possible square-root choices give the same unordered pair of branches. -/
theorem branch_neg (s : Surcomplex.{u}) (hs : IsInfinitesimal s) :
    branch (-s) (infinitesimal_neg hs) = -branch s hs := by
  change 2 * infArcsin (-s) _ = -(2 * infArcsin s hs)
  rw [infArcsin_neg s hs, mul_neg]

/-- The original angle is recovered from its sine half-angle. -/
theorem branch_sin_half (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    branch (infSin (θ / 2) (infinitesimal_div_two hθ))
      (infinitesimal_infSin _ _) = θ := by
  rw [branch, infArcsin_infSin]
  ring

/-- The half-angle identity identifies the fold with the quadratic equation. -/
theorem equation_iff_square (τ θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    infCos θ hθ = 1 - τ ↔
      infSin (θ / 2) (infinitesimal_div_two hθ) ^ 2 = τ / 2 := by
  have h := infCos_two_mul (θ / 2) (infinitesimal_div_two hθ)
    (infinitesimal_two_mul (infinitesimal_div_two hθ))
  have he : 2 * (θ / 2) = θ := by ring
  have hh : infCos θ hθ = 1 - 2 * infSin (θ / 2) (infinitesimal_div_two hθ) ^ 2 :=
    (show infCos θ hθ = infCos (2 * (θ / 2)) _ by congr 1; exact he.symm).trans h
  rw [hh]
  constructor
  · intro hh; linear_combination -hh / 2
  · intro hh; linear_combination -2 * hh

/-- Every square root produces an actual infinitesimal solution. -/
theorem branch_solution (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) : infCos (branch s hs) (infinitesimal_branch s hs) = 1 - τ := by
  change infCos (2 * infArcsin s hs) _ = _
  rw [infCos_two_mul _ (infinitesimal_infArcsin s hs), infSin_infArcsin, hsq]
  ring

/-- These are all solutions in the full infinitesimal monad, including collision. -/
theorem solutions_iff (τ s θ : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hθ : IsInfinitesimal θ) :
    infCos θ hθ = 1 - τ ↔ θ = branch s hs ∨ θ = -branch s hs := by
  constructor
  · intro h
    have hq := (equation_iff_square τ θ hθ).mp h
    rcases (QuadraticCollision.points_iff (τ / 2) s _ hsq).mp hq with hp | hm
    · left
      calc
        θ = branch (infSin (θ / 2) (infinitesimal_div_two hθ))
            (infinitesimal_infSin _ _) := (branch_sin_half θ hθ).symm
        _ = branch s hs := by congr 1
    · right
      calc
        θ = branch (infSin (θ / 2) (infinitesimal_div_two hθ))
            (infinitesimal_infSin _ _) := (branch_sin_half θ hθ).symm
        _ = branch (-s) (infinitesimal_neg hs) := by congr 1
        _ = -branch s hs := branch_neg s hs
  · rintro (rfl | rfl)
    · exact branch_solution τ s hs hsq
    · rw [infCos_neg]
      exact branch_solution τ s hs hsq

/-- At collision zero is the only infinitesimal root. -/
theorem zero_solution_iff (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    infCos θ hθ = 1 ↔ θ = 0 := by
  simpa [branch] using solutions_iff 0 0 θ infinitesimal_zero (by simp) hθ

theorem branch_ne_zero (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hτ : τ ≠ 0) : branch s hs ≠ 0 := by
  intro h
  have ha : infArcsin s hs = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
  have he : s = 0 := infArcsin_injective hs infinitesimal_zero (by simpa using ha)
  simp [he] at hsq
  exact hτ ((div_eq_zero_iff).mp hsq.symm |>.resolve_right (by norm_num))

/-- The two branches are distinct at every nonzero parameter. -/
theorem branches_distinct (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hτ : τ ≠ 0) : branch s hs ≠ -branch s hs := by
  intro h
  have he : 2 * branch s hs = 0 := by linear_combination h
  exact branch_ne_zero τ s hs hsq hτ ((mul_eq_zero.mp he).resolve_left (by norm_num))

/-- Existence and exhaustion of the two actual branches at every nonzero infinitesimal scale. -/
theorem exists_two_roots (τ : Surcomplex.{u}) (hτ : IsInfinitesimal τ) (hτ0 : τ ≠ 0) :
    ∃ θ : Surcomplex.{u}, IsInfinitesimal θ ∧ θ ≠ -θ ∧
      ∀ z (hz : IsInfinitesimal z), infCos z hz = 1 - τ ↔ z = θ ∨ z = -θ := by
  obtain ⟨s, hs, hsq⟩ := exists_infinitesimal_sq_eq (τ / 2) (infinitesimal_div_two hτ)
  exact ⟨branch s hs, infinitesimal_branch s hs, branches_distinct τ s hs hsq hτ0,
    fun z hz => solutions_iff τ s z hs hsq hz⟩

/-- The inverse germ and multiplication by two preserve the root valuation. -/
theorem valuation_branch (s : Surcomplex.{u}) (hs : IsInfinitesimal s) :
    valuation (branch s hs) = valuation s := by
  have htwo : valuation (2 : Surcomplex.{u}) = 0 := by
    have hc : (ofComplex (2 : ℂ) : Surcomplex.{u}) = 2 := map_ofNat _ _
    exact hc ▸ valuation_ofComplex (by norm_num : (2 : ℂ) ≠ 0)
  rw [branch, valuation_mul, htwo, zero_add, valuation_infArcsin]

/-- Exact half valuation without a choice of a representative for infinity. -/
theorem two_nsmul_valuation_branch (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) : 2 • valuation (branch s hs) = valuation τ := by
  have he : τ = 2 * s ^ 2 := by rw [hsq]; ring
  have htwo : valuation (2 : Surcomplex.{u}) = 0 := by
    have hc : (ofComplex (2 : ℂ) : Surcomplex.{u}) = 2 := map_ofNat _ _
    exact hc ▸ valuation_ofComplex (by norm_num : (2 : ℂ) ≠ 0)
  rw [valuation_branch, he, valuation_mul, htwo, zero_add, valuation.map_pow]

/-- At a nonzero parameter the finite valuation exponent is literally halved. -/
theorem valuation_branch_half (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hτ : τ ≠ 0) :
    valuation (branch s hs) =
      ((-leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have he := two_nsmul_valuation_branch τ s hs hsq
  have hb := branch_ne_zero τ s hs hsq hτ
  rw [valuation_of_ne_zero hb, valuation_of_ne_zero hτ, ← WithTop.coe_nsmul] at he
  have hh := WithTop.coe_injective he
  rw [valuation_of_ne_zero hb]
  congr 1
  simp only [two_nsmul] at hh
  dsimp only [leadingExponent]
  linarith

/-- Both signs have the same exact half valuation. -/
theorem valuations_both_branches (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hτ : τ ≠ 0) :
    valuation (branch s hs) =
        ((-leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) ∧
      valuation (-branch s hs) =
        ((-leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [valuation_neg]
  exact ⟨valuation_branch_half τ s hs hsq hτ, valuation_branch_half τ s hs hsq hτ⟩

/-- The sine at a separated fold root does not vanish. -/
theorem sin_branch_ne_zero (τ s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hsq : s ^ 2 = τ / 2) (hτ : τ ≠ 0) :
    infSin (branch s hs) (infinitesimal_branch s hs) ≠ 0 := by
  change infSin (2 * infArcsin s hs) _ ≠ 0
  rw [infSin_two_mul _ (infinitesimal_infArcsin s hs), infSin_infArcsin]
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num)
    intro he
    have ht : τ = 0 := by
      have hh : τ / 2 = 0 := by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using hsq.symm
      exact (div_eq_zero_iff.mp hh).resolve_right (by norm_num)
    exact hτ ht
  · exact infCos_ne_zero _ _

/-- A real square-root choice produces a real angular branch. -/
theorem branch_im_eq_zero (s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hr : s.im = 0) : (branch s hs).im = 0 := by
  rw [branch, two_mul, QuadraticAlgebra.im_add, infArcsin_im_eq_zero s hs hr, add_zero]

/-- A purely imaginary square-root choice produces a purely imaginary branch. -/
theorem branch_re_eq_zero (s : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (hi : s.re = 0) : (branch s hs).re = 0 := by
  rw [branch, two_mul, QuadraticAlgebra.re_add, infArcsin_re_eq_zero s hs hi, add_zero]

/-- Positive real parameters have only real infinitesimal fold roots. -/
theorem positive_real_roots (τ : SignSequence.{u}) (hp : 0 < τ)
    (hi : SignSequence.IsInfinitesimal τ) (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ)
    (he : infCos θ hθ = 1 - ofReal τ) : θ.im = 0 := by
  let s : Surcomplex.{u} := ofReal (SignSequence.sqrt (τ / 2))
  have hsq : s ^ 2 = ofReal τ / 2 := by
    dsimp only [s]
    rw [← map_pow, SignSequence.sqrt_sq (by positivity), map_div₀, map_ofNat]
  have hs : IsInfinitesimal s := infinitesimal_of_sq_eq hsq
    (infinitesimal_div_two ⟨hi, SignSequence.infinitesimal_zero⟩)
  rcases (solutions_iff (ofReal τ) s θ hs hsq hθ).mp he with h | h
  · rw [h]
    exact branch_im_eq_zero s hs (by simp [s])
  · rw [h, QuadraticAlgebra.im_neg, branch_im_eq_zero s hs (by simp [s]), neg_zero]

/-- Negative real parameters yield exactly two conjugate imaginary roots. -/
theorem negative_real_roots (τ : SignSequence.{u}) (hn : τ < 0)
    (hi : SignSequence.IsInfinitesimal τ) :
    ∃ θ : Surcomplex.{u}, IsInfinitesimal θ ∧ θ.re = 0 ∧ θ ≠ 0 ∧
      conj θ = -θ ∧ θ ≠ -θ ∧
      ∀ z (hz : IsInfinitesimal z),
        infCos z hz = 1 - ofReal τ ↔ z = θ ∨ z = conj θ := by
  let s := QuadraticCollision.imaginaryPoint (τ / 2)
  have hsq : s ^ 2 = ofReal τ / 2 := by
    simpa only [map_div₀, map_ofNat] using
      QuadraticCollision.imaginaryPoint_sq (τ / 2) (div_neg_of_neg_of_pos hn (by norm_num))
  have hs : IsInfinitesimal s := infinitesimal_of_sq_eq hsq
    (infinitesimal_div_two ⟨hi, SignSequence.infinitesimal_zero⟩)
  have hτ : (ofReal τ : Surcomplex.{u}) ≠ 0 := by
    intro h
    have hr := congrArg (fun z : Surcomplex.{u} => z.re) h
    exact hn.ne (by simpa using hr)
  have hr : (branch s hs).re = 0 :=
    branch_re_eq_zero s hs (QuadraticCollision.imaginaryPoint_re _)
  have hc := (conj_eq_neg_iff_re_eq_zero _).mpr hr
  refine ⟨branch s hs, infinitesimal_branch s hs, hr,
    branch_ne_zero _ s hs hsq hτ, hc, branches_distinct _ s hs hsq hτ, ?_⟩
  intro z hz
  rw [hc]
  exact solutions_iff _ s z hs hsq hz

/-- No real infinitesimal angle solves a negative-real cosine fold. -/
theorem no_real_root_of_neg (τ : SignSequence.{u}) (hn : τ < 0)
    (hi : SignSequence.IsInfinitesimal τ) (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ)
    (hr : θ.im = 0) : infCos θ hθ ≠ 1 - ofReal τ := by
  obtain ⟨z, _, hzre, hz0, hc, _, hz⟩ := negative_real_roots τ hn hi
  intro he
  have hh := (hz θ hθ).mp he
  rw [hc] at hh
  rcases hh with h | h
  · apply hz0
    apply ext
    · exact hzre
    · simpa only [h, QuadraticAlgebra.im_zero] using hr
  · apply hz0
    apply ext
    · exact hzre
    · simpa only [h, QuadraticAlgebra.im_neg, neg_eq_zero, QuadraticAlgebra.im_zero] using hr

end
end Surreal.Surcomplex.CosineFold
