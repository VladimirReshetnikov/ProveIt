import OAI.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
import OAI.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
import OAI.Combinatorics.Progressions.Lattices.IntegerRepresentativeFraction

namespace OAI

section

namespace Erdos3.RepresentativeWindow

open MvPolynomial
open scoped BigOperators

theorem patch_weighted_value {σ : Type*} {N : ℕ} [NeZero N]
    (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (a : ℤ) (he : aeval t P = (a : ℝ) / N) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) * F (a - (N : ℤ) * b 0)) =
      w.value (((a : ZMod N).val : ℝ) / N) * F ((a : ZMod N).val) := by
  have hterm (b : Fin 1 → ℤ) :
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F (a - (N : ℤ) * b 0) =
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F ((a : ZMod N).val) := by
    by_cases hb : (w.patch s hs P hP).kernel.value
        (((w.patch s hs P hP).form.slots t).residual b) = 0
    · simp only [hb, zero_mul]
    · rw [w.patch_contributing_lift s hs P hP t b hb, he, integer_sub_floor_eq_zmod_val]
  simp_rw [hterm]
  rw [tsum_mul_right]
  change (w.patch s hs P hP).value t * F ((a : ZMod N).val) = _
  rw [w.patch_value s hs P hP t, he, integer_fraction_eq_zmod_val]

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtPatch (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    PolynomialPatch J s 1 :=
  w.patch s hs (crtRepresentativePolynomial N hN) (crtRepresentativePolynomial_degree N hN)

theorem crtPatch_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) (u : J → ℤ) :
    (w.crtPatch N hN s hs).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) := by
  rw [crtPatch, w.patch_value, crtRepresentativePolynomial_eval,
    integer_fraction_eq_zmod_val, crtIntegerRepresentative_cast]

theorem crtPatch_value_residues [∀ j, NeZero (N j)] (w : RepresentativeWindow)
    (s : ℕ) (hs : 1 ≤ s) (u : (j : J) → ZMod (N j)) :
    (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) := by
  have h := w.crtPatch_value N hN s hs (fun j => ((u j).val : ℤ))
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

theorem crtPatch_weighted_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (u : J → ℤ) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.crtPatch N hN s hs).kernel.value
      (((w.crtPatch N hN s hs).form.slots (fun j => (u j : ℝ))).residual b) *
        F (crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      F (((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val) := by
  have h := w.patch_weighted_value s hs (crtRepresentativePolynomial N hN)
    (crtRepresentativePolynomial_degree N hN) (fun j => (u j : ℝ))
    (crtIntegerRepresentative N hN u) (crtRepresentativePolynomial_eval N hN u) F
  simpa only [crtIntegerRepresentative_cast, crtPatch] using h

omit [NeZero (∏ j, N j)] in
@[simp] theorem crtPatch_lip (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    (w.crtPatch N hN s hs).kernel.lip = w.lip := rfl

end Erdos3.RepresentativeWindow

end

end OAI
