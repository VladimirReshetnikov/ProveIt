import OAI.Combinatorics.Progressions.Polynomial.SitePhaseCauchySchwarz

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

noncomputable def shiftedBoxSite {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) (x : Fin h → X) : V :=
  base + ∑ i, coefficient i • shift (x i)

theorem shiftedBoxSite_update {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) {i : Fin h}
    (hi : coefficient i = 0) (x : Fin h → X) (a : X) :
    shiftedBoxSite base coefficient shift (Function.update x i a) =
      shiftedBoxSite base coefficient shift x := by
  unfold shiftedBoxSite
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, zero_smul]
  · simp only [Function.update_of_ne hj]

theorem shifted_site_phase_cauchySchwarz {h : ℕ} {S X V : Type*}
    [Fintype S] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (base : S → V) (coefficient : S → Fin h → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, coefficient s i = 0) (P : (Fin h → X) → ℝ)
    (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) *
      ∏ s, test s (shiftedBoxSite (base s) (coefficient s) shift x)‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  let assignment : S → Fin h := fun s => (hzero s).choose
  apply assigned_phase_cauchySchwarz hh P assignment
    (fun s x => test s (shiftedBoxSite (base s) (coefficient s) shift x))
    (fun s x => htest s _)
  intro s x a
  exact congrArg (test s)
    (shiftedBoxSite_update (base s) (coefficient s) shift (hzero s).choose_spec x a)

end Erdos3

end

end OAI
