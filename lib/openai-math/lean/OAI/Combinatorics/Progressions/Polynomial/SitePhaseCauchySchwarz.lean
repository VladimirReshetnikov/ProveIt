import OAI.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter
import OAI.Combinatorics.Progressions.Geometry.BoxCornerMean

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem boxPhaseMoment_character {X : Type*} [Fintype X] (h : ℕ)
    (P : (Fin h → X) → ℝ) :
    boxPhaseMoment h (fun x => character (P x : CircleFourier.Circle)) =
      𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle) := by
  unfold boxPhaseMoment
  simp_rw [iteratedBoxDifference_character]

theorem assigned_phase_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (P : (Fin h → X) → ℝ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) * ∏ s, U s x‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  have hc := assigned_site_cauchySchwarz hh
    (fun x => character (P x : CircleFourier.Circle)) assignment U hU hmiss
  rw [boxPhaseMoment_character] at hc
  exact hc.trans (Complex.re_le_norm _)

theorem assigned_phase_bias {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (P : (Fin h → X) → ℝ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : δ ≤ ‖𝔼 x, character (P x : CircleFourier.Circle) * ∏ s, U s x‖) :
    δ ^ (2 ^ h) ≤ ‖𝔼 u, 𝔼 v, character
      ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ :=
  (pow_le_pow_left₀ hδ hbias _).trans (assigned_phase_cauchySchwarz hh P assignment U hU hmiss)

end Erdos3

end

end OAI
