import Surreal.Surcomplex.CoupledAngularRoots

/-!
# Real points of the coupled angular system

The reality and nonexistence clauses of `trigonometry:sec:coupled` reduce
to nonnegative squares in the actual surreal field. Sine and inverse sine
preserve and reflect the real axis on the complete infinitesimal monad.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Inverse sine reflects, as well as preserves, reality on the monad. -/
theorem infArcsin_im_eq_zero_iff (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    (infArcsin z hz).im = 0 ↔ z.im = 0 := by
  refine ⟨fun h => ?_, infArcsin_im_eq_zero z hz⟩
  apply (conj_eq_self_iff_im_eq_zero z).mp
  apply infArcsin_injective (infinitesimal_conj hz) hz
  rw [infArcsin_conj]
  exact (conj_eq_self_iff_im_eq_zero _).mpr h

/-- Sine preserves and reflects reality on the monad. -/
theorem infSin_im_eq_zero_iff (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    (infSin z hz).im = 0 ↔ z.im = 0 := by
  have h := infArcsin_im_eq_zero_iff (infSin z hz) (infinitesimal_infSin z hz)
  rw [infArcsin_infSin] at h
  exact h.symm

namespace CoupledAngular

/-- A real square root in the complexified field forces the real parameter nonnegative. -/
theorem nonneg_of_real_square {z : Surcomplex.{u}} {d : SignSequence.{u}}
    (hz : z.im = 0) (he : z ^ 2 = ofReal d) : 0 ≤ d := by
  have h := congrArg (fun w : Surcomplex.{u} => w.re) he
  simp only [pow_two, mul_re, hz, mul_zero, sub_zero, ofReal_re] at h
  rw [← h]
  exact mul_self_nonneg z.re

/-- Real infinitesimal angle pairs solving the system with real parameters. -/
def HasRealSolution (s t : SignSequence.{u}) : Prop :=
  ∃ p : Solutions (ofReal s) (ofReal t), p.1.1.1.im = 0 ∧ p.1.2.1.im = 0

/-- Both diagonal parameters must be nonnegative for a real angular solution. -/
theorem real_solution_nonneg (s t : SignSequence.{u}) (h : HasRealSolution s t) :
    0 ≤ s + 2 * t ∧ 0 ≤ s - 2 * t := by
  obtain ⟨p, hα, hβ⟩ := h
  have hx := (infSin_im_eq_zero_iff p.1.1.1 p.1.1.2).mpr hα
  have hy := (infSin_im_eq_zero_iff p.1.2.1 p.1.2.2).mpr hβ
  have he := (equations_iff _ _ _ _).mp p.2
  constructor
  · apply nonneg_of_real_square (z := infSin p.1.1.1 p.1.1.2 + infSin p.1.2.1 p.1.2.2)
    · simp [hx, hy]
    · simpa [map_ofNat] using he.1
  · apply nonneg_of_real_square (z := infSin p.1.1.1 p.1.1.2 - infSin p.1.2.1 p.1.2.2)
    · simp [hx, hy]
    · simpa [map_ofNat] using he.2

/-- The nonnegative diagonal parameters give real roots via the exact arcsine formulas. -/
theorem hasRealSolution_iff (s t : SignSequence.{u})
    (hs : SignSequence.IsInfinitesimal s) (ht : SignSequence.IsInfinitesimal t) :
    HasRealSolution s t ↔ 0 ≤ s + 2 * t ∧ 0 ≤ s - 2 * t := by
  refine ⟨real_solution_nonneg s t, fun ⟨hp, hq⟩ => ?_⟩
  let X := SignSequence.sqrt (s + 2 * t)
  let Y := SignSequence.sqrt (s - 2 * t)
  have hX : (ofReal X : Surcomplex.{u}) ^ 2 = ofReal s + 2 * ofReal t := by
    rw [← map_pow, SignSequence.sqrt_sq hp]; simp [map_ofNat]
  have hY : (ofReal Y : Surcomplex.{u}) ^ 2 = ofReal s - 2 * ofReal t := by
    rw [← map_pow, SignSequence.sqrt_sq hq]; simp [map_ofNat]
  have hs' : IsInfinitesimal (ofReal s) := ⟨hs, SignSequence.infinitesimal_zero⟩
  have ht' : IsInfinitesimal (ofReal t) := ⟨ht, SignSequence.infinitesimal_zero⟩
  refine ⟨anglesOfRoots (ofReal s) (ofReal t) hs' ht' (⟨ofReal X, hX⟩, ⟨ofReal Y, hY⟩), ?_, ?_⟩
  · change (infArcsin ((ofReal X + ofReal Y) / 2) _).im = 0
    apply infArcsin_im_eq_zero
    have he : (ofReal X + ofReal Y) / 2 = ofReal ((X + Y) / 2) := by simp [map_ofNat]
    rw [he]; rfl
  · change (infArcsin ((ofReal X - ofReal Y) / 2) _).im = 0
    apply infArcsin_im_eq_zero
    have he : (ofReal X - ofReal Y) / 2 = ofReal ((X - Y) / 2) := by simp [map_ofNat]
    rw [he]; rfl

/-- A negative diagonal parameter precludes two simultaneously real angles. -/
theorem no_real_solution_of_neg (s t : SignSequence.{u})
    (h : s + 2 * t < 0 ∨ s - 2 * t < 0) : ¬ HasRealSolution s t := by
  intro he
  have hn := real_solution_nonneg s t he
  rcases h with h | h
  · exact h.not_ge hn.1
  · exact h.not_ge hn.2

/-- Every complex square root of a nonnegative real parameter is real. -/
theorem real_of_square_nonneg {z : Surcomplex.{u}} {d : SignSequence.{u}}
    (hd : 0 ≤ d) (he : z ^ 2 = ofReal d) : z.im = 0 := by
  have hr : (ofReal (SignSequence.sqrt d) : Surcomplex.{u}) ^ 2 = ofReal d := by
    rw [← map_pow, SignSequence.sqrt_sq hd]
  rcases (QuadraticCollision.points_iff _ _ _ hr).mp he with h | h <;> simp [h]

/-- If both diagonal parameters are nonnegative, every complex angular solution is real. -/
theorem all_solutions_real (s t : SignSequence.{u})
    (hp : 0 ≤ s + 2 * t) (hq : 0 ≤ s - 2 * t)
    (p : Solutions (ofReal s) (ofReal t)) : p.1.1.1.im = 0 ∧ p.1.2.1.im = 0 := by
  have he := (equations_iff _ _ _ _).mp p.2
  have hX := real_of_square_nonneg hp (by simpa [map_ofNat] using he.1)
  have hY := real_of_square_nonneg hq (by simpa [map_ofNat] using he.2)
  simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub] at hX hY
  constructor
  · apply (infSin_im_eq_zero_iff p.1.1.1 p.1.1.2).mp
    linear_combination (hX + hY) / 2
  · apply (infSin_im_eq_zero_iff p.1.2.1 p.1.2.2).mp
    linear_combination (hX - hY) / 2

/-- The set of distinct real angle pairs. -/
abbrev RealSolutions (s t : SignSequence.{u}) :=
  {p : Solutions (ofReal s) (ofReal t) // p.1.1.1.im = 0 ∧ p.1.2.1.im = 0}

/-- Exact real counts in all strata: four for two positive parameters,
two for one zero and one positive, one at the origin, and zero otherwise. -/
theorem card_real_solutions (s t : SignSequence.{u})
    (hs : SignSequence.IsInfinitesimal s) (ht : SignSequence.IsInfinitesimal t) :
    Nat.card (RealSolutions s t) =
      if 0 ≤ s + 2 * t ∧ 0 ≤ s - 2 * t then
        (if s + 2 * t = 0 then 1 else 2) * (if s - 2 * t = 0 then 1 else 2)
      else 0 := by
  by_cases hn : 0 ≤ s + 2 * t ∧ 0 ≤ s - 2 * t
  · rw [if_pos hn]
    have e : RealSolutions s t ≃ Solutions (ofReal s) (ofReal t) :=
      Equiv.subtypeUnivEquiv (all_solutions_real s t hn.1 hn.2)
    have hc := card_solutions (ofReal s) (ofReal t)
      ⟨hs, SignSequence.infinitesimal_zero⟩ ⟨ht, SignSequence.infinitesimal_zero⟩
    rw [Nat.card_congr e, hc]
    have hp : ofReal s + 2 * ofReal t = ofReal (s + 2 * t) := by simp [map_ofNat]
    have hq : ofReal s - 2 * ofReal t = ofReal (s - 2 * t) := by simp [map_ofNat]
    simp only [hp, hq, map_eq_zero]
  · rw [if_neg hn]
    haveI : IsEmpty (RealSolutions s t) :=
      ⟨fun p => hn (real_solution_nonneg s t ⟨p.1, p.2⟩)⟩
    simp

end CoupledAngular
end
end Surreal.Surcomplex
