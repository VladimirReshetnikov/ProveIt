import BusyBeaver.ZFC.ArithmeticCode254
import Foundation.FirstOrder.Arithmetic.HFS.Vec
/-! Properties of an internally definable map on coded finite vectors. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorVectorMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (f map : V → V) [𝚺₁-Function₁[V] f] [𝚺₁-Function₁[V] map]
variable (nil_rule : map 0 = 0) (cons_rule : ∀ p L, map (p ∷ L) = f p ∷ map L)
include nil_rule cons_rule in
lemma len_nth : ∀ L : V, len (map L) = len L ∧ ∀ i < len L, (map L).[i] = f L.[i] := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp [nil_rule]
  case adjoin p L ih =>
    refine ⟨by simp [cons_rule, ih.1], fun i hi ↦ ?_⟩
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simp [cons_rule]
    · simpa [cons_rule] using ih.2 j (by simpa using hi)
omit [𝚺₁-Function₁[V] f] [𝚺₁-Function₁[V] map] in
lemma mem (L y : V) (h : len (map L) = len L ∧ ∀ i < len L, (map L).[i] = f L.[i]) :
    y ∈ᵥ map L ↔ ∃ p, p ∈ᵥ L ∧ y = f p := by
  obtain ⟨hl, hn⟩ := h
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hl] at hi
    exact ⟨L.[i], nth_mem_memVec hi, hn i hi⟩
  · rintro ⟨p, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, by rw [hl]; exact hi, (hn i hi).symm⟩
end LeanProofs.ZFCinPA.ValidatorVectorMap
