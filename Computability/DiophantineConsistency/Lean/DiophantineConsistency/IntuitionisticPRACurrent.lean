import DiophantineConsistency.IntuitionisticPRABridge
import DiophantineConsistency.FoundationHACurrentNoZero2011
import DiophantineConsistency.FoundationZFCConsistencyNat
/-! Conditional intuitionistic transfer of the literal 14-variable source. -/
set_option autoImplicit false
namespace DiophantineConsistency.IntuitionisticPRACurrent
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IntuitionisticPRABridge

noncomputable def currentClassical : Sentence language :=
  Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘
    Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence

theorem translated_current (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ PRA, T ⊢ σᴺ) (hcurrent : PRA ⊢ currentClassical) :
    T ⊢ currentClassicalᴺ := from_classical T hax hcurrent

theorem current_with_target (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ PRA, T ⊢ σᴺ) (hcurrent : PRA ⊢ currentClassical)
    (target : Sentenceᵢ language) (hbridge : T ⊢ (currentClassicalᴺ 🡒 target)) : T ⊢ target :=
  from_classical_with_target T hax hcurrent target hbridge
end DiophantineConsistency.IntuitionisticPRACurrent
