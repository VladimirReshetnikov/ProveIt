import OAI.Combinatorics.Progressions.Fourier.CokernelCharacterWitness
import OAI.Combinatorics.Progressions.Fourier.IndependentCharacterEvents

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def sampledColumnMatrix {I J : Type*} {Ω : J → Type*}
    (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  fun i j => column j (x j) i

theorem sampledColumn_mem_range {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) (j : J) :
    column j (x j) ∈ (sampledColumnMatrix column x).mulVecLin.range := by
  refine ⟨Pi.single j 1, ?_⟩
  exact Matrix.mulVec_single_one _ _

def largeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (B R : ℕ) (x : ∀ j, Ω j) : Prop :=
  ∃ A : Matrix I I ℤ, A.det ≠ 0 ∧
    A.mulVecLin.range ≤ (sampledColumnMatrix column x).mulVecLin.range ∧
    A.det.natAbs ≤ R ∧ B < integerCokernelExponent (sampledColumnMatrix column x).mulVecLin.range

theorem largeCokernelEvent_character {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (B R : ℕ) (x : ∀ j, Ω j)
    (hx : largeCokernelEvent column B R x) :
    ∃ χ : AddChar (I → ℤ) ℂ, B < orderOf χ ∧ orderOf χ ≤ R ∧
      ∀ j, χ (column j (x j)) = 1 := by
  obtain ⟨A, hA, hAin, hAR, hB⟩ := hx
  obtain ⟨χ, hχB, hχA, hann⟩ := exists_bounded_annihilating_character
    (sampledColumnMatrix column x).mulVecLin.range A hA hAin B hB
  exact ⟨χ, hχB, hχA.trans hAR,
    fun j => hann _ (sampledColumn_mem_range column x j)⟩

theorem largeCokernel_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q a) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      ∑ a : Fin R, if B < a.val + 1 then
        ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I * q (a.val + 1) ^ Fintype.card J else 0 :=
  largeOrderAnnihilator_probability_le p column _ B R q hq
    (largeCokernelEvent_character column B R) hsingle

end Erdos3

end

end OAI
