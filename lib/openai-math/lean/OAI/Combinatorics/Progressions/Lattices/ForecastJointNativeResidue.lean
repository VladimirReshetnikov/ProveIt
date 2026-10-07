import OAI.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

def forecastJointNativeResidue {A : Type*}
    (deck : ∀ j, E j → A) (r : X ⊕ AllocatedActiveIntegerAxis U basis L → A) : Out → A
  | ⟨_, .inl x⟩ => r (.inl x.val)
  | ⟨j, .inr (.inl e)⟩ => deck j e
  | ⟨j, .inr (.inr i)⟩ => r (.inr ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩)

theorem forecastJointNativeResidue_integer (q : ℕ)
    (u : X → ℤ) (ks : AllocatedShortIntegerAxis U basis L → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis L → ℤ) (deck : ∀ j, E j → ℤ) :
    forecastJointNativeResidue (I := I) U basis L (fun j e => (deck j e : ZMod q))
        (Sum.elim (fun x => (u x : ZMod q)) (fun a => (ka a : ZMod q))) =
      fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis L ks ka ⟨j, i⟩)
          (deck j)) output : ZMod q) := by
  funext output
  rcases output with ⟨j, x | e | i⟩
  · rfl
  · rfl
  · change (ka ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩ : ZMod q) =
      (forecastIntegerAxisMerge U basis L ks ka ⟨j, i.val⟩ : ZMod q)
    rw [forecastIntegerAxisMerge_active U basis L ks ka ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩]

end Erdos3.VectorPolynomial

end

end OAI
