import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastSpatialOutputHom {R : Type*} [AddCommMonoid R] :
    (X → R) →+ (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun u o := match o.2 with
    | .inl x => u x.val
    | .inr _ => 0
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

def forecastCoefficientOutputHom {R : Type*} [AddCommMonoid R] :
    (∀ j, Fin (n j) ⊕ E j → R) →+
      (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun label o := match o.2 with
    | .inl _ => 0
    | .inr (.inl i) => label o.1 (.inr i)
    | .inr (.inr a) => label o.1 (.inl a.val)
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

def forecastCongruenceOutput {R : Type*} (u : X → R)
    (label : ∀ j, Fin (n j) ⊕ E j → R) :
    Sigma (AllocatedCongruenceRankOutput X E inactive) → R := fun o =>
  match o.2 with
  | .inl x => u x.val
  | .inr (.inl i) => label o.1 (.inr i)
  | .inr (.inr a) => label o.1 (.inl a.val)

theorem forecastCongruenceOutput_eq_add {R : Type*} [AddCommMonoid R]
    (u : X → R) (label : ∀ j, Fin (n j) ⊕ E j → R) :
    forecastCongruenceOutput inactive u label =
      forecastSpatialOutputHom inactive u + forecastCoefficientOutputHom inactive label := by
  funext o
  rcases o with ⟨j, x | i | a⟩ <;>
    simp [forecastCongruenceOutput, forecastSpatialOutputHom, forecastCoefficientOutputHom]

theorem forecastCongruenceOutput_intCast (q : ℕ) (u : X → ℤ)
    (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod q)) =
      forecastCongruenceOutput inactive (fun x => (u x : ZMod q))
        (fun j i => (label j i : ZMod q)) := by
  funext o
  rcases o with ⟨j, x | i | a⟩ <;> rfl

variable [Fintype X] [∀ j, Fintype (E j)]

theorem exists_forecastSpatialCharacterSplit
    {N : ℕ} [NeZero N]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod N) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M) :
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ coeff : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ,
        (∀ u, ‖mask u‖ = 1) ∧ (∀ label, ‖coeff label‖ = 1) ∧
        (∀ (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ),
          χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N)) =
            mask (fun x => (u x : ZMod M)) * coeff (fun j i => (label j i : ZMod M))) ∧
        ∀ (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ),
          star (χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N))) =
            star (mask (fun x => (u x : ZMod M))) *
              star (coeff (fun j i => (label j i : ZMod M))) := by
  obtain ⟨ψ, _, _, _, hψ⟩ := exists_characterOrder_descent χ
  let ψM := ψ.compAddMonoidHom (zmodPiReduction hM)
  let mask := ψM.compAddMonoidHom (forecastSpatialOutputHom (E := E) inactive)
  let coeff := ψM.compAddMonoidHom (forecastCoefficientOutputHom (X := X) inactive)
  have heq (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
      χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N)) =
        mask (fun x => (u x : ZMod M)) * coeff (fun j i => (label j i : ZMod M)) := by
    rw [hψ]
    change ψ _ = ψM (forecastSpatialOutputHom inactive _) *
      ψM (forecastCoefficientOutputHom inactive _)
    rw [← AddChar.map_add_eq_mul, ← forecastCongruenceOutput_eq_add]
    dsimp only [ψM, AddChar.compAddMonoidHom_apply]
    congr 1
    funext o
    rcases o with ⟨j, x | i | a⟩ <;>
      simp [zmodPiReduction, forecastCongruenceOutput]
  refine ⟨mask, coeff, (fun _ => AddChar.norm_apply _ _),
    (fun _ => AddChar.norm_apply _ _), heq, ?_⟩
  intro u label
  rw [heq]
  exact map_mul (starRingEnd ℂ) _ _

end Erdos3.VectorPolynomial

end

end OAI
