import ZFCinPA.SetRelativization

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.SetRelativization
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.SetRelativization.set_not_isFunc
#print axioms LeanProofs.ZFCinPA.SetRelativization.isTerm_eq_fvar
#print axioms LeanProofs.ZFCinPA.SetRelativization.provable_falsum_of_relativize_set

section Weak
variable {V : Type*} [ORingStructure V]
example (k f : V) : ¬(ℒₛₑₜ).IsFunc k f := set_not_isFunc k f
end Weak

section Strong
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (t : V) (ht : IsTerm ℒₛₑₜ t) : ∃ j : V, t=^&j := isTerm_eq_fvar ht
example (j : V) : ∃ k : V, (^&j : V)=^&k := isTerm_eq_fvar (by simp)
example (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (d : V)
    (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d=d)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p∈T.Δ₁Class →
      ∃ m : V, Derivable U (insert (relativize ℒₛₑₜ d p) (domSet ℒₛₑₜ d m)))
    (hne : Provable U (^∃ d)) (hp : Provable T (^⊥ : V)) :
    Provable U (^⊥ : V) := provable_falsum_of_relativize_set hd hds hAx hne hp
example (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (d : V)
    (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d=d)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p∈T.Δ₁Class →
      ∃ m : V, Derivable U (insert (relativize ℒₛₑₜ d p) (domSet ℒₛₑₜ d m)))
    (hne : Provable U (^∃ d)) (hcon : ¬Provable U (^⊥ : V)) :
    ¬Provable T (^⊥ : V) := by
  intro hp
  exact hcon (provable_falsum_of_relativize_set hd hds hAx hne hp)
example (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (d p : V)
    (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d=d)
    (hAx : ∀ q : V, IsFormula ℒₛₑₜ q → q∈T.Δ₁Class →
      ∃ m : V, Derivable U (insert (relativize ℒₛₑₜ d q) (domSet ℒₛₑₜ d m)))
    (hne : Provable U (^∃ d)) (hp : Provable T p) (hps : shift ℒₛₑₜ p=p) :
    Provable U (relativize ℒₛₑₜ d p) :=
  provable_relativize hd hds (fun _ ht => isTerm_eq_fvar ht) hAx hne hp hps
end Strong
