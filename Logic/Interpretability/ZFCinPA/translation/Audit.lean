import ZFCinPA.Translation

namespace LeanProofs.ZFCinPA.TranslationFreshAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
set_option autoImplicit false
attribute [local irreducible] LeanProofs.BoundedZFCConsistency.conZFCForm SetTheory.sealF

#print axioms LeanProofs.ZFCinPA.val_toSetVar
#print axioms LeanProofs.ZFCinPA.eval_toSet
#print axioms LeanProofs.ZFCinPA.modelsZF_of_modelsZFC
#print axioms LeanProofs.ZFCinPA.modelsZ_of_modelsZFC
#print axioms LeanProofs.ZFCinPA.sep_clause
#print axioms LeanProofs.ZFCinPA.sat_totalGraphF
#print axioms LeanProofs.ZFCinPA.sat_carveF
#print axioms LeanProofs.ZFCinPA.repl_clause
#print axioms LeanProofs.ZFCinPA.union_clause
#print axioms LeanProofs.ZFCinPA.pow_clause
#print axioms LeanProofs.ZFCinPA.inf_clause
#print axioms LeanProofs.ZFCinPA.reg_clause
#print axioms LeanProofs.ZFCinPA.choice_clause
#print axioms LeanProofs.ZFCinPA.zfcAxioms_of_models
#print axioms LeanProofs.ZFCinPA.zfc_proves_conZFCSet

example (k i : Nat) : Semiterm ℒₛₑₜ ℕ k :=
  LeanProofs.ZFCinPA.toSetVar k i

example (k : Nat) (φ : SetTheory.Form) : SetTheorySemiproposition k :=
  LeanProofs.ZFCinPA.toSet k φ

example {V : Type*} [SetStructure V] {k : Nat} {b : Fin k → V}
    {f e : ℕ → V} (hb : ∀ i : Fin k, b i = e i.val)
    (hf : ∀ j, f j = e (k + j)) (i : ℕ) :
    (toSetVar k i).val b f = e i :=
  LeanProofs.ZFCinPA.val_toSetVar hb hf i

example {V : Type*} [SetStructure V] (φ : SetTheory.Form)
    (k : Nat) (b : Fin k → V) (f e : ℕ → V)
    (hb : ∀ i : Fin k, b i = e i.val) (hf : ∀ j, f j = e (k + j)) :
    (toSet k φ).Eval b f ↔ SetTheory.Sat (memRel V) e φ :=
  LeanProofs.ZFCinPA.eval_toSet φ k b f e hb hf

example {V : Type*} [SetStructure V] (ψ : SetTheory.Form)
    (e : ℕ → V) (x y : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons x (SetTheory.scons y e)) (totalGraphF ψ) ↔
      (SetTheory.relOf (memRel V) ψ e y x ∨
        ((¬ ∃ z, SetTheory.relOf (memRel V) ψ e z x) ∧ y = x)) :=
  LeanProofs.ZFCinPA.sat_totalGraphF ψ e x y

example {V : Type*} [SetStructure V] (ψ : SetTheory.Form)
    (e : ℕ → V) (a y : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons y (SetTheory.scons a e)) (carveF ψ) ↔
      ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) ψ e y x :=
  LeanProofs.ZFCinPA.sat_carveF ψ e a y

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  LeanProofs.ZFCinPA.modelsZF_of_modelsZFC (V := V)

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    V↓[ℒₛₑₜ] ⊧* 𝗭 :=
  LeanProofs.ZFCinPA.modelsZ_of_modelsZFC (V := V)

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]
    (φ : SetTheory.Form) (e : ℕ → V) (a : V) :
    ∃ s : V, ∀ x, x ∈ s ↔ (x ∈ a ∧ SetTheory.Sat (memRel V) (SetTheory.scons x e) φ) :=
  LeanProofs.ZFCinPA.sep_clause φ e a

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖]
    (ψ : SetTheory.Form) (e : ℕ → V)
    (hfun : SetTheory.Functional (SetTheory.relOf (memRel V) ψ e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) ψ e y x :=
  LeanProofs.ZFCinPA.repl_clause ψ e hfun a

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] (u : V) :
    ∃ w : V, ∀ x, x ∈ w ↔ ∃ v, x ∈ v ∧ v ∈ u :=
  LeanProofs.ZFCinPA.union_clause u

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] (a : V) :
    ∃ p : V, ∀ x, x ∈ p ↔ SetTheory.Sub (memRel V) x a :=
  LeanProofs.ZFCinPA.pow_clause a

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] :
    ∃ I : V, (∃ e0, e0 ∈ I ∧ ∀ z, ¬ z ∈ e0) ∧
      (∀ x, x ∈ I → ∃ sx, sx ∈ I ∧ ∀ t, t ∈ sx ↔ (t ∈ x ∨ t = x)) :=
  LeanProofs.ZFCinPA.inf_clause (V := V)

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]
    (a : V) (ha : ∃ x, x ∈ a) :
    ∃ m : V, m ∈ a ∧ ¬ ∃ z, z ∈ m ∧ z ∈ a :=
  LeanProofs.ZFCinPA.reg_clause a ha

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    LeanProofs.BoundedZFCConsistency.ChoiceSem (memRel V) :=
  LeanProofs.ZFCinPA.choice_clause (V := V)

example {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    LeanProofs.BoundedZFCConsistency.ZFCAxioms (memRel V) :=
  LeanProofs.ZFCinPA.zfcAxioms_of_models (V := V)

example (n : Nat) : 𝗭𝗙𝗖 ⊢ conZFCSet n :=
  LeanProofs.ZFCinPA.zfc_proves_conZFCSet n

end LeanProofs.ZFCinPA.TranslationFreshAudit
