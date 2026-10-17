import ZFCinPA.NativeZFContainers254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.NativeZFContainers254
variable {M : Type*} [SetStructure M] [Nonempty M]
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.eval_toSet
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.sep_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.sat_totalGraphF
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.sat_carveF
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.repl_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.pair_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.union_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.succ_exists
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.inf_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.pow_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.reg_clause
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.zfAxioms_of_models
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.power_containers
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.zf_container_sentence
#print axioms LeanProofs.ZFCinPA.NativeZFContainers254.zf_containerRow_sentence
example (phi : SetTheory.Form) (k : Nat) (b : Fin k → M) (f e : Nat → M)
    (hb : ∀ i : Fin k, b i = e i.val) (hf : ∀ j, f j = e (k+j)) :
    (toSet k phi).Eval b f ↔ SetTheory.Sat (memRel M) e phi := eval_toSet phi k b f e hb hf
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (phi : SetTheory.Form) (e : Nat → M) (a : M) :
    ∃ s : M, ∀ x, x ∈ s ↔ x ∈ a ∧ SetTheory.Sat (memRel M) (SetTheory.scons x e) phi := sep_clause phi e a
example (psi : SetTheory.Form) (e : Nat → M) (x y : M) :
    SetTheory.Sat (memRel M) (SetTheory.scons x (SetTheory.scons y e)) (totalGraphF psi) ↔
      (SetTheory.relOf (memRel M) psi e y x ∨ ((¬ ∃ z, SetTheory.relOf (memRel M) psi e z x) ∧ y = x)) :=
  sat_totalGraphF psi e x y
example (psi : SetTheory.Form) (e : Nat → M) (a y : M) :
    SetTheory.Sat (memRel M) (SetTheory.scons y (SetTheory.scons a e)) (carveF psi) ↔
      ∃ x, x ∈ a ∧ SetTheory.relOf (memRel M) psi e y x := sat_carveF psi e a y
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (psi : SetTheory.Form) (e : Nat → M)
    (hfun : SetTheory.Functional (SetTheory.relOf (memRel M) psi e)) (a : M) :
    ∃ r : M, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ SetTheory.relOf (memRel M) psi e y x := repl_clause psi e hfun a
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x y : M) :
    ∃ p : M, ∀ z, z ∈ p ↔ z = x ∨ z = y := pair_clause x y
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (u : M) :
    ∃ w : M, ∀ x, x ∈ w ↔ ∃ v, x ∈ v ∧ v ∈ u := union_clause u
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x : M) :
    ∃ s : M, ∀ z, z ∈ s ↔ z ∈ x ∨ z = x := succ_exists x
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ∃ I : M, (∃ e0, e0 ∈ I ∧ ∀ z, ¬ z ∈ e0) ∧
      (∀ x, x ∈ I → ∃ sx, sx ∈ I ∧ ∀ t, t ∈ sx ↔ t ∈ x ∨ t = x) := inf_clause
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : M) :
    ∃ p : M, ∀ z, z ∈ p ↔ SetTheory.Sub (memRel M) z a := pow_clause a
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : M) (ha : ∃ x, x ∈ a) :
    ∃ m : M, m ∈ a ∧ ¬ ∃ z, z ∈ m ∧ z ∈ a := reg_clause a ha
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : SetTheory.ZFAxioms (memRel M) := zfAxioms_of_models
example [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : M) :
    ∃ v : M, a ∈ v ∧ ∀ x, x ∈ v →
      (∀ z, z ∈ x → z ∈ v) ∧ ∃ p, p ∈ v ∧ ∀ z, (∀ u, u ∈ z → u ∈ x) → z ∈ p := power_containers a
example : (𝗭𝗙 : SetTheory) ⊢ containerSentence := zf_container_sentence
example : (𝗭𝗙 : SetTheory) ⊢ containerRowSentence := zf_containerRow_sentence
