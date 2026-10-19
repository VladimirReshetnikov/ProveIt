import ZFCinPA.NativeInterp

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA SetTheory.BusyBeaver.ZFC
open LeanProofs.ZFCinPA.NativeInterp

#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_closeS
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_eqS
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_memS
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_domS
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_eqS'
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_memS'
#print axioms LeanProofs.ZFCinPA.NativeInterp.term_cases
#print axioms LeanProofs.ZFCinPA.NativeInterp.val_cons
#print axioms LeanProofs.ZFCinPA.NativeInterp.cls_cons
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_domAtS
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_atomI
#print axioms LeanProofs.ZFCinPA.NativeInterp.eval_intF
#print axioms LeanProofs.ZFCinPA.NativeInterp.shift_quote_sen
#print axioms LeanProofs.ZFCinPA.NativeInterp.isSemiformula_quote_sen
#print axioms LeanProofs.ZFCinPA.NativeInterp.dom_PN
#print axioms LeanProofs.ZFCinPA.NativeInterp.atomOf_PN
#print axioms LeanProofs.ZFCinPA.NativeInterp.good_PN
#print axioms LeanProofs.ZFCinPA.NativeInterp.quote_embSubsts
#print axioms LeanProofs.ZFCinPA.NativeInterp.quote_domAtS
#print axioms LeanProofs.ZFCinPA.NativeInterp.quote_intF

section Semantics
variable {M : Type} [Nonempty M] [SetStructure M]
  [M↓[ℒₛₑₜ] ⊧* NativeSet.nativeTheory]

example {k : ℕ} (φ : SetTheorySemiproposition (k + 1)) (b : Fin (k + 1) → M)
    (ε : Empty → M) : (closeS φ).Eval b ε ↔ φ.Eval b (fun _ ↦ b 0) :=
  eval_closeS φ b ε

example (x y : M) (ε : Empty → M) :
    eqS.Eval ![x, y] ε ↔ ProfileCollection.Eqv (memRel M) x y :=
  eval_eqS x y ε

example (x y : M) (ε : Empty → M) :
    memS.Eval ![x, y] ε ↔ ProfileComposition.Member (memRel M) x y :=
  eval_memS x y ε

example (x : M) (ε : Empty → M) :
    domS.Eval ![x] ε ↔ WellFoundedPart.WF (qm (M := M)) (cl x) :=
  eval_domS x ε

example (w : Fin 2 → M) (ε : Empty → M) :
    eqS.Eval w ε ↔ ProfileCollection.Eqv (memRel M) (w 0) (w 1) :=
  eval_eqS' w ε

example (w : Fin 2 → M) (ε : Empty → M) :
    memS.Eval w ε ↔ ProfileComposition.Member (memRel M) (w 0) (w 1) :=
  eval_memS' w ε

example {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n)
    (b : Fin n → {x : M // D x}) (f : ξ → {x : M // D x}) :
    ∃ u : {x : M // D x}, t.val (Subtype.val ∘ b) (Subtype.val ∘ f) = u.1 ∧
      t.val (cls ∘ b) (cls ∘ f) = cls u :=
  term_cases t b f

example {n : ℕ} (x : {x : M // D x}) (b : Fin n → {x : M // D x}) :
    Subtype.val ∘ (x :> b) = (x.1 :> Subtype.val ∘ b) :=
  val_cons x b

example {n : ℕ} (x : {x : M // D x}) (b : Fin n → {x : M // D x}) :
    cls ∘ (x :> b) = (cls x :> cls ∘ b) :=
  cls_cons x b

example {ξ : Type*} {n : ℕ} (x : M) (e : Fin n → M) (ε : ξ → M) :
    (domAtS n : Semiformula ℒₛₑₜ ξ (n + 1)).Eval (x :> e) ε ↔ D x :=
  eval_domAtS x e ε

example {ξ : Type*} {n k : ℕ} (R : (ℒₛₑₜ).Rel k)
    (v : Fin k → Semiterm ℒₛₑₜ ξ n) (b : Fin n → {x : M // D x})
    (f : ξ → {x : M // D x}) :
    (atomI R v).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔
      (Semiformula.rel R v).Eval (cls ∘ b) (cls ∘ f) :=
  eval_atomI R v b f

example {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n)
    (b : Fin n → {x : M // D x}) (f : ξ → {x : M // D x}) :
    (intF φ).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔
      φ.Eval (cls ∘ b) (cls ∘ f) :=
  eval_intF φ b f

example {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1))
    (b : Fin n → {x : M // D x}) (f : ξ → {x : M // D x}) :
    (intF (∀⁰ φ)).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔
      (∀⁰ φ).Eval (cls ∘ b) (cls ∘ f) :=
  eval_intF (∀⁰ φ) b f
end Semantics

section Codes
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation
open LeanProofs.BoundedPAConsistency.InternalRelativization
variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    shift ℒₛₑₜ (⌜σ⌝ : W) = ⌜σ⌝ := shift_quote_sen σ

example {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    IsSemiformula ℒₛₑₜ (k : W) (⌜σ⌝ : W) := isSemiformula_quote_sen σ

example : dom (PN : W) = ⌜domS⌝ := dom_PN

example (R : W) : atomOf (PN : W) R = if R = 0 then ⌜eqS⌝ else ⌜memS⌝ :=
  atomOf_PN R

example : Good (PN : W) := good_PN

example {k n : ℕ} (σ : Semisentence ℒₛₑₜ k)
    (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) :
    (⌜(Rew.embSubsts v ▹ σ : SetTheorySemiproposition n)⌝ : W) =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm W ℒₛₑₜ n)) ⌜σ⌝ :=
  quote_embSubsts σ v

example (n : ℕ) : (⌜(domAtS n : SetTheorySemiproposition (n + 1))⌝ : W) = ⌜domS⌝ :=
  quote_domAtS n

example {n : ℕ} (φ : SetTheorySemiproposition n) :
    (⌜intF φ⌝ : W) = interp (PN : W) ⌜φ⌝ := quote_intF φ

example {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) :
    (⌜intF (∃⁰ φ)⌝ : W) = interp (PN : W) ⌜(∃⁰ φ : SetTheorySemiproposition n)⌝ :=
  quote_intF (∃⁰ φ)
end Codes
