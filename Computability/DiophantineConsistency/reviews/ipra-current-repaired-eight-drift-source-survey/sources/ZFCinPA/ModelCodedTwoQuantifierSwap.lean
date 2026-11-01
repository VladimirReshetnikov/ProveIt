import ZFCinPA.ModelCodedBindOneSwap

set_option autoImplicit false

/-!
Finite internal double-universal exchange proof for arbitrary typed matrices.
The generalized rule retains two actual context SHIFTs. No target axiom,
standard-matrix or free-variable support premise is used.
-/
namespace LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def generalizeTwo (T : InternalTheory V L)
    {Γ : List (Formula V L)} {p : Bootstrapping.Semiformula V L 2}
    (d : Γ.map (fun r => r.shift.shift) ⊢[T]!
      p.shift.shift.subst ![Semiterm.fvar 0,Semiterm.fvar 1]) :
    Γ ⊢[T]! ∀⁰ ∀⁰ p := by
  apply TProof.generalize
  suffices Γ.map Bootstrapping.Semiformula.shift ⊢[T]!
      ∀⁰ (p.shift.subst ![Semiterm.bvar 0,Semiterm.fvar 0]) by
    simpa [Bootstrapping.Semiformula.free,SemitermVec.q] using this
  apply TProof.generalize
  simpa [Bootstrapping.Semiformula.free,SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    List.map_map,Function.comp_def] using d

noncomputable def allSwap (T : InternalTheory V L)
    (p : Bootstrapping.Semiformula V L 2) :
    T ⊢! (∀⁰ ∀⁰ p) 🡒
      (∀⁰ ∀⁰ (p.subst ![Semiterm.bvar 1,Semiterm.bvar 0])) := by
  apply FiniteContext.deduct'
  apply generalizeTwo T
  have h : [(∀⁰ ∀⁰ p).shift.shift] ⊢[T]! ∀⁰ ∀⁰ p.shift.shift := by
    simpa using (FiniteContext.byAxm₀ (𝓢 := T) (Γ := [])
      (φ := (∀⁰ ∀⁰ p).shift.shift))
  have h1 : [(∀⁰ ∀⁰ p).shift.shift] ⊢[T]!
      ∀⁰ (p.shift.shift.subst ![Semiterm.bvar 0,Semiterm.fvar 0]) := by
    simpa [SemitermVec.q] using (TProof.specializeWithCtx h (Semiterm.fvar (0 : V)))
  have h2 := TProof.specializeWithCtx h1 (Semiterm.fvar (1 : V))
  simpa [Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs]
    using h2

lemma typed_swap_val (p : Bootstrapping.Semiformula V L 2) :
    (p.subst (![Semiterm.bvar 1,Semiterm.bvar 0] : SemitermVec V L 2 2)).val =
      subst L (swapVec L (0 : V)) p.val := by
  simp [swapVec,Bootstrapping.Semiformula.val_substs,SemitermVec.val_cons,
    Semiterm.bvar_val,Nat.cast_zero,Nat.cast_one]

end LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap
