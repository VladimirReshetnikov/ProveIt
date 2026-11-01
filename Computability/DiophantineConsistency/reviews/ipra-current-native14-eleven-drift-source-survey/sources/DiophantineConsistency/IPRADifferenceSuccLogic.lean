import DiophantineConsistency.IPRADifferenceSuccEq
import DiophantineConsistency.IPRASubSuccZeroNative
import Foundation.Meta.IntProver
/-! The actual native open successor invariant, conditional on its positive reconstruction branch. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceSuccLogic
open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation DiophantineConsistency.IPRANativeDifferenceEquality
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRADifferenceSuccEq
open Rewriting HilbertProofᵢ
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))
variable (a b c d e f : Propositionᵢ language)
def core (hac : extended nativeTheory ⊢! a 🡒 c)
    (hen : extended nativeTheory ⊢! e 🡒 ∼a)
    (hbridge : extended nativeTheory ⊢! b 🡒 (∼d 🡒 f)) :
    extended nativeTheory ⊢! (∼c ⋎ (∼d ⋎ e)) 🡒 (a 🡒 (b 🡒 f)) := by
  have hctx : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! f := by
    have hb : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! b := byAxm₀
    have ha : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! a := byAxm₁
    have hi : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! ∼c ⋎ (∼d ⋎ e) := byAxm₂
    have hcz : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! c := (FiniteContext.of hac) ⨀ ha
    have hncnd : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! ∼c 🡒 ∼d :=
      (Entailment.C_swap Entailment.CNC) ⨀ hcz
    have hena : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! e 🡒 ∼d :=
      Entailment.C_trans (FiniteContext.of hen) ((Entailment.C_swap Entailment.CNC) ⨀ ha)
    have hond : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! (∼d ⋎ e) 🡒 ∼d :=
      Entailment.or₃ ⨀ Entailment.C_id ⨀ hena
    have hnd : [b,a,∼c ⋎ (∼d ⋎ e)] ⊢[extended nativeTheory]! ∼d :=
      Entailment.of_C_of_C_of_A hncnd hond hi
    exact (FiniteContext.of hbridge) ⨀ hb ⨀ hnd
  have h1 := FiniteContext.deduct! ⟨hctx⟩
  have h2 := FiniteContext.deduct! h1
  have h3 := FiniteContext.deduct! h2
  have ht := FiniteContext.toDef (Classical.choice h3)
  simpa using (ht ⨀ (Entailment.verum : extended nativeTheory ⊢! ⊤))
def full (hcore : extended nativeTheory ⊢! (∼c ⋎ (∼d ⋎ e)) 🡒 (a 🡒 (b 🡒 f)))
    (hda : extended nativeTheory ⊢! a ⋎ ∼a)
    (hdb : extended nativeTheory ⊢! b ⋎ ∼b) :
    extended nativeTheory ⊢! (∼c ⋎ (∼d ⋎ e)) 🡒 (∼a ⋎ (∼b ⋎ f)) := by
  let i := ∼c ⋎ (∼d ⋎ e)
  let r := ∼a ⋎ (∼b ⋎ f)
  have hctx : [i] ⊢[extended nativeTheory]! r := by
    have hi : [i] ⊢[extended nativeTheory]! i := byAxm₀
    have ha_case : [i] ⊢[extended nativeTheory] a 🡒 r := by
      apply FiniteContext.deduct!
      let Γ : List (Propositionᵢ language) := [a,i]
      have ha : Γ ⊢[extended nativeTheory]! a := byAxm₀
      have hi' : Γ ⊢[extended nativeTheory]! i := byAxm₁
      have hb_case : Γ ⊢[extended nativeTheory] b 🡒 r := by
        apply FiniteContext.deduct!
        let Δ : List (Propositionᵢ language) := [b,a,i]
        have hb : Δ ⊢[extended nativeTheory]! b := byAxm₀
        have ha' : Δ ⊢[extended nativeTheory]! a := byAxm₁
        have hi'' : Δ ⊢[extended nativeTheory]! i := byAxm₂
        have hf : Δ ⊢[extended nativeTheory]! f := (FiniteContext.of hcore) ⨀ hi'' ⨀ ha' ⨀ hb
        exact ⟨Entailment.or₂ ⨀ (Entailment.or₂ ⨀ hf)⟩
      have hnb_case : Γ ⊢[extended nativeTheory]! ∼b 🡒 r :=
        Entailment.C_trans Entailment.or₁ Entailment.or₂
      exact ⟨Entailment.of_C_of_C_of_A (Classical.choice hb_case) hnb_case (FiniteContext.of hdb)⟩
    have hna_case : [i] ⊢[extended nativeTheory]! ∼a 🡒 r := Entailment.or₁
    exact Entailment.of_C_of_C_of_A (Classical.choice ha_case) hna_case (FiniteContext.of hda)
  have h := FiniteContext.deduct! ⟨hctx⟩
  have ht := FiniteContext.toDef (Classical.choice h)
  simpa using (ht ⨀ (Entailment.verum : extended nativeTheory ⊢! ⊤))

def stepOpen (x y : Term language ℕ)
    (hbridge : extended nativeTheory ⊢! zeroOpen (.func subCode ![y,sx x]) 🡒
      (∼zeroOpen (.func subCode ![y,x]) 🡒 eqAt (sx x) y)) :
    extended nativeTheory ⊢!
      (∼zeroOpen (.func subCode ![x,y]) ⋎ (∼zeroOpen (.func subCode ![y,x]) ⋎ eqAt x y)) 🡒
      (∼zeroOpen (.func subCode ![sx x,y]) ⋎ (∼zeroOpen (.func subCode ![y,sx x]) ⋎ eqAt (sx x) y)) := by
  let A := zeroOpen (.func subCode ![sx x,y])
  let B := zeroOpen (.func subCode ![y,sx x])
  let C := zeroOpen (.func subCode ![x,y])
  let D := zeroOpen (.func subCode ![y,x])
  let E := eqAt x y
  let F := eqAt (sx x) y
  let m : Semisentenceᵢ language 2 :=
    (.rel .eq ![DiophantineConsistency.PRASubSuccZero.leftTerm, DiophantineConsistency.PRASubSuccZero.zeroTerm]) 🡒
    (.rel .eq ![DiophantineConsistency.PRASubSuccZero.rightTerm, DiophantineConsistency.PRASubSuccZero.zeroTerm])
  have hp := instantiateTheory (T := nativeTheory) m DiophantineConsistency.IPRASubSuccZeroNative.native ![y,x]
  have hv1 : (fun i : Fin 2 => Rew.embSubsts ![y,x] (![DiophantineConsistency.PRASubSuccZero.leftTerm, DiophantineConsistency.PRASubSuccZero.zeroTerm] i)) =
    ![.func subCode ![sx x,y], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero =>
      simp [DiophantineConsistency.PRASubSuccZero.leftTerm, Rew.func, Function.comp_def, sx]
      funext j; cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]
      | succ j => cases j using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [DiophantineConsistency.PRASubSuccZero.zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hv2 : (fun i : Fin 2 => Rew.embSubsts ![y,x] (![DiophantineConsistency.PRASubSuccZero.rightTerm, DiophantineConsistency.PRASubSuccZero.zeroTerm] i)) =
    ![.func subCode ![x,y], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp [DiophantineConsistency.PRASubSuccZero.rightTerm, Rew.func, Function.comp_def]; funext j; cases j using Fin.cases <;> simp
    | succ j => cases j using Fin.cases with
      | zero => simp [DiophantineConsistency.PRASubSuccZero.zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hac : extended nativeTheory ⊢! A 🡒 C := by
    simpa [m, A, C, zeroOpen, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv1, hv2] using hp
  have he : extended nativeTheory ⊢! E 🡒 ∼A := equalityNotSuccDiff x y
  have hda : extended nativeTheory ⊢! A ⋎ ∼A := zeroDecOpen (Classical.choice DiophantineConsistency.IPRAZeroStepNative.zero_decidable) _
  have hdb : extended nativeTheory ⊢! B ⋎ ∼B := zeroDecOpen (Classical.choice DiophantineConsistency.IPRAZeroStepNative.zero_decidable) _
  exact full A B C D E F (core A B C D E F hac he hbridge) hda hdb

end DiophantineConsistency.IPRADifferenceSuccLogic
