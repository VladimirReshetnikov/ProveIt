import PA194ComprehensionShift
import PA194InternalEmpty
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PA194ComprehensionBase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalSingleton PA194ComprehensionStep PA194ComprehensionShift PA194InternalOrder PA194InternalEmpty
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def predicate (P : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∃⁰ ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏ P.subst ![Bootstrapping.Semiterm.bvar 0]))

theorem base_correct (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Arithmetic.typedNumeral 0) 🡘
        (Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Arithmetic.typedNumeral 0) ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let A : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Arithmetic.typedNumeral 0)
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Arithmetic.typedNumeral 0)
  change T ⊢ ∀⁰ (A 🡘 (B ⋏ P))
  have hA : T ⊢ ∀⁰ ∼A := by simpa [A,PA194ConditionalSingleton.Bit] using (internal_PA_empty_explicit (V := V))
  have hB : T ⊢ ∀⁰ ∼B := by simpa [B,Lt] using (internal_PA_zero_explicit (V := V))
  apply Nonempty.intro
  apply FiniteContext.emptyPrf
  apply TProof.generalize
  simp only [List.map_nil]
  have hAs : T ⊢! ∀⁰ (∼A).shift := by simpa using TProof.shift hA.some
  have hBs : T ⊢! ∀⁰ (∼B).shift := by simpa using TProof.shift hB.some
  have hnA : [] ⊢[T]! ∼A.free := by
    have h := TProof.specializeWithCtx (FiniteContext.of hAs : [] ⊢[T]! ∀⁰ (∼A).shift) (Bootstrapping.Semiterm.fvar 0)
    simpa [Bootstrapping.Semiformula.free] using h
  have hnB : [] ⊢[T]! ∼B.free := by
    have h := TProof.specializeWithCtx (FiniteContext.of hBs : [] ⊢[T]! ∀⁰ (∼B).shift) (Bootstrapping.Semiterm.fvar 0)
    simpa [Bootstrapping.Semiformula.free] using h
  have hgood : [] ⊢[T]! A.free 🡘 (B.free ⋏ P.free) := by
    apply E_intro
    · exact CNC ⨀ hnA
    · apply FiniteContext.deduct
      have hbp : [B.free ⋏ P.free] ⊢[T]! B.free ⋏ P.free := FiniteContext.byAxm (by simp)
      have hn : [B.free ⋏ P.free] ⊢[T]! ∼B.free := FiniteContext.weakening (by simp) hnB
      have hc : [B.free ⋏ P.free] ⊢[T]! ∼B.free 🡒 B.free 🡒 A.free := CNC
      exact hc ⨀ hn ⨀ K_left hbp
  simpa [Bootstrapping.Semiformula.free] using hgood

theorem induction_base (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (predicate P).subst ![⌜(‘0’ : ArithmeticSemiterm Nat 0)⌝] := by
  simp only [predicate,Bootstrapping.Semiformula.substs_ex]
  apply TProof.exs! (Bootstrapping.Arithmetic.typedNumeral 0)
  simpa [predicate,PA194ConditionalSingleton.Bit,Lt,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using base_correct P
#print axioms induction_base
#print axioms base_correct
end PA194ComprehensionBase
