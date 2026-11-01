import DiophantineConsistency.IPRAReconstructClosure
import DiophantineConsistency.IPRASubPredZeroNative
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReconstructBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct IPRAAddRecursion IPRASubArithmetic IPRAReconstructAlgebra
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def recAx : Propositionᵢ language := Rewriting.emb (∀⁰ ∀⁰ IPRAReconstructClosure.matrix)
def subPredAx : Propositionᵢ language := Rewriting.emb IPRASubPredZeroNative.result
def B : List (Propositionᵢ language) := [recAx, subPredAx] ++ F

theorem lift_F {φ : Propositionᵢ language} (h : F ⊢[𝗜𝗻𝘁¹] φ) : B ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [B,hq]) (Classical.choice h)⟩

theorem reconstruction (x y : SyntacticTerm language) : B ⊢[𝗜𝗻𝘁¹] Z (sub y x) ⋎ R x (sub y x) y := by
  let p : Semiformulaᵢ language ℕ 2 := Rewriting.emb IPRAReconstructClosure.matrix
  have hc : B ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : B ⊢[𝗜𝗻𝘁¹] recAx := ⟨FiniteContext.byAxm (by simp [B])⟩
    let q : Semisentenceᵢ language 2 := IPRAReconstructClosure.matrix
    have hq : B ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by simpa [q, recAx, allClosure_succ] using ha
    simpa only [p,q,Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![x,y] B hc
  convert hs using 1
  simp [p, IPRAReconstructClosure.matrix, zeroTerm, Z, R, IPRASubArithmetic.sub, add, z, equal,
    Rewriting.subst, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => simp [Rew.func, Matrix.fun_eq_vec_two]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two] <;> funext j <;> exact Fin.elim0 j
    | succ i => exact Fin.elim0 i

theorem pred_zero_of_subsucc_zero (x y : SyntacticTerm language) :
    B ⊢[𝗜𝗻𝘁¹] Z (sub y (sc x)) 🡒 Z (pred (sub y x)) := by
  let q : Semisentenceᵢ language 2 :=
    (.rel .eq ![PRASubPredZero.leftTerm, PRASubPredZero.zeroTerm]) 🡒
    (.rel .eq ![PRASubPredZero.rightTerm, PRASubPredZero.zeroTerm])
  let p : Semiformulaᵢ language ℕ 2 := Rewriting.emb q
  have hc : B ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : B ⊢[𝗜𝗻𝘁¹] subPredAx := ⟨FiniteContext.byAxm (by simp [B])⟩
    have hq : B ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by
      simpa [q, subPredAx, IPRASubPredZeroNative.result, allClosure_succ] using ha
    simpa only [p,q,Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![x,y] B hc
  convert hs using 1
  simp [p, q, PRASubPredZero.leftTerm, PRASubPredZero.rightTerm, PRASubPredZero.zeroTerm,
    Z, z, IPRASubArithmetic.sub, pred, sc, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two]; funext j; exact Fin.elim0 j
    | succ i => exact Fin.elim0 i
def H (x y : SyntacticTerm language) : List (Propositionᵢ language) :=
  ∼Z (sub y x) :: Z (sub y (sc x)) :: B

theorem lift_B {φ : Propositionᵢ language} {x y : SyntacticTerm language}
    (h : B ⊢[𝗜𝗻𝘁¹] φ) : H x y ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [H,hq]) (Classical.choice h)⟩

theorem trans_H {x y a b c : SyntacticTerm language} (h : H x y ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : H x y ⊢[𝗜𝗻𝘁¹] equal b c) : H x y ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (H x y) (by simp [H,B,F,E,Δ,Γ]) a b c) h) j

theorem congr_add_H {x y a b c d : SyntacticTerm language}
    (h : H x y ⊢[𝗜𝗻𝘁¹] equal a b) (j : H x y ⊢[𝗜𝗻𝘁¹] equal c d) :
    H x y ⊢[𝗜𝗻𝘁¹] equal (add a c) (add b d) := by
  have hf : ∀ i : Fin 2, funAx addCode i ∈ H x y := by intro i; simp [H,B, hf_add i]
  have hr : ∀ i : Fin 2, H x y ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCode (H x y) (by simp [H,B,F,E,Δ,Γ]) (by simp [H,B,F,E,Δ,Γ]) hf _ _ hr

theorem successor_bridge_open (x y : SyntacticTerm language) : B ⊢[𝗜𝗻𝘁¹]
    Z (sub y (sc x)) 🡒 ∼Z (sub y x) 🡒 equal (sc x) y := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let d := sub y x
  let p := pred d
  have hnonzero : H x y ⊢[𝗜𝗻𝘁¹] ∼Z d := ⟨FiniteContext.byAxm (by simp [H,d])⟩
  have hzero : H x y ⊢[𝗜𝗻𝘁¹] Z (sub y (sc x)) := ⟨FiniteContext.byAxm (by simp [H])⟩
  have hrec : H x y ⊢[𝗜𝗻𝘁¹] Z d ⋎ R x d y := lift_B (reconstruction x y)
  have hpred : H x y ⊢[𝗜𝗻𝘁¹] Z d ⋎ J d p := lift_B (lift_F (pred_reconstruct d))
  have hR : H x y ⊢[𝗜𝗻𝘁¹] R x d y := Entailment.A!_cases (Entailment.C_of_N hnonzero) ⟨Entailment.C_id⟩ hrec
  have hJ : H x y ⊢[𝗜𝗻𝘁¹] J d p := Entailment.A!_cases (Entailment.C_of_N hnonzero) ⟨Entailment.C_id⟩ hpred
  have hp0 : H x y ⊢[𝗜𝗻𝘁¹] Z p := Entailment.mdp! (lift_B (pred_zero_of_subsucc_zero x y)) hzero
  have hstep : H x y ⊢[𝗜𝗻𝘁¹] equal (add (sc x) p) (add x d) :=
    Entailment.mdp! (lift_B (lift_F (step_addition x d p))) hJ
  have hrefl : H x y ⊢[𝗜𝗻𝘁¹] equal (sc x) (sc x) := refl_context (H x y) (by simp [H,B,F,E,Δ,Γ]) (sc x)
  have hzeroadd : H x y ⊢[𝗜𝗻𝘁¹] equal (add (sc x) z) (sc x) :=
    lift_B (lift_F (lift_delta (add_zero_open (sc x))))
  have hleft : H x y ⊢[𝗜𝗻𝘁¹] equal (add (sc x) p) (sc x) :=
    trans_H (congr_add_H hrefl hp0) hzeroadd
  have hleft' : H x y ⊢[𝗜𝗻𝘁¹] equal (sc x) (add (sc x) p) :=
    Entailment.mdp! (lift_B (lift_F (lift_delta (symm_new _ _)))) hleft
  exact trans_H hleft' (trans_H hstep hR)
def matrix : Semisentenceᵢ language 2 :=
  (.rel .eq ![.func subCode ![#1, .func .succ (fun _ => #0)], zeroTerm 2]) 🡒
  ∼(.rel .eq ![.func subCode ![#1,#0], zeroTerm 2]) 🡒
  (.rel .eq ![.func .succ (fun _ => #0), #1])

theorem bridge_closed : B ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ Rewriting.emb matrix := by
  have hB : B⁺ = B := by
    simp [B, recAx, subPredAx, IPRAReconstructClosure.shift_embedded,
      F, leftAx, zeroDecAx, predReconAx, zeroLeftAx, E, subBaseAx, subStepAx, predBaseAx,
      Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hB]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hB]
  have ho := Classical.choice (successor_bridge_open (&0) (&1))
  convert ho using 1
  simp [matrix, Z, z, IPRASubArithmetic.sub, sc, equal, zeroTerm, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def]
  have h1 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb
      ((![.func subCode ![#1, .func .succ (fun _ => #0)], zeroTerm 2] : Fin 2 → TermN 2) i)))) =
      ![.func subCode ![&1, .func .succ (fun _ => &0)], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, IPRAReconstructClosure.var_one]
    | succ i => cases i using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have h2 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb
      ((![.func subCode ![#1,#0], zeroTerm 2] : Fin 2 → TermN 2) i)))) =
      ![.func subCode ![&1,&0], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Matrix.fun_eq_vec_two, IPRAReconstructClosure.var_one]
    | succ i => cases i using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have h3 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb
      ((![.func .succ (fun _ => #0), #1] : Fin 2 → TermN 2) i)))) =
      ![.func (Code.succ : Code 1) (fun _ => &0), &1] := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => cases i using Fin.cases with
      | zero => exact IPRAReconstructClosure.var_one
      | succ i => exact Fin.elim0 i
  simpa [zeroTerm, Semiformulaᵢ.neg_def] using And.intro h1 (And.intro h2 h3)
theorem successor_bridge : nativeTheory ⊢ ∀⁰ ∀⁰ matrix := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hB : ∀ p ∈ B, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [B, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | hp
    · exact IPRAReconstructClosure.reconstruction
    · exact IPRASubPredZeroNative.native_provable
    · exact IPRAReconstructClosure.f_theory p ⟨FiniteContext.byAxm hp⟩
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀B := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hB
  have hi := Context.mdp (Context.of (FiniteContext.toDef (Classical.choice bridge_closed))) (Classical.choice hc)
  change Θ *⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰ ∀⁰ matrix)
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]
end DiophantineConsistency.IPRAReconstructBridge
