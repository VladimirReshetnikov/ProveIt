import DiophantineConsistency.IPRASuccLeft
import DiophantineConsistency.IPRASubArithmetic
import DiophantineConsistency.IPRAZeroStepNative
import DiophantineConsistency.IPRAReconstructLogic
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReconstructAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct IPRAAddRecursion IPRASubArithmetic
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def leftAx : Propositionᵢ language := Rewriting.emb (∀⁰ ∀⁰ IPRASuccLeft.matrix)
def zeroDecAx : Propositionᵢ language := Rewriting.emb IPRAZeroDecidable.zeroDecSentence
def predReconAx : Propositionᵢ language := Rewriting.emb (∀⁰ IPRAPredReconstruct.reconstruct)
def zeroLeftAx : Propositionᵢ language := Rewriting.emb (∀⁰ IPRAZeroLeft.matrix)
def F : List (Propositionᵢ language) := [leftAx, zeroDecAx, predReconAx, zeroLeftAx, funAx addCode (0 : Fin 2), funAx addCode (1 : Fin 2), funAx subCode (0 : Fin 2), funAx subCode (1 : Fin 2)] ++ E
theorem lift_E {φ : Propositionᵢ language} (h : E ⊢[𝗜𝗻𝘁¹] φ) : F ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro p hp; simp [F, hp]) (Classical.choice h)⟩
theorem lift_delta {φ : Propositionᵢ language} (h : Δ ⊢[𝗜𝗻𝘁¹] φ) : F ⊢[𝗜𝗻𝘁¹] φ :=
  lift_E (IPRASubArithmetic.lift_delta h)
theorem trans_F {a b c : SyntacticTerm language} (h : F ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : F ⊢[𝗜𝗻𝘁¹] equal b c) : F ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context F (by simp [F,E,Δ,Γ]) a b c) h) j
theorem congr_add {a b c d : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] equal a b) (j : F ⊢[𝗜𝗻𝘁¹] equal c d) :
    F ⊢[𝗜𝗻𝘁¹] equal (add a c) (add b d) := by
  have hx : ∀ i : Fin 2, funAx addCode i ∈ F := by
    intro i; cases i using Fin.cases with
    | zero => simp [F]
    | succ i => cases i using Fin.cases with
      | zero => simp [F]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, F ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCode F (by simp [F,E,Δ,Γ]) (by simp [F,E,Δ,Γ]) hx _ _ hr

theorem left_succ (a b : SyntacticTerm language) : F ⊢[𝗜𝗻𝘁¹] equal (add (sc a) b) (sc (add a b)) := by
  let p : Semiformulaᵢ language ℕ 2 := Rewriting.emb IPRASuccLeft.matrix
  have hc : F ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : F ⊢[𝗜𝗻𝘁¹] leftAx := ⟨FiniteContext.byAxm (by simp [F])⟩
    let q : Semisentenceᵢ language 2 := IPRASuccLeft.matrix
    have hq : F ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by simpa [q, leftAx, allClosure_succ] using ha
    simpa only [p, q, Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![b,a] F hc
  convert hs using 1
  simp [p, IPRASuccLeft.matrix, add, sc, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two]
    | succ i => exact Fin.elim0 i
def J (d p : SyntacticTerm language) : Propositionᵢ language := equal d (sc p)
def K (d p : SyntacticTerm language) : List (Propositionᵢ language) := J d p :: F

theorem lift_F {φ : Propositionᵢ language} {d p : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] φ) : K d p ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [K, hq]) (Classical.choice h)⟩

theorem trans_K {a b c d p : SyntacticTerm language} (h : K d p ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : K d p ⊢[𝗜𝗻𝘁¹] equal b c) : K d p ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (K d p) (by simp [K,F,E,Δ,Γ]) a b c) h) j

theorem congr_add_K {a b c d u v : SyntacticTerm language}
    (h : K u v ⊢[𝗜𝗻𝘁¹] equal a b) (j : K u v ⊢[𝗜𝗻𝘁¹] equal c d) :
    K u v ⊢[𝗜𝗻𝘁¹] equal (add a c) (add b d) := by
  have hx : ∀ i : Fin 2, funAx addCode i ∈ K u v := by
    intro i; cases i using Fin.cases with
    | zero => simp [K,F]
    | succ i => cases i using Fin.cases with
      | zero => simp [K,F]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, K u v ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCode (K u v) (by simp [K,F,E,Δ,Γ]) (by simp [K,F,E,Δ,Γ]) hx _ _ hr

theorem step_addition (a d p : SyntacticTerm language) :
    F ⊢[𝗜𝗻𝘁¹] J d p 🡒 equal (add (sc a) p) (add a d) := by
  apply FiniteContext.deduct!
  have hj : K d p ⊢[𝗜𝗻𝘁¹] J d p := ⟨FiniteContext.byAxm (by simp [K])⟩
  have hs : K d p ⊢[𝗜𝗻𝘁¹] equal (sc p) d :=
    Entailment.mdp! (lift_F (lift_delta (symm_new _ _))) hj
  have hr : K d p ⊢[𝗜𝗻𝘁¹] equal a a := refl_context (K d p) (by simp [K,F,E,Δ,Γ]) a
  have ha : K d p ⊢[𝗜𝗻𝘁¹] equal (add (sc a) p) (sc (add a p)) := lift_F (left_succ a p)
  have hb : K d p ⊢[𝗜𝗻𝘁¹] equal (add a (sc p)) (sc (add a p)) := lift_F (lift_delta (add_succ_open a p))
  have hb' : K d p ⊢[𝗜𝗻𝘁¹] equal (sc (add a p)) (add a (sc p)) :=
    Entailment.mdp! (lift_F (lift_delta (symm_new _ _))) hb
  exact trans_K ha (trans_K hb' (congr_add_K hr hs))
def R (a d y : SyntacticTerm language) : Propositionᵢ language := equal (add a d) y
def K₂ (a d p y : SyntacticTerm language) : List (Propositionᵢ language) := R a d y :: J d p :: F

theorem lift_F2 {φ : Propositionᵢ language} {a d p y : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] φ) : K₂ a d p y ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [K₂, hq]) (Classical.choice h)⟩

theorem trans_K2 {a d p y u v w : SyntacticTerm language} (h : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal u v)
    (j : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal v w) : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal u w := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (K₂ a d p y) (by simp [K₂,F,E,Δ,Γ]) u v w) h) j

theorem congr_binary_K2 {a d p y u v w z : SyntacticTerm language}
    (f : Code 2) (hf : ∀ i : Fin 2, funAx f i ∈ F)
    (h : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal u v) (j : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal w z) :
    K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (.func f ![u,w]) (.func f ![v,z]) := by
  have hx : ∀ i : Fin 2, funAx f i ∈ K₂ a d p y := by intro i; simp [K₂, hf i]
  have hr : ∀ i : Fin 2, K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (![u,w] i) (![v,z] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context f (K₂ a d p y) (by simp [K₂,F,E,Δ,Γ]) (by simp [K₂,F,E,Δ,Γ]) hx _ _ hr

theorem hf_add : ∀ i : Fin 2, funAx addCode i ∈ F := by
  intro i; cases i using Fin.cases with
  | zero => simp [F]
  | succ i => cases i using Fin.cases with
    | zero => simp [F]
    | succ i => exact Fin.elim0 i

theorem hf_sub : ∀ i : Fin 2, funAx subCode i ∈ F := by
  intro i; cases i using Fin.cases with
  | zero => simp [F]
  | succ i => cases i using Fin.cases with
    | zero => simp [F]
    | succ i => exact Fin.elim0 i

theorem reconstruction_step_equation (a y : SyntacticTerm language) :
    F ⊢[𝗜𝗻𝘁¹] J (sub y a) (pred (sub y a)) 🡒 R a (sub y a) y 🡒
      R (add a one) (sub y (add a one)) y := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let d := sub y a
  let p := pred d
  have hj : K₂ a d p y ⊢[𝗜𝗻𝘁¹] J d p := ⟨FiniteContext.byAxm (by simp [K₂])⟩
  have hr : K₂ a d p y ⊢[𝗜𝗻𝘁¹] R a d y := ⟨FiniteContext.byAxm (by simp [K₂])⟩
  have ha : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (add a one) (sc a) := lift_F2 (lift_delta (lift_old (add_one_open a)))
  have hy : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal y y := refl_context (K₂ a d p y) (by simp [K₂,F,E,Δ,Γ]) y
  have hsub1 : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (sub y (add a one)) (sub y (sc a)) :=
    congr_binary_K2 subCode hf_sub hy ha
  have hsub2 : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (sub y (sc a)) p :=
    lift_F2 (lift_E (sub_succ y a))
  have hsub := trans_K2 hsub1 hsub2
  have hfirst : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (add (add a one) (sub y (add a one))) (add (sc a) p) :=
    congr_binary_K2 addCode hf_add ha hsub
  have hsecond : K₂ a d p y ⊢[𝗜𝗻𝘁¹] equal (add (sc a) p) (add a d) :=
    Entailment.mdp! (lift_F2 (step_addition a d p)) hj
  exact trans_K2 hfirst (trans_K2 hsecond hr)
theorem hf_sub_F : ∀ i : Fin 2, funAx subCode i ∈ F := hf_sub

theorem congr_sub_F {a b c d : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] equal a b) (j : F ⊢[𝗜𝗻𝘁¹] equal c d) :
    F ⊢[𝗜𝗻𝘁¹] equal (sub a c) (sub b d) := by
  have hr : ∀ i : Fin 2, F ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context subCode F (by simp [F,E,Δ,Γ]) (by simp [F,E,Δ,Γ]) hf_sub_F _ _ hr

theorem sub_step_eq (a y : SyntacticTerm language) :
    F ⊢[𝗜𝗻𝘁¹] equal (sub y (add a one)) (pred (sub y a)) := by
  have hr := refl_context F (by simp [F,E,Δ,Γ]) y
  exact trans_F (congr_sub_F hr (lift_delta (lift_old (add_one_open a)))) (lift_E (sub_succ y a))

def Z (d : SyntacticTerm language) : Propositionᵢ language := equal d z
def KZ (d : SyntacticTerm language) : List (Propositionᵢ language) := Z d :: F

theorem lift_FZ {φ : Propositionᵢ language} {d : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] φ) : KZ d ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [KZ,hq]) (Classical.choice h)⟩

theorem trans_KZ {a b c d : SyntacticTerm language} (h : KZ d ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : KZ d ⊢[𝗜𝗻𝘁¹] equal b c) : KZ d ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (KZ d) (by simp [KZ,F,E,Δ,Γ]) a b c) h) j

theorem congr_pred_KZ {a b d : SyntacticTerm language} (h : KZ d ⊢[𝗜𝗻𝘁¹] equal a b) :
    KZ d ⊢[𝗜𝗻𝘁¹] equal (pred a) (pred b) := by
  have hx : ∀ i : Fin 1, funAx predCode i ∈ KZ d := by
    intro i; cases i using Fin.cases with
    | zero => simp [KZ,F,E,Δ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context predCode (KZ d) (by simp [KZ,F,E,Δ,Γ]) (by simp [KZ,F,E,Δ,Γ]) hx _ _ (fun _ => h)

theorem zero_step (a y : SyntacticTerm language) :
    F ⊢[𝗜𝗻𝘁¹] Z (sub y a) 🡒 Z (sub y (add a one)) := by
  apply FiniteContext.deduct!
  have hz : KZ (sub y a) ⊢[𝗜𝗻𝘁¹] Z (sub y a) := ⟨FiniteContext.byAxm (by simp [KZ])⟩
  exact trans_KZ (lift_FZ (sub_step_eq a y)) (trans_KZ (congr_pred_KZ hz) (lift_FZ (lift_E pred_zero)))
theorem zero_decision (a : SyntacticTerm language) : F ⊢[𝗜𝗻𝘁¹] Z a ⋎ ∼Z a := by
  let p : Semiformulaᵢ language ℕ 1 := Rewriting.emb IPRAZeroDecidable.zeroDec
  have hc : F ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : F ⊢[𝗜𝗻𝘁¹] zeroDecAx := ⟨FiniteContext.byAxm (by simp [F])⟩
    let q : Semisentenceᵢ language 1 := IPRAZeroDecidable.zeroDec
    have hq : F ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by simpa [q, zeroDecAx, IPRAZeroDecidable.zeroDecSentence, allClosure_succ] using ha
    simpa only [p,q,Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![a] F hc
  convert hs using 1
  simp [p, IPRAZeroDecidable.zeroDec, IPRAZeroDecidable.zeroEq, zeroTerm, Z, z, equal,
    Rewriting.subst, Semiformulaᵢ.rew_rel]
  have hv : ![a, Semiterm.func (Code.zero 0) Fin.elim0] =
      (fun i : Fin 2 => (Rew.subst ![a]) (Rew.emb ((![#0, .func (Code.zero 0) Fin.elim0] : Fin 2 → TermN 1) i))) := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  constructor
  · exact hv
  · rw [← hv]

theorem pred_reconstruct (a : SyntacticTerm language) : F ⊢[𝗜𝗻𝘁¹] Z a ⋎ J a (pred a) := by
  let p : Semiformulaᵢ language ℕ 1 := Rewriting.emb IPRAPredReconstruct.reconstruct
  have hc : F ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : F ⊢[𝗜𝗻𝘁¹] predReconAx := ⟨FiniteContext.byAxm (by simp [F])⟩
    let q : Semisentenceᵢ language 1 := IPRAPredReconstruct.reconstruct
    have hq : F ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by simpa [q, predReconAx, allClosure_succ] using ha
    simpa only [p,q,Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![a] F hc
  convert hs using 1
  simp [p, IPRAPredReconstruct.reconstruct, IPRAPredReconstruct.reconEq, IPRAZeroDecidable.zeroEq,
    zeroTerm, Z, J, z, pred, sc, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => first | rfl | (simp [Rew.func, Function.comp_def]; funext j; first | rfl | exact Fin.elim0 j)
    | succ i => exact Fin.elim0 i
def I (a y : SyntacticTerm language) : Propositionᵢ language := Z (sub y a) ⋎ R a (sub y a) y
def W (a y : SyntacticTerm language) : List (Propositionᵢ language) := I a y :: F

theorem lift_FW {φ : Propositionᵢ language} {a y : SyntacticTerm language}
    (h : F ⊢[𝗜𝗻𝘁¹] φ) : W a y ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro q hq; simp [W,hq]) (Classical.choice h)⟩

theorem reconstruction_step_open (a y : SyntacticTerm language) :
    F ⊢[𝗜𝗻𝘁¹] I a y 🡒 I (add a one) y := by
  apply FiniteContext.deduct!
  let d := sub y a
  let P := Z (sub y (add a one))
  let Q := R (add a one) (sub y (add a one)) y
  have hdec : W a y ⊢[𝗜𝗻𝘁¹] P ⋎ ∼P := lift_FW (zero_decision (sub y (add a one)))
  have hih : W a y ⊢[𝗜𝗻𝘁¹] Z d ⋎ R a d y := ⟨FiniteContext.byAxm (by simp [W,I,d])⟩
  have hz : W a y ⊢[𝗜𝗻𝘁¹] Z d 🡒 P := lift_FW (zero_step a y)
  have hrec : W a y ⊢[𝗜𝗻𝘁¹] Z d ⋎ J d (pred d) := lift_FW (pred_reconstruct d)
  have heq : W a y ⊢[𝗜𝗻𝘁¹] J d (pred d) 🡒 R a d y 🡒 Q :=
    lift_FW (reconstruction_step_equation a y)
  have hl := Classical.choice (IPRAReconstructLogic.reconstruction_step_logic P (Z d) (R a d y) (J d (pred d)) Q)
  have ho : W a y ⊢[𝗜𝗻𝘁¹] P ⋎ Q :=
    ⟨FiniteContext.of hl ⨀ Classical.choice hdec ⨀ Classical.choice hih ⨀
      Classical.choice hz ⨀ Classical.choice hrec ⨀ Classical.choice heq⟩
  exact ho
theorem zero_left (a : SyntacticTerm language) : F ⊢[𝗜𝗻𝘁¹] equal (add z a) a := by
  let p : Semiformulaᵢ language ℕ 1 := Rewriting.emb IPRAZeroLeft.matrix
  have hc : F ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    have ha : F ⊢[𝗜𝗻𝘁¹] zeroLeftAx := ⟨FiniteContext.byAxm (by simp [F])⟩
    let q : Semisentenceᵢ language 1 := IPRAZeroLeft.matrix
    have hq : F ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by simpa [q, zeroLeftAx, allClosure_succ] using ha
    simpa only [p,q,Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![a] F hc
  convert hs using 1
  simp [p, IPRAZeroLeft.matrix, zeroTerm, z, add, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem reconstruction_base_open (y : SyntacticTerm language) : F ⊢[𝗜𝗻𝘁¹] I z y := by
  have hz := refl_context F (by simp [F,E,Δ,Γ]) z
  have hs := lift_E (sub_zero y)
  have hp := trans_F (congr_add hz hs) (zero_left y)
  exact Entailment.A!_intro_right hp
end DiophantineConsistency.IPRAReconstructAlgebra
