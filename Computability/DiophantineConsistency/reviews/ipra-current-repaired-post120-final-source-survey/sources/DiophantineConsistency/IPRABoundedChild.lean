import DiophantineConsistency.IPRACharacteristicTransfer
import DiophantineConsistency.PRABoundedFormula
import DiophantineConsistency.IPRASelectorSearchBinding
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAGuardedSelector
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ DiophantineConsistency.IPRABoundedErasureLogic
open DiophantineConsistency.IPRASelectorStability
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

def guarded {g p q : Semipropositionᵢ L 1} (t : Term L ℕ)
    (hforward : Λ ⊢! free p 🡒 free q)
    (hback : Λ ⊢! q/[t] 🡒 p/[t])
    (hselector : Λ ⊢! free (g ⋏ q) 🡒 shift ((g ⋏ q)/[t]))
    (hstable : Λ ⊢! ∼∼((g ⋏ q)/[t]) 🡒 (g ⋏ q)/[t]) :
    Λ ⊢! ∼∼(∃⁰ (g ⋏ p)) 🡒 ∃⁰ (g ⋏ p) := by
  apply stableExistsOfCharacteristic (g ⋏ p) (g ⋏ q) t ?_ hselector hstable ?_
  · simpa using (eraseAnd (Λ := Λ) Entailment.C_id hforward)
  · simpa using (eraseAnd (Λ := Λ) Entailment.C_id hback)
end DiophantineConsistency.IPRAGuardedSelector

namespace DiophantineConsistency.IPRABoundedChild
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler
open IPRANativeFormula IPRANativeTheory IPRATheoryHilbertBridge IPRANativeOpenDecidable
open IPRASelectorSearchBinding IPRACharacteristicTransfer IPRAGuardedSelector PRABoundedSelector
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def assign {n : ℕ} (v : Fin (n+1) → Term language ℕ) : Fin (n+2) → Semiterm language ℕ 1 :=
  Fin.cases (#0) (fun i => Rew.bShift (v i))
def guard {n : ℕ} (v : Fin (n+1) → Term language ℕ) : Semipropositionᵢ language 1 :=
  native (Rew.embSubsts (assign v) ▹ (.rel .lt ![#0,#1] : Semisentence language (n+2)))
def test {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) : Semipropositionᵢ language 1 :=
  native (Rew.embSubsts (assign v) ▹ (.rel .eq ![goodWitnessTerm good,zeroTerm] : Semisentence language (n+2)))
theorem splitTest {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) :
    native (boundTest good v) = guard v ⋏ test good v := by
  simp [boundTest, IPRASelectorSearchBinding.test, guard, test, assign, IPRANativeFormula.native]
  constructor <;> rfl

def stableBounded {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ)
    (p : Semipropositionᵢ language 1)
    (hf : extended nativeTheory ⊢! Rewriting.free p 🡒 Rewriting.free (test good v))
    (hb : extended nativeTheory ⊢! (test good v)/[selected good v] 🡒 p/[selected good v]) :
    extended nativeTheory ⊢! ∼∼(∃⁰ (guard v ⋏ p)) 🡒 ∃⁰ (guard v ⋏ p) := by
  have hs := selectorAt good v
  rw [splitTest] at hs
  have ho : (boundTest good v)/[selected good v] |>.Open := by
    simpa using boundTest_open good v
  have hst := openStable ((boundTest good v)/[selected good v]) ho
  have heq : (native (boundTest good v))/[selected good v] = native ((boundTest good v)/[selected good v]) := by
    simp only [← IPRANativeFormulaRew.native_rew]
  rw [← heq, splitTest] at hst
  exact guarded (selected good v) hf hb hs hst
def childBody {n : ℕ} (φ : Semisentence language (n+1)) (v : Fin (n+1) → Term language ℕ) : Semipropositionᵢ language 1 :=
  native (Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (v i.succ))) ▹ φ)
def freeVal {n : ℕ} (v : Fin (n+1) → Term language ℕ) : Fin (n+1) → Term language ℕ :=
  Fin.cases (&0) (fun i => Rew.shift (v i.succ))
def chosenVal {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) : Fin (n+1) → Term language ℕ :=
  Fin.cases (selected good v) (fun i => v i.succ)

theorem childFree {n : ℕ} (φ : Semisentence language (n+1)) (v : Fin (n+1) → Term language ℕ) :
    Rewriting.free (childBody φ v) = native (Rew.embSubsts (freeVal v) ▹ φ) := by
  have hrew : (Rew.free (L := language) (n := 0)).comp
      (Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (v i.succ)))) = Rew.embSubsts (freeVal v) := by
    ext i
    · cases i using Fin.cases with
      | zero => change Rew.free (#0 : Semiterm language ℕ 1) = &0; rfl
      | succ i => change (Rew.free.comp Rew.bShift) (v i.succ) = Rew.shift (v i.succ); rw [Rew.bShift_free_eq_shift]
    · exact Empty.elim i
  simp only [childBody, ← IPRANativeFormulaRew.native_rew, Rewriting.free,
    ← TransitiveRewriting.comp_app, hrew]

theorem childChosen {n : ℕ} (φ : Semisentence language (n+1)) (good : Code (n+1))
    (v : Fin (n+1) → Term language ℕ) :
    (childBody φ v)/[selected good v] = native (Rew.embSubsts (chosenVal good v) ▹ φ) := by
  have hsubst : (Rew.subst ![selected good v]).comp (Rew.bShift : Rew language ℕ 0 ℕ 1) = Rew.id := by
    ext i
    · exact Fin.elim0 i
    · change (Rew.subst ![selected good v]) (&i) = &i
      exact Rew.subst_fvar _ _
  have hrew : (Rew.subst ![selected good v]).comp
      (Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (v i.succ)))) = Rew.embSubsts (chosenVal good v) := by
    ext i
    · cases i using Fin.cases with
      | zero => change (Rew.subst ![selected good v]) (#0) = selected good v; simp
      | succ i => change ((Rew.subst ![selected good v]).comp Rew.bShift) (v i.succ) = v i.succ; rw [hsubst]; rfl
    · exact Empty.elim i
  simp only [childBody, ← IPRANativeFormulaRew.native_rew, Rewriting.subst,
    ← TransitiveRewriting.comp_app, hrew]
theorem testFree {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) :
    Rewriting.free (test good v) = IPRABitConvention.eq (.func good (freeVal v)) IPRABitConvention.zero := by
  have hrew : (Rew.free (L := language) (n := 0)).comp (Rew.embSubsts (assign v)) =
      Rew.embSubsts (Fin.cases (&0) (fun i => Rew.shift (v i))) := by
    ext i
    · cases i using Fin.cases with
      | zero => change Rew.free (#0 : Semiterm language ℕ 1) = &0; rfl
      | succ i => change (Rew.free.comp Rew.bShift) (v i) = Rew.shift (v i); rw [Rew.bShift_free_eq_shift]
    · exact Empty.elim i
  unfold test
  rw [← IPRANativeFormulaRew.native_rew, Rewriting.free, ← TransitiveRewriting.comp_app, hrew,
    IPRANativeFormulaRew.native_rew]
  simp [IPRANativeFormula.native, IPRABitConvention.eq, IPRABitConvention.zero, goodWitnessTerm,
    zeroTerm, applyCode, Function.comp_def]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases <;> rfl
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
    | succ i => exact Fin.elim0 i
theorem testChosen {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) :
    (test good v)/[selected good v] = IPRABitConvention.eq (.func good (chosenVal good v)) IPRABitConvention.zero := by
  have hsubst : (Rew.subst ![selected good v]).comp (Rew.bShift : Rew language ℕ 0 ℕ 1) = Rew.id := by
    ext i
    · exact Fin.elim0 i
    · change (Rew.subst ![selected good v]) (&i) = &i
      exact Rew.subst_fvar _ _
  have hrew : (Rew.subst ![selected good v]).comp (Rew.embSubsts (assign v)) =
      Rew.embSubsts (Fin.cases (selected good v) (fun i => v i)) := by
    ext i
    · cases i using Fin.cases with
      | zero => change (Rew.subst ![selected good v]) (#0) = selected good v; simp
      | succ i => change ((Rew.subst ![selected good v]).comp Rew.bShift) (v i) = v i; rw [hsubst]; rfl
    · exact Empty.elim i
  unfold test
  rw [← IPRANativeFormulaRew.native_rew, Rewriting.subst, ← TransitiveRewriting.comp_app, hrew,
    IPRANativeFormulaRew.native_rew]
  simp [IPRANativeFormula.native, IPRABitConvention.eq, IPRABitConvention.zero, goodWitnessTerm,
    zeroTerm, applyCode, Function.comp_def]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases <;> rfl
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
    | succ i => exact Fin.elim0 i
def stableFromClassical {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (hbit : PRA ⊢ PRACharacteristicBit.bitSentence c)
    (hcorrect : PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence c φ)
    (v : Fin (n+1) → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! ∼∼(∃⁰ (guard v ⋏ childBody φ v)) 🡒 ∃⁰ (guard v ⋏ childBody φ v) := by
  let good := notCode c
  have hfree := transferZeroCorrectness c φ hbit hcorrect (freeVal v) (hback (freeVal v))
  have hchosen := transferZeroCorrectness c φ hbit hcorrect (chosenVal good v) (hback (chosenVal good v))
  apply stableBounded good v (childBody φ v)
  · rw [childFree, testFree]
    exact Entailment.K_right hfree
  · rw [childChosen, testChosen]
    exact Entailment.K_left hchosen
def stableFromBounded {n : ℕ} (φ : Semisentence language (n+1)) (hφ : Hierarchy 𝚺 0 φ)
    (v : Fin (n+1) → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! ∼∼(∃⁰ (guard v ⋏ childBody φ v)) 🡒 ∃⁰ (guard v ⋏ childBody φ v) := by
  let h := PRABoundedFormula.PRA_proves_boundedBooleanCharacteristic φ hφ
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  exact stableFromClassical c φ hc.2.1 hc.2.2 v hback
end DiophantineConsistency.IPRABoundedChild
