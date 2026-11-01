import DiophantineConsistency.IPRASelectorOpenCharacteristic
import DiophantineConsistency.IPRABoundedSelector
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASelectorSearchBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRANativeFormula IPRANativeTheory IPRANativeOpenDecidable IPRANativeFormulaRew
open IPRASelectorOpenCharacteristic IPRABoundedSelector PRABoundedSelector
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABoundedSearchCode IPRATheoryHilbertBridge
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def test {n : ℕ} (good : Code (n+1)) : Semisentence language (n+2) :=
  (.rel .lt ![#0,#1]) ⋏ (.rel .eq ![goodWitnessTerm good,zeroTerm])
def boundTest {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) : Semiproposition language 1 :=
  Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (v i))) ▹ test good
def output {n : ℕ} (good : Code (n+1)) : Semisentence language (n+2) :=
  (.rel .lt ![foundTerm good,#1]) ⋏ (.rel .eq ![goodFoundTerm good,zeroTerm])

def selected {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) : Term language ℕ :=
  .func (searchCode good) v

def selectorAt {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) :
   extended nativeTheory ⊢! Rewriting.free (native (boundTest good v)) 🡒
       Rewriting.shift ((native (boundTest good v))/[selected good v]) := by
  let w : Fin (n+2) → Term language ℕ := Fin.cases (&0) (fun i => Rew.shift (v i))
  have hlogic : extended nativeTheory ⊢!
    native (Rew.embSubsts w ▹ matrix good) 🡒
      (native (Rew.embSubsts w ▹ test good) 🡒 native (Rew.embSubsts w ▹ output good)) := by
    simp [matrix, test, output, IPRANativeFormula.native, Semiformula.neg]
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  have hs := hlogic ⨀ selectorOpen good w
  have hrew : (Rew.free (L := language) (n := 0)).comp (Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (v i)))) = Rew.embSubsts w := by
    ext i
    · cases i using Fin.cases with
      | zero =>
        change Rew.free (#0 : Semiterm language ℕ 1) = &0
        rfl
      | succ i =>
        change (Rew.free.comp Rew.bShift) (v i) = Rew.shift (v i)
        rw [Rew.bShift_free_eq_shift]
    · exact Empty.elim i
  have hin : Rewriting.free (native (boundTest good v)) = native (Rew.embSubsts w ▹ test good) := by
    simp only [boundTest, ← native_rew, Rewriting.free, ← TransitiveRewriting.comp_app, hrew]
  have hsubst : (Rew.subst ![selected good v]).comp (Rew.bShift : Rew language ℕ 0 ℕ 1) = Rew.id := by
    ext i
    · exact Fin.elim0 i
    · change (Rew.subst ![selected good v]) (&i) = &i
      exact Rew.subst_fvar _ _
  have hv : ∀ i : Fin (n+1), (Rew.subst ![selected good v]) (Rew.bShift (v i)) = v i := by
    intro i
    change ((Rew.subst ![selected good v]).comp Rew.bShift) (v i) = v i
    rw [hsubst]
    rfl
  have hout : Rewriting.shift ((native (boundTest good v))/[selected good v]) = native (Rew.embSubsts w ▹ output good) := by
    simp [w, boundTest, test, output, selected, goodWitnessTerm, goodFoundTerm, foundTerm, zeroTerm, applyCode,
      IPRANativeFormula.native, Semiformulaᵢ.rew_rel, Rew.embSubsts, Rewriting.shift, Function.comp_def]
    constructor <;> funext i <;> cases i using Fin.cases <;>
      simp [Rew.bind_bvar, Rew.subst_bvar, argsWitness, argsBound, Rew.func, Function.comp_def]
    all_goals try (funext j; cases j using Fin.cases <;> simp [Rew.bind_bvar, Rew.subst_bvar, Rew.func, Function.comp_def])
    all_goals try (change Rew.shift ((Rew.subst ![selected good v]) (Rew.bShift (v 0))) = Rew.shift (v 0); rw [hv])
    all_goals try (funext j; exact Fin.elim0 j)
    all_goals try rfl
    all_goals try (funext j; cases j using Fin.cases <;> rfl)
  simpa only [hin, hout] using hs
theorem boundTest_open {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ) :
    (boundTest good v).Open := by
  simp [boundTest, test, Semiformula.Open]

def stableWithCharacteristic {n : ℕ} (good : Code (n+1)) (v : Fin (n+1) → Term language ℕ)
    (φ : Semipropositionᵢ language 1)
    (hf : extended nativeTheory ⊢! Rewriting.free φ 🡒 Rewriting.free (native (boundTest good v)))
    (hb : extended nativeTheory ⊢! (native (boundTest good v))/[selected good v] 🡒 φ/[selected good v]) :
    extended nativeTheory ⊢! ∼∼(∃⁰ φ) 🡒 ∃⁰ φ :=
  openCharacteristic (boundTest good v) (boundTest_open good v) (selected good v) hf (selectorAt good v) hb
end DiophantineConsistency.IPRASelectorSearchBinding
