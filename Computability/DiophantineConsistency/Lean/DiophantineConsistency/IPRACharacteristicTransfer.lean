import DiophantineConsistency.PRACharacteristicBit
import DiophantineConsistency.IPRANotBit
import DiophantineConsistency.PRABoundedCharacteristic
import DiophantineConsistency.IPRABitConvention
import DiophantineConsistency.IPRAIffGG
import DiophantineConsistency.IPRANativeForward
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRACharacteristicTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler PRABoundedCharacteristic
open IPRANativeFormula IPRANativeTheory IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeForward
open IPRAOpenAtomDecision IPRABoundedSelector IPRAIffGG IPRABitConvention IPRANotBit PRACharacteristicBit PRAOpenFormulaCompiler IPRANativeOpenDecidable
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def oneAtom {n : ℕ} (c : Code n) : Semisentence language n :=
  .rel .eq ![applyCode c (vars n), applyCode oneCode Fin.elim0]

def transferCorrectness {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hcorrect : PRA ⊢ oneCorrectSentence c φ) (v : Fin n → Term language ℕ)
    (hback : extended nativeTheory ⊢! (Rew.embSubsts v ▹ φ)ᴺ 🡒 native (Rew.embSubsts v ▹ φ)) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ oneAtom c) 🡘 native (Rew.embSubsts v ▹ φ) := by
  let a : Proposition language := Rew.embSubsts v ▹ oneAtom c
  let b : Proposition language := Rew.embSubsts v ▹ φ
  have ht := IPRAFullGGTransfer.from_classical hcorrect
  have hgg : nativeTheory ⊢! ∀⁰* ((oneAtom c 🡘 φ)ᴺ) := by
    have h := Classical.choice ht
    simpa only [oneCorrectSentence, oneAtom, IPRAQuantifierFree.gg_allClosure] using h
  have hi := instantiateTheory (T := nativeTheory) ((oneAtom c 🡘 φ)ᴺ) hgg v
  have he : extended nativeTheory ⊢! (a 🡘 b)ᴺ := by
    simpa only [a, b, Semiformula.rew_doubleNegation, LogicalConnective.HomClass.map_iff] using hi
  have hiff : extended nativeTheory ⊢! aᴺ 🡘 bᴺ :=
    Entailment.K_right (Classical.choice (iff_doubleNegation (Λ := extended nativeTheory) a b)) ⨀ he
  have ha : extended nativeTheory ⊢! aᴺ 🡒 native a := by
    have hopen : a.Open := by simp [a, oneAtom, Semiformula.Open]
    exact backward a (openAtoms a hopen)
  have hb : extended nativeTheory ⊢! bᴺ 🡒 native b := hback
  exact Entailment.E_intro
    (Entailment.C_trans (nativeForward a) (Entailment.C_trans (Entailment.K_left hiff) hb))
    (Entailment.C_trans (nativeForward b) (Entailment.C_trans (Entailment.K_right hiff) ha))
def bitMatrix {n : ℕ} (c : Code n) : Semisentence language n :=
  (.rel .eq ![applyCode c (vars n), applyCode (.zero 0) Fin.elim0]) ⋎
    (.rel .eq ![applyCode c (vars n), applyCode oneCode Fin.elim0])

def transferBit {n : ℕ} (c : Code n) (hbit : PRA ⊢ bitSentence c)
    (v : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! eq (.func c v) zero ⋎ eq (.func c v) one := by
  have hs := transferOpen (bitMatrix c) (by simp [bitMatrix, Semiformula.Open])
    (by simpa only [bitSentence, bitMatrix] using hbit) v
  have hv : (fun i : Fin n => Rew.embSubsts v (vars n i)) = v := by funext i; simp [vars]
  have ha : Rew.embSubsts v (applyCode c (vars n)) = .func c v := by simp [applyCode, Rew.func, Function.comp_def, hv]
  have hz : Rew.embSubsts v (applyCode (.zero 0) (Fin.elim0 : Fin 0 → TermN n)) = zero := by
    simp [zero, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have ho : Rew.embSubsts v (applyCode oneCode (Fin.elim0 : Fin 0 → TermN n)) = one := by
    simp [one, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  simpa [bitMatrix, IPRANativeFormula.native, eq, ha, hz, ho] using hs

def transferZeroCorrectness {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ)
    (v : Fin n → Term language ℕ)
    (hback : extended nativeTheory ⊢! (Rew.embSubsts v ▹ φ)ᴺ 🡒 native (Rew.embSubsts v ▹ φ)) :
    extended nativeTheory ⊢! eq (.func (notCode c) v) zero 🡘 native (Rew.embSubsts v ▹ φ) := by
  have hc := transferCorrectness c φ hcorrect v hback
  have hv : (fun i : Fin n => Rew.embSubsts v (vars n i)) = v := by funext i; simp [vars]
  have ha : Rew.embSubsts v (applyCode c (vars n)) = .func c v := by simp [applyCode, Rew.func, Function.comp_def, hv]
  have ho : Rew.embSubsts v (applyCode oneCode (Fin.elim0 : Fin 0 → TermN n)) = one := by
    simp [one, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have hnorm : native (Rew.embSubsts v ▹ oneAtom c) = eq (.func c v) one := by
    simp [oneAtom, IPRANativeFormula.native, eq, ha, ho]
  rw [hnorm] at hc
  exact Entailment.E_trans (notBitConvention c v ⨀ transferBit c hbit v) hc
def decideFromCharacteristic {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hcorrect : PRA ⊢ oneCorrectSentence c φ) (v : Fin n → Term language ℕ)
    (hback : extended nativeTheory ⊢! (Rew.embSubsts v ▹ φ)ᴺ 🡒 native (Rew.embSubsts v ▹ φ)) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ φ) ⋎ ∼native (Rew.embSubsts v ▹ φ) := by
  let a : Proposition language := Rew.embSubsts v ▹ oneAtom c
  let b : Proposition language := Rew.embSubsts v ▹ φ
  have hc : extended nativeTheory ⊢! native a 🡘 native b := transferCorrectness c φ hcorrect v hback
  have hopen : a.Open := by simp [a, oneAtom, Semiformula.Open]
  have hd := openDecidable a hopen
  have hl : extended nativeTheory ⊢! (native a 🡘 native b) 🡒
      (native a ⋎ ∼native a) 🡒 (native b ⋎ ∼native b) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact hl ⨀ hc ⨀ hd
end DiophantineConsistency.IPRACharacteristicTransfer
