import DiophantineConsistency.PRANotBit
import DiophantineConsistency.IPRABitConvention
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANotBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAIsZero PRAOpenFormulaCompiler
open IPRANativeFormula IPRANativeTheory IPRATheoryHilbertBridge IPRABitConvention PRANotBit
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def notBitConvention {n : ℕ} (c : Code n) (v : Fin n → Term language ℕ) : extended nativeTheory ⊢!
    (eq (.func c v) zero ⋎ eq (.func c v) one) 🡒
      (eq (.func (notCode c) v) zero 🡘 eq (.func c v) one) := by
  have hs := transferOpen (matrix c) (matrix_open c) (PRA_proves_sentence c) v
  have hv : (fun i : Fin n => Rew.embSubsts v (vars n i)) = v := by funext i; simp [vars]
  have ha : Rew.embSubsts v (arg c) = .func c v := by simp [arg, applyCode, Rew.func, Function.comp_def, hv]
  have hb : Rew.embSubsts v (notarg c) = .func (notCode c) v := by simp [notarg, applyCode, Rew.func, Function.comp_def, hv]
  have hz : Rew.embSubsts v (z : TermN n) = zero := by
    simp [z, zero, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have ho : Rew.embSubsts v (o : TermN n) = one := by
    simp [o, one, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have hl : extended nativeTheory ⊢! native (Rew.embSubsts v ▹ matrix c) 🡒
      ((eq (.func c v) zero ⋎ eq (.func c v) one) 🡒
        (eq (.func (notCode c) v) zero 🡘 eq (.func c v) one)) := by
    simp [matrix, Semiformula.neg, IPRANativeFormula.native, eq, ha, hb, hz, ho]
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact hl ⨀ hs
end DiophantineConsistency.IPRANotBit
