import DiophantineConsistency.PRAOpenFormulaCompiler
import DiophantineConsistency.IPRABitConvention
import IPRABridge.ComparisonBits
import IPRABridge.ScopedSequents

set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANotBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic LeanProofs.ConciseIPRA.Fm
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAIsZero PRAOpenFormulaCompiler
open IPRANativeFormula IPRANativeTheory IPRATheoryHilbertBridge IPRABitConvention
open IPRATheoryInstantiation IPRABridge
open LeanProofs.ConciseIPRA (Fm PTm PR Prf PRAAx)
open LeanProofs.IPRA (eqb eqb_of_eq eqb_of_ne succ_ne_zero)

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

private theorem translatedNot {n m : ℕ} {Γ : List (Fm PTm m)}
    (c : Code n) (ts : Fin n → PTm m) :
    Prf PRAAx Γ (translatedApp (notCode c) ts ≐ eqb (translatedApp c ts) PTm.zero) := by
  change Prf PRAAx Γ (PTm.app (.comp (toConciseCode isZeroCode) ![toConciseCode c]) ts ≐ _)
  refine (LeanProofs.ConciseIPRA.PRA.comp (toConciseCode isZeroCode) ![toConciseCode c] ts).eqTrans ?_
  have args : (fun j : Fin 1 => PTm.app (![toConciseCode c] j) ts) = ![translatedApp c ts] := by
    funext j
    fin_cases j
    rfl
  rw [args]
  exact translated_isZeroCode (translatedApp c ts)

private theorem conciseNotBit {n m : ℕ} {Γ : List (Fm PTm m)}
    (c : Code n) (ts : Fin n → PTm m) :
    let t := translatedApp c ts
    let z := PTm.zero (n := m)
    let o := translatedApp oneCode Fin.elim0
    Prf PRAAx Γ (((t ≐ z) ⋎ (t ≐ o)) ⟶ Fm.iff (translatedApp (notCode c) ts ≐ z) (t ≐ o)) := by
  dsimp
  refine .impI (.orE Prf.hyp0 ?_ ?_)
  · apply Prf.iffI
    · exact .impI (.botE _ (succ_ne_zero ((eqb_of_eq Prf.hyp1).eqSymm.eqTrans
        ((translatedNot c ts).eqSymm.eqTrans Prf.hyp0))))
    · exact .impI (.botE _ (succ_ne_zero (translated_oneCode.eqSymm.eqTrans
        (Prf.hyp0.eqSymm.eqTrans Prf.hyp1))))
  · apply Prf.iffI
    · exact .impI Prf.hyp1
    · exact .impI ((translatedNot c ts).eqTrans (eqb_of_ne
        (.impI (succ_ne_zero (translated_oneCode.eqSymm.eqTrans
          (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))))))

private def matrixI {n : ℕ} (c : Code n) : Semisentenceᵢ language n :=
  let t : TermN n := .func c (fun i => .bvar i)
  let s : TermN n := .func (notCode c) (fun i => .bvar i)
  let z : TermN n := .func (.zero 0) Fin.elim0
  let o : TermN n := .func oneCode Fin.elim0
  (.rel .eq ![t, z] ⋎ .rel .eq ![t, o]) 🡒 (.rel .eq ![s, z] 🡘 .rel .eq ![t, o])

private theorem nullaryApp {n : ℕ} (c : PR 0) (args : Fin 0 → PTm n) :
    PTm.app c args = PTm.app c Fin.elim0 := by
  rw [Subsingleton.elim args (Fin.elim0 : Fin 0 → PTm n)]

def notBitConvention {n : ℕ} (c : Code n) (v : Fin n → Term language ℕ) : extended nativeTheory ⊢!
    (eq (.func c v) zero ⋎ eq (.func c v) one) 🡒
      (eq (.func (notCode c) v) zero 🡘 eq (.func c v) one) := by
  let label : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have concise : Prf PRAAx [] (toConciseSemisentence (matrixI c)) := by
    simpa only [toConciseSemisentence, matrixI, IPRAOrderErasure.erase,
      IPRAOrderErasure.termsToReference, Semiterm.lMap_func, Semiterm.lMap_bvar, Function.comp_def,
      Matrix.cons_val_zero,
      Matrix.cons_val_one, toConciseFormula, toConciseTerm, toConciseCode, nullaryApp, Fm.iff,
      translatedApp, PTm.zero] using (conciseNotBit (Γ := []) c PTm.var)
  have standard := (scopedStandardSequent_iff_closure label [] (matrixI c)).mp
    ((scopedStandardSequent_iff label [] (matrixI c)).mpr concise)
  have native := ((IPRAStandardTheory.provable_iff _).mp standard).some
  have applied := instantiateTheory _ native v
  have rewPair (s t : TermN n) :
      (fun i : Fin 2 => Rew.embSubsts v (![s, t] i)) =
        ![Rew.embSubsts v s, Rew.embSubsts v t] := by
    funext i
    fin_cases i <;> rfl
  have rewConstant (d : Code 0) :
      Rew.embSubsts v (.func d Fin.elim0) = .func d Fin.elim0 := by
    simp only [Rew.func, Function.comp_def]
    congr 1
    exact Subsingleton.elim _ _
  have specialized : extended nativeTheory ⊢! ⊤ 🡒
      ((eq (.func c v) zero ⋎ eq (.func c v) one) 🡒
        (eq (.func (notCode c) v) zero 🡘 eq (.func c v) one)) := by
    simpa [matrixI, eq, zero, one, Semiformulaᵢ.rew_rel, Function.comp_def,
      rewPair, rewConstant, Rew.func, Rew.embSubsts_bvar] using applied
  exact specialized ⨀ Entailment.verum
end DiophantineConsistency.IPRANotBit
