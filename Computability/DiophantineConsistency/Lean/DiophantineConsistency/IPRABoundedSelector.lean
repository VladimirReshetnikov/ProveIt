import DiophantineConsistency.PRABoundedSelector
import DiophantineConsistency.IPRANativeOpenDecidable
import DiophantineConsistency.IPRAOpenAtomDecision
import DiophantineConsistency.IPRANativeFormulaRew
import IPRABridge.BoundedSearch
import IPRABridge.ScopedSequents
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedSelector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic LeanProofs.ConciseIPRA.Fm
open PRAFiniteFunctionCodes PRALanguage PRATheory PRABoundedSelector
open IPRANativeTheory IPRANativeFormula IPRANativeOpenDecision IPRANativeEqualityDecidable
open IPRAOpenAtomDecision IPRATheoryHilbertBridge IPRATheoryInstantiation
open IPRABridge
open LeanProofs.ConciseIPRA (Fm PTm PR Prf PRAAx)
open LeanProofs.IPRA (eq_or_ne neg)
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem openAtoms : (φ : Proposition language) → φ.Open → AtomDecisions φ
  | .rel r v, _ => by
    rw [AtomDecisions.eq_1]
    exact ⟨atomDec equalityDecidable r v⟩
  | .nrel r v, _ => by
    rw [AtomDecisions.eq_2]
    exact ⟨atomDec equalityDecidable r v⟩
  | ⊤, _ => by change AtomDecisions .verum; rw [AtomDecisions.eq_3]; trivial
  | ⊥, _ => by change AtomDecisions .falsum; rw [AtomDecisions.eq_4]; trivial
  | φ ⋏ ψ, h => by
    simp only [Semiformula.open_and] at h
    change AtomDecisions (.and φ ψ)
    rw [AtomDecisions.eq_5]
    exact ⟨openAtoms φ h.1, openAtoms ψ h.2⟩
  | φ ⋎ ψ, h => by
    simp only [Semiformula.open_or] at h
    change AtomDecisions (.or φ ψ)
    rw [AtomDecisions.eq_6]
    exact ⟨openAtoms φ h.1, openAtoms ψ h.2⟩
  | ∀⁰ φ, h => by simp at h
  | ∃⁰ φ, h => by simp at h
  termination_by φ _ => φ.complexity

private abbrev comparisonBit {n : ℕ} (a b : PTm n) : Fm PTm n :=
  translatedApp ltBitCode ![a, b] ≐ translatedApp PRALanguage.oneCode Fin.elim0

private theorem conciseSelector {n k : ℕ} {Γ : List (Fm PTm n)} (good : Code (k + 1))
    (i N : PTm n) (xs : Fin k → PTm n) :
    let result := translatedSearch good N xs
    Prf PRAAx Γ ((neg (comparisonBit i N) ⋎ neg (translatedApp good (Fin.cases i xs) ≐ PTm.zero)) ⋎
      (comparisonBit result N ⋏ (translatedApp good (Fin.cases result xs) ≐ PTm.zero))) := by
  dsimp only
  refine .orE (eq_or_ne (translatedApp ltBitCode ![i, N])
    (translatedApp PRALanguage.oneCode Fin.elim0)) ?_ (.orI₁ (.orI₁ Prf.hyp0))
  refine .orE (eq_or_ne (translatedApp good (Fin.cases i xs)) PTm.zero) ?_ (.orI₁ (.orI₂ Prf.hyp0))
  have bound : Prf PRAAx
      ((translatedApp good (Fin.cases i xs) ≐ PTm.zero) :: comparisonBit i N :: Γ)
      (LeanProofs.IPRA.lt i N) := (translated_ltBitCode i N).iffMp Prf.hyp1
  have found := translatedSearch_found (good := good) (xs := xs) Prf.hyp0 bound
  exact .orI₂ (.andI ((translated_ltBitCode _ N).iffMpr (.andE₁ found)) (.andE₂ found))

private theorem mapCases {n : ℕ} {α β : Type} (f : α → β) (a : α) (xs : Fin n → α) :
    (fun i => f (Fin.cases a xs i)) = Fin.cases (f a) (fun i => f (xs i)) :=
  funext (Fin.cases rfl (fun _ => rfl))

private theorem mapPair {α β : Type} (f : α → β) (a b : α) :
    (fun i : Fin 2 => f (![a, b] i)) = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem nullaryApp {n : ℕ} (c : PR 0) (args : Fin 0 → PTm n) :
    PTm.app c args = PTm.app c Fin.elim0 := by
  rw [Subsingleton.elim args (Fin.elim0 : Fin 0 → PTm n)]

private theorem conciseMatrix {n : ℕ} (good : Code (n + 1)) :
    Prf PRAAx [] (toConciseSemisentence (native (matrix good))) := by
  simpa only [matrix, Semiformula.neg, IPRANativeFormula.native, Semiformulaᵢ.neg_def,
    toConciseSemisentence, IPRAOrderErasure.erase, IPRAOrderErasure.termsToReference,
    goodWitnessTerm, goodFoundTerm, foundTerm, argsWitness, argsBound, zeroTerm, applyCode,
    Semiterm.lMap_func, Semiterm.lMap_bvar, Function.comp_def, mapCases, mapPair, Matrix.cons_val_zero,
    Matrix.cons_val_one, toConciseFormula, toConciseTerm, toConciseCode, nullaryApp,
    comparisonBit, translatedSearch, translatedApp, PTm.zero, neg] using
    (conciseSelector (Γ := ([] : List (Fm PTm (n + 2)))) good (PTm.var 0) (PTm.var 1)
      (fun i => PTm.var i.succ.succ))

def selectorOpen {n : ℕ} (good : Code (n+1)) (v : Fin (n+2) → Term language ℕ) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ matrix good) := by
  let label : Fin (n + 2) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let p := native (matrix good)
  have standard := (scopedStandardSequent_iff_closure label [] p).mp
    ((scopedStandardSequent_iff label [] p).mpr (conciseMatrix good))
  have proof := ((IPRAStandardTheory.provable_iff _).mp standard).some
  have applied := instantiateTheory _ proof v
  have specialized : extended nativeTheory ⊢! ⊤ 🡒 native (Rew.embSubsts v ▹ matrix good) := by
    simpa [p, IPRANativeFormulaRew.native_rew] using applied
  exact specialized ⨀ Entailment.verum
end DiophantineConsistency.IPRABoundedSelector
