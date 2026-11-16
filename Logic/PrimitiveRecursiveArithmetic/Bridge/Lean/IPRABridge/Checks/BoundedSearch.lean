import IPRABridge.BoundedSearch
import DiophantineConsistency.IPRABoundedLogic

/-! Check the finite parameter interface, the failure case for the original
Foundation search code, and the native client's public judgment. -/

set_option autoImplicit false
noncomputable section

namespace IPRABridge.Checks.BoundedSearch

open LeanProofs.ConciseIPRA (Fm PTm Prf PRAAx)
open scoped LeanProofs.ConciseIPRA.Fm
open LeanProofs.IPRA
open DiophantineConsistency
open PRAFiniteFunctionCodes (Code)

example {n : ℕ} (f : PTm 2) (N x : PTm n) :
    Search.Finite.mu f N ![x] = Search.mu f N x :=
  Search.Finite.mu_single f N x

example {n k : ℕ} {Γ : List (Fm PTm n)} (good : Code (k + 1)) (xs : Fin k → PTm n) :
    Prf PRAAx Γ (translatedSearch good PTm.zero xs ≐ PTm.zero) :=
  translatedSearch_zero good xs

example {n k : ℕ} {Γ : List (Fm PTm n)} (good : Code (k + 1)) (N : PTm n)
    (xs : Fin k → PTm n)
    (noWitness : ∀ i : PTm n, Prf PRAAx Γ
      (lt i N ⟶ neg (translatedApp good (Fin.cases i xs) ≐ PTm.zero))) :
    Prf PRAAx Γ (translatedSearch good N xs ≐ N) :=
  (translatedSearch_eq good N xs).eqTrans
    (Search.Finite.search_failed (translatedSearchBody good) N xs (fun i => by
      simpa only [translatedSearchBody_apply] using noWitness i))

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage (language)
open IPRANativeFormula (native)
open IPRANativeTheory (nativeTheory)
open IPRATheoryHilbertBridge (extended)

example {n : ℕ} (good : Code (n + 1)) (v : Fin (n + 2) → Term language ℕ) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ PRABoundedSelector.matrix good) :=
  IPRABoundedSelector.selectorOpen (good := good) (v := v)

#print axioms Search.Finite.search_found
#print axioms Search.Finite.search_failed
#print axioms translatedSearch_eq
#print axioms translatedSearch_found
#print axioms IPRABoundedSelector.selectorOpen
#print axioms IPRABoundedLogic.stableAnyBoundedExists

end IPRABridge.Checks.BoundedSearch
