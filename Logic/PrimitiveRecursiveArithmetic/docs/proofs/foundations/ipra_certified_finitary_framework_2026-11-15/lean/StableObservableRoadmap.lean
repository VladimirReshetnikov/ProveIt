import ConciseIPRA.PR

/-!
# Stable-observable proof glue and roadmap

The small cut combinators below are complete object-theory proofs. The bounded
least-certificate search and rational metric formulas remain integration
work and are stated as explicit targets.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.Finitary

open Syn
open scoped Fm

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- Combine two independently proved certificates with a stability implication. -/
theorem stableOfIndependent
    (C₁ C₂ O : Fm PTm n)
    (h₁ : Γ ⊢[PRAAx] C₁)
    (h₂ : Γ ⊢[PRAAx] C₂)
    (hs : Γ ⊢[PRAAx] (C₁ ⟶ C₂ ⟶ O)) :
    Γ ⊢[PRAAx] O :=
  Prf.impE (Prf.impE hs h₁) h₂

/-- Same rule when stability is proved under local certificate hypotheses. -/
theorem stableOfLocalProof
    (C₁ C₂ O : Fm PTm n)
    (h₁ : Γ ⊢[PRAAx] C₁)
    (h₂ : Γ ⊢[PRAAx] C₂)
    (hs : C₁ :: C₂ :: Γ ⊢[PRAAx] O) :
    Γ ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI hs)) h₂) h₁

/-- Symbols for finite certificate clouds and observations. -/
structure PRStablePresentation where
  bound : PR 2        -- (precision, parameter)
  cert  : PR 3        -- (candidate, precision, parameter)
  obs   : PR 3        -- (candidate, precision, parameter)
  dist  : PR 2        -- coded rational distance
  err   : PR 3        -- (precision1, precision2, parameter)

/-- Nonempty cloud formula, to be built from `Any` and bounded search. -/
def StableNonemptyFm (S : PRStablePresentation) : Fm PTm 0 := by
  sorry

/-- Pairwise cross-precision stability formula. -/
def StablePairwiseFm (S : PRStablePresentation) : Fm PTm 0 := by
  sorry

/-- Conclusion for least valid certificates at the two precisions. -/
def StableSelectorFm (S : PRStablePresentation) : Fm PTm 0 := by
  sorry

structure StableProofs (S : PRStablePresentation) where
  nonempty : ([] : List (Fm PTm 0)) ⊢[PRAAx] StableNonemptyFm S
  pairwise : ([] : List (Fm PTm 0)) ⊢[PRAAx] StablePairwiseFm S

/--
Completion path:
1. instantiate nonemptiness at each precision;
2. apply least-search correctness to obtain two certificate derivations;
3. instantiate `pairwise` at those candidates;
4. close with `stableOfIndependent`;
5. add a separate error-modulus corollary for a regular name.
-/
def stableObservableChoiceErasure
    (S : PRStablePresentation) (h : StableProofs S) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] StableSelectorFm S := by
  sorry

/-- Symbols used by the more general shrinking-viability theorem. -/
structure PRShrinkingPresentation where
  relation : PRLayeredRelation
  obs      : PR 3
  dist     : PR 2
  eps      : PR 2
  delta    : PR 2
  horizon  : PR 2

/-- Final finite shrinking inequality. -/
def ShrinkingBoundFm (S : PRShrinkingPresentation) : Fm PTm 0 := by
  sorry

/--
Dependencies: full-viable least search, least path extraction, path truncation,
finite telescoping of edge bounds, and one metric triangle inequality.
-/
def shrinkingViability (S : PRShrinkingPresentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ShrinkingBoundFm S := by
  sorry

end LeanProofs.ConciseIPRA.Finitary
