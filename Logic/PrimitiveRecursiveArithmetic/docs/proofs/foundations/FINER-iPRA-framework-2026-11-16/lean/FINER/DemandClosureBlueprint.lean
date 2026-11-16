import FINER.TraceBlueprint
import IPRADerivations.Core.MultiSums

/-!
# Finite monotone demand closure: source-oriented blueprint

For capacities `C_i`, iterate `d(t+1) = max(d(t), F(d(t)))` from zero.
A strict step raises the coordinate sum, whose upper bound is `sum C_i`.
Hence the state at that horizon is the least prefixed point.

The final implementation should generate the displayed formulas from the fixed
system data.  This file records the intended object-language endpoints and is
not claimed compiled.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Metalevel package for one theorem-specialised finite demand system.
`stabilitySentence` and `leastnessSentence` are explicit closed object formulas
generated from the fixed capacity vector and transformer. -/
structure DemandSystem where
  arity : ℕ
  capacities : Fin arity → ℕ
  packedStep : PR 1
  coordinate : Fin arity → PR 1
  boundedSentence : Fm PTm 0
  monotoneSentence : Fm PTm 0
  stabilitySentence : Fm PTm 0
  leastnessSentence : Fm PTm 0
  boundedProof : ([] : List (Fm PTm 0)) ⊢[PRAAx] boundedSentence
  monotoneProof : ([] : List (Fm PTm 0)) ⊢[PRAAx] monotoneSentence

/-- After `sum capacities` iterations, the packed state is a prefixed point. -/
theorem demand_stabilises (D : DemandSystem) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] D.stabilitySentence := by
  -- 1. define the packed trace by `rec1`;
  -- 2. prove coordinate bounds and inflation by `ind`;
  -- 3. prove a strict step raises the finite coordinate sum;
  -- 4. exclude `sum capacities + 1` strict steps;
  -- 5. unfold the final join equation.
  sorry

/-- Every prefixed point bounds every iterate, hence bounds the stabilised
closure. -/
theorem demand_least_prefixed (D : DemandSystem) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] D.leastnessSentence := by
  -- Quantifier-free induction on the trace, using `D.monotoneProof`.
  sorry

end LeanProofs.IPRA.FINER
