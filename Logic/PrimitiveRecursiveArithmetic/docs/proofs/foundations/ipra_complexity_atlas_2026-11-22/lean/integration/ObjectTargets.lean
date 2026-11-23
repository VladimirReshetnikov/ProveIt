/-
UNCOMPILED integration outline for the inspected ProveIt revision.
This file is intentionally outside the standalone Std-only library root.
Open it in ProveIt's own Lean 4.32.0 workspace after adding the source path.
It defines proof TARGETS; it does not assert that those targets are inhabited.
Symbols must first be implemented by actual finite PR syntax as specified in
the report and CoreOutline.lean. No target is postulated as an axiom.
-/
import ConciseIPRA.PR
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Foundations.DiagonalClock

namespace IPRAComplexity.ObjectTargets

open LeanProofs.ConciseIPRA
open scoped Fm

/-- Fixed function syntax, not a numerical universal PR evaluator. -/
structure Symbols where
  length : PR 1
  accept : PR 3          -- e, input word, transition clock
  selfWord : PR 3        -- e, c, k
  polynomialClock : PR 3 -- c, k, input length
  diagonal : PR 1

def nonzero {n : Nat} (t : PTm n) : Fm PTm n :=
  (t ≐ PTm.zero) ⟶ Fm.bot

def unequal {n : Nat} (s t : PTm n) : Fm PTm n :=
  (s ≐ t) ⟶ Fm.bot

def mismatchBody (s : Symbols) : Fm PTm 3 :=
  let e : PTm 3 := .var 0
  let c : PTm 3 := .var 1
  let k : PTm 3 := .var 2
  let w : PTm 3 := .app s.selfWord ![e,c,k]
  let n : PTm 3 := .app s.length ![w]
  let t : PTm 3 := .app s.polynomialClock ![c,k,n]
  (nonzero e ⋏ nonzero c) ⟶
    unequal (.app s.diagonal ![w]) (.app s.accept ![e,w,t])

def mismatchSentence (s : Symbols) : Fm PTm 0 :=
  .all (.all (.all (mismatchBody s)))

/-- The actual H01 object-proof goal, after constructing the specified symbols. -/
def DiagonalProofTarget (s : Symbols) : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] mismatchSentence s

/- Other exact endpoint families, to encode by the same bounded syntax.

F05 trace uniqueness:
  ∀ e x T z, ValidTrace(e,x,T,z)=1 ->
    ∀ i≤T, Entry(z,i)=Run(e,x,i).
  Trace quantification is bounded when this assertion is used in induction.

N03/N04/N18:
  ∀ v x w<2^p, CNFOK(Compile(v,x),Extend(v,x,w))=V(v,x,w);
  ∀ a<2^variables, CNFOK(...,a)=1 ->
    Extend(v,x,Restrict(v,x,a))=a;
  counts are equal by the explicit inverse pair of finite witness maps.

S05:
  ∀ N G s t K, Valid(G,N) and s,t<N ->
    Midpoint(G,K,s,t)=1 iff
    ∃ pathCode<max(2,N)^(2^K+1), PathOK(...)=1.
  Separately derive the concrete depth-first machine's space bound.

S08:
  ∀ graph source target, nonReachBranchOR(...)=1-Reach(...).
  Both ORs are bounded finite numerical functions; include fuel and code
  bounds before induction and give the actual online nondeterministic machine.

S11/S12:
  ∀ graph-description endpoints K,
    QBFTruth(PrintSelector(...))=Midpoint(...),
  together with explicit syntax, variable-freshness and printer-cost bounds.

R03/R07/R08:
  amplify: 2^d*BadCount(x,d)<2^(12*d*r) under 3*bad≤2^r;
  advice: ∀ n ∃ a<2^AdviceBits(n) ∀ x in the length-n word interval,
    AmplifiedOutput(x,a)=LanguageBit(x);
  translate-covering: express the finite ∃list∀seed / ∀list∃seed formula
    and prove equality to the positively identified BPP language bit.

Q03:
  encoded PP branch accepting count minus its rejecting count = 2*A-2^h.
  Represent signed differences by natural cross-addition if convenient.

Completion must provide the exact PR terms, BFm syntax, and derivation terms.
Do not replace any of these goals with a structure containing the desired
conclusion as a supplied field and then call that a completed formalization.
-/

end IPRAComplexity.ObjectTargets
