/-!
Object-language blueprint for ProveIt.

Expected repository placement:
  Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/
    IPRADerivations/Combinatorics/Catalan/Core.lean

The imported theorem `BinomialIdentities.catalan` is already kernel checked in
ProveIt snapshot 00bbe871268c453903499fb6afe07519e87d9631.  This file records
reusable terms and target signatures only.  It deliberately declares no
unproved theorem, uses no `sorry`, and adds no axiom.

This delivery environment did not contain Lean, so the new file is not claimed
to have been compiled.
-/
import IPRADerivations.Combinatorics.BinomialIdentities

namespace LeanProofs.IPRA.Combinatorics.Catalan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

/-- `C_n = binom (2n) n monus binom (2n) (n+1)`. -/
abbrev cat {m : Nat} (n : PTm m) : PTm m :=
  monus (binom (n + n) n) (binom (n + n) (succ n))

/-- Left and right terms of the denominator-cleared ratio recurrence. -/
abbrev ratioLhs {m : Nat} (n : PTm m) : PTm m :=
  succ (succ n) * cat (succ n)

abbrev ratioRhs {m : Nat} (n : PTm m) : PTm m :=
  num 2 * succ (n + n) * cat n

/-- Body `C_k C_(n-k)` with variables `0=k`, `1=n`. -/
abbrev segnerBody : PTm 2 :=
  cat (var 0) * cat (monus (var 1) (var 0))

/-- Exact checked base theorem in the imported repository module. -/
#check LeanProofs.IPRA.Combinatorics.BinomialIdentities.catalan
#check LeanProofs.IPRA.Combinatorics.BinomialIdentities.catalan_ratio
#check LeanProofs.IPRA.Combinatorics.BinomialIdentities.binom_sum
#check LeanProofs.IPRA.Combinatorics.BinomialIdentities.central_binomial

/-
Next object-language targets (the report gives the proof algorithms):

1. ratioFormula:
     forall n, ratioLhs n = ratioRhs n.

2. segnerFormula:
     forall n, cat (n+1) = sum_{k<n+1} cat k * cat (n monus k).

3. reflectionFormula:
     count Dyck(2n) = binom (2n) n monus binom (2n) (n+1).

4. valuationFormula:
     forall prime p, vp p (cat n)
       = carries p n n monus vp p (n+1).

5. hankel0Formula / hankel1Formula / hankel2Formula:
     det [cat (i+j)] = 1,
     det [cat (i+j+1)] = 1,
     det [cat (i+j+2)] = n+1.

Each target must conclude in `Prf PRAAx`; an ambient `Nat` theorem is not a
substitute.  See paper/09_formalization.tex for the dependency graph.
-/

end LeanProofs.IPRA.Combinatorics.Catalan
