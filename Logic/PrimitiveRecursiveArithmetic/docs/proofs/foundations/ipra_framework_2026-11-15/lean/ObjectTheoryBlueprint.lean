import ConciseIPRA.PR
/-!
Object-theory-facing blueprint (not claimed compiled here).
Core repository API: LeanProofs.ConciseIPRA.PR, PTm, PRAAx,
PRA.qfInd, PRA.precZero, PRA.precSucc and Prf.
The declarations below name interfaces but do NOT postulate missing axioms.
-/
namespace IPRAFramework.ObjectTarget
open LeanProofs.ConciseIPRA

-- Candidate code for a Boolean bounded-or fold is to be assembled using
-- PR.prec, PR.comp, and projections. A complete development must provide:
-- (1) PR code for Boolean/arithmetical building blocks;
-- (2) PTm term for the code and QF formula for its loop invariant;
-- (3) Prf derivation via PRA.qfInd;
-- (4) semantic correspondence to FiniteCore.testUpTo.

-- Bare statements about Nat here are insufficient for an iPRA theorem.
end IPRAFramework.ObjectTarget
