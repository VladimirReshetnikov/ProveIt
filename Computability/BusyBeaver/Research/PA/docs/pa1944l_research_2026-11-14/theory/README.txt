Research supplement: arithmetic checks and equality-interface obstruction
=======================================================================

Files
-----
bounded_compiler_and_radix3.tex
  Full written proofs of:
  (1) an explicit bounded-store replacement for the imported PA196
      numerical-proof-to-command-word compiler's full-PA induction;
  (2) an iPRA-provably consistent Boolean countermodel to the proposed
      equality-free radix-three deletion, and to deleting just the equality
      witness head at radix four;
  (3) the relative iPRA halting transfer for complete positive symbolic
      source-to-physical contracts, with exact arithmetic soundness rules.
      Both exact-table independent verifications passed, so the supplement
      includes the ordinary computer-assisted theorem
      iPRA proves Halt(PA1944L) iff Halt(primary PA194), and their negations.
  The abstract and theorem boundaries explicitly do not claim a complete
  PA-refutation calibration or a newly compiled Lean theorem.

check_boolean_obstruction.py
  Pure standard-library executable checks of both exact coded valuations.
  Run: python3 check_boolean_obstruction.py
  It writes boolean_obstruction_receipt.json beside the script.
  The unbounded theorem is the mathematical induction proof in the TeX;
  the finite tests are supporting executable checks, not a proof substitute.

summarize_durations.py
  Checks the exact thirteen-slot duration coefficients from the new machine's
  4,780 independent contracts. Run with the contracts.json path as its single
  argument; it prints the reproducible physical_duration_bounds.json data.
  In each branch, 3 <= duration <=
  534 + 8*gap + 4*sum(primary values) + 2*first spare + 2*spare-tail width.

Repository scope
----------------
VladimirReshetnikov/ProveIt, main snapshot
1c9524d8bf2e0a27b9a16ff622359927f536e663.

Key source references under Computability/BusyBeaver/Research/PA:
  README.md
  pa194-forward-audit/README.md
  isigma1-transfer/README.md
  jamesyc-upstream/pa196/PA196/Arithmetic/Realizes.lean
  jamesyc-upstream/pa196/PA196/Arithmetic/CompilerRecursive.lean
  jamesyc-upstream/pa196/PA196/Arithmetic/CompilerInvariant.lean
  jamesyc-upstream/pa196/PA196/Arithmetic/CompilerRule.lean
  jamesyc-upstream/pa196/PA196/Arithmetic/WordMacros.lean
  jamesyc-upstream/pa196/PA196/Commands/Words.lean
  jamesyc-upstream/pa196/PA196/Commands/Selectors.lean
  jamesyc-upstream/pa196/PA196/Logic/Basic.lean

Proof status
------------
The finite data for a physical relative theorem must be the exact successful
independent verification receipts for that literal machine, including all
source branches, complete startup, and source-instruction equality.
The present result does not supply the still-open uniform PA-axiom compiler.
Consequently it does not assert iPRA proves nonhalting iff Con(PA) for any
new machine, nor that a sub-194 machine has been found.
