# AX9 source research and a semantic zero-credit bridge

This directory contains a source-level AX emitter simplification, a complete written compiler argument, and a standalone kernel-checked semantic resource theorem. It contains **no accepted 214-state binary machine**.

- `AX9_THEORY.md`: full equations, all-natural macro argument, repaired strong compiler, proof boundaries, and alternative comparison.
- `AX9Factor.v`: 301 lines of Coq 8.18, twelve closed assumption reports, recursively checked with `coqchk`. Its pairing, generated-row, gate, generalization and MP hypotheses are explicit theorem parameters. No `Admitted`, local `Axiom`, or oracle is used. A finite ghost-zero-spine corollary removes all scheduler-credit hypotheses for clean-zero-stack soundness; it is an abstract command-level theorem, not an exact-machine endpoint.
- `verify_ax9_source.py`: exact 19-leaf source edit, source/CFG reconstruction and finite arithmetic corroboration.
- `source-evidence/`: two source variants and the precise check receipt.
- `reference/`: pinned input source and inherited notices/licenses.

Run the portable source check with Python 3 (standard library only):

    python3 verify_ax9_source.py

Regenerate both derived sources and a receipt in a fresh directory:

    python3 verify_ax9_source.py --out /tmp/ax9-fresh-evidence

Compile and recursively check the formal theorems with Coq 8.18:

    coqc AX9Factor.v
    coqchk -silent AX9Factor

The recorded run used Coq 8.18.0 / OCaml 4.14.1. `coqc.log` records the twelve closed assumption reports, and the silent `coqchk.log` is empty because the recursive check exited successfully. `verification.json` records exit status and source hash. Binary proof objects are intentionally omitted: regenerate them with the commands above.

**Candidate recommendation.** M124/M160 have the simplest marker invariants among the examined 215-state alternatives; M124 needs four changed rows and two unconditional entry facts. CM215 has a conditional marker exception, but its existing exact-Core/dense adapter work is more advanced. These are different reasons to prefer a candidate. Their standalone proofs are existing repository work, not new contributions here, and the alternatives index does not establish that every adapter has been integrated into the accepted endpoint closure. ZC215 is the cleaner source target for arbitrary-tail resource reasoning, yet still needs its full exact-machine adapter.

New proof and verifier code follow ProveIt's MIT No Attribution terms. The original K215 source and inherited terms are preserved under `reference/`. The artifact was prepared by this research collaboration for Vladimir Reshetnikov; it makes no global priority claim.
