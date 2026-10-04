# Square/product 82: height and fixed-outer auxiliary minimum

New quantitative packet, 2026-10-04. Author-complete and bounded-check PASS;
independent mathematical audit pending. It does not change or supersede
Report45's full positive counterfamily theorem.

## Core files

- HEIGHT.md: exact numerical height, all 18 bit-length bounds, exact cubics,
  explicit minimal-r dependence, and radix-jump caveat
- AUX_MINIMUM.md: complete Pell classification and least index R for fixed
  outer coordinates; extension to every positive i in the same outer tuple
- BASE_COUNTERFAMILY.md: fresh recovered proof, explicitly not byte-identical
  to the lost historical proof
- source/: eight authenticated upstream snapshots, always treated as data
- height_check.py: independent fail-closed checker, no upstream execution
- auxiliary_minimum_check.py: independent minimum-index checker
- check_tamper.py: seven deliberate mutations, each rejected in normal and -O
- *_CHECKS.json and *_CHECKS_O.json: byte-identical normal/optimized receipts

Run only the three newly authored checkers above. The Python file under
source/ is a pinned data snapshot and must not be executed. No checker
imports it, evaluates the saved arithmetic schedule, or builds a complete
counterfamily tuple. Inner component tests and outer packing tests remain
separate. Synthetic masks are not labeled genuine compiled programs.

The exact-height proof, not the finite checks, supplies the general result.
Main scope: a particular explicit witness family, not a lower bound for
all witnesses of this 82-operation polynomial. Auxiliary minimum: fixed
outer tuple only. No smooth leading asymptotic in x is asserted across
power-of-five radix jumps.

Any analytic series/inversion research is a separate follow-on and is not
part of these core claims until explicitly completed and audited.
