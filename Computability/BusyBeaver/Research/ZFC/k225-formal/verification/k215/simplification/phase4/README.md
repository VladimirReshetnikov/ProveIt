# Shared implication lemmas and symbolic execution

The exact 215-state machine and both endpoint statements are unchanged. The
[combined Lean check](lean/README.md) validates all 185 project modules:
10 affected modules were freshly compiled and 175 predecessor objects reused
with exact source, dependency, object and log bindings. Both typed endpoint
clients pass, with ten standard axiom reports and zero audit warnings. All
private objects and the immutable phase-three basis were rehashed after the
audits. This is an incremental check, not a fresh compilation of all modules.

The [implication proof](lean-rho8-sharing/README.md) shares identical conclusions
between its bootstrap and condensed-detachment hierarchy, then prunes the unused
ancestors. It retains 58 bootstrap lemmas and 59 templates, down from 61 and 81.
All eight numerical guards, public statements and the deduction-theorem argument
are unchanged. The source decreases from 35,185 to 30,114 bytes (614 to 517 lines).
The maintained producer reproduces it; its alternate modes and invalid-mode
controls also pass. The optional notation experiment was not adopted.

The [register proof](register-prefix/README.md) uses a general lemma for removing
a successful prefix from a halting run. Its segment-halting theorem follows
from the existing segment-execution theorem, replacing the second induction over
segment syntax. All old statements and executable definitions are unchanged.
Including the reusable lemma, the file decreases from 555 to 544 lines.

The [upstream symbolic-execution draft](enum-symbolic/README.md), from
[1d264e552f](https://github.com/VladimirReshetnikov/ProveIt/commit/1d264e552f),
merged at `b6c7087477`, proves enumerator block contracts using shared command
lemmas. It replaces stack-selection scaffolding and decreases `EnumPerm` from
645 to 545 lines. The exact fetched source is retained. An explicit client proves
all-input equality with the former execution function; the general halting
interface and endpoint clients pass.

Together these three proof files decrease from 1,814 to 1,606 lines. The
[legacy compatibility refresh](legacy/README.md) separately checks the four root
interfaces against the current primary objects. Earlier receipts, failed
attempts, attribution and the [phase-three checkpoint](../phase3/README.md) remain
unchanged. This adds no internal PA derivation or minimum-size claim.
