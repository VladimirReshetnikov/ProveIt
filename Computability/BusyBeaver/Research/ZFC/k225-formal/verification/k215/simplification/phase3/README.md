# Shared lemmas and one enumerator theorem

The exact 215-state machine and both endpoint statements are unchanged. The
[current Lean check](lean/README.md) validates the 185-module primary closure:
9 affected modules are freshly compiled and 176 reused
objects remain hash-bound to the previous checkpoint. Both typed endpoint clients
pass; all ten axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`,
with zero audit warnings. Every private object, compiler log and toolchain pin is
rechecked after the audits. This is an incremental check, not a fresh full replay.
The feature packets preserve their isolated checks before adoption; the combined
check records the adopted sources.

The [dominated-implication proof](lean-rho8-guarded/README.md) now derives its
basis from 61 small bootstrap lemmas and reuses 81 conditional schemas. Eight of
those schemas carry one explicit numerical inequality, discharged at each use.
After composition and distribution are derived, a small deduction theorem gives
the same unrestricted rho8 theorem for arbitrary natural codes. This removes
repeated substitution instances and the valuation-term data graph: the Lean file
shrinks from 128,177 to 35,185 bytes. Its proof and producer have independent
reviews; the proof introduces no formula-decoding or consistency premise.

The [upstream general enumerator theorem](upstream-l1/README.md), from
`021d848979`, handles every valid state between candidates. The zero start and
the boot start no longer need separate completeness arguments. Its decoder uses
the same command-step function as the block contracts. The integrated proof keeps
our shared contract helpers, and a typed audit proves that the new execution
function equals the former four-branch definition for all inputs. Two
[subsequent upstream refactors](upstream-l1/selector-successor/README.md) put the
AX atom effects directly in the word interpreter and share three selector-level
lemmas across DROP, MP and AX. The four affected source files shrink from 1,198
to 1,030 lines, including our retained contract helpers. The newer upstream files
are included in the combined kernel check above.

The [site-coverage facade](site-coverage/README.md) directly composes the same
105 checked blocks, replacing 104 intermediate joins and their repeated paths.
It shrinks from 107,243 to 14,916 bytes; all nine batch files and all 4,751 leaf
checks remain unchanged. The maintained generator reproduces the checked source,
and preparation preserves both maintained source/site generators.

The [legacy compatibility check](legacy/README.md) separately refreshes the
four root interfaces and their fourteen additional dependencies against
the current primary objects. Its private union cache is separate from the
185-module primary check. Earlier full-build and simplification receipts remain
unchanged. A final trailing-newline cleanup of `RMDag` was freshly compiled and
produced the same object as the preceding checkpoint.

The [second checkpoint](../phase2/README.md) records source-certificate symmetry,
the smaller register determinism argument, and the 629-node Lean/Rocq certificate.
Rocq retains that checked 735-instruction rendering and its closed endpoint
reports; the guarded hierarchy is the subsequent Lean simplification. No
internal PA proof or minimum-size claim is added.
