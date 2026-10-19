# Comparison with submission 074c76bb74

The [243-state submission in commit 074c76bb74](https://github.com/VladimirReshetnikov/ProveIt/commit/074c76bb74)
contains **the same machine as this directory**. Direct byte comparison agrees
for both transition tables, the state renumbering, and both source-site lists.
This is stronger than agreement up to state renaming. The comparison was made
against the files extracted from the committed archive, without executing its
code first.

| Property | Both constructions |
| --- | --- |
| Working states / binary rows | 243 / 486 |
| Canonical start / dispatcher / halt | 0 / 87 / 243 |
| Deleted Routing245 states | 26 and 122 |
| Changed retained rows | 12/0, 12/1, 17/1, 92/1, 104/1, 106/1, 167/1 |
| Source leaves / guarded cases | 6,459 / 8,390 |
| Exact blank prefix | 407,967 transitions |
| Expanded symbolic rules | 2,314,868 |

Both combine the same loop rotation with the same compensated fold. There is
no additional state reduction in this submission to combine with ours. The
canonical table identity is
`a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791`.
The [artifact comparison](evidence/comparison-074c76bb74.json) records all five
file pairs.

The submission adds useful supporting material:

- A standalone local checker imports none of the inherited compiler or
  symbolic runtime. It checks the same seven whole-tape block identities,
  all 480 ordinary boundary rows, invariant preservation, and exhaustive
  guards. Its ordinary proof reaches the same relative halting theorem as
  our existing [Lean simulation](../combined243_simulation.md).
- Explicit clock accounting gives
  `time243 = timeRotation244 + 2*A - 2*D`, where `A` counts the delayed
  right-zero routing blocks and `D` the shortened two-cell erase blocks.
  For matched complete halting runs, the new time is between two thirds
  and twice the old time. These bounds follow from the same local blocks;
  they do not change the machine.
- A finite-algebra appendix proposes evaluating ground terms in finite
  total operation tables, so equality and congruence follow from evaluation.
  It proves a finite-ground satisfiability bound and supplies a reference
  checker. A calibrated ZFC clause generator and binary compiler remain
  absent, so this separate research direction has no demonstrated state saving.

Seven direct checks were freshly run on copies: construction and startup,
local composition, source rotation, frame closure, affine runtime,
finite-algebra controls, and the printed transition table. All passed.
The seven rebuilt machine files exactly match the submission. The local,
frame, and finite-algebra outputs match its recorded JSON; affine output
differs only in elapsed time. The supplied verification driver was inspected;
its delivery-manifest checks were bypassed in accordance with the repository's
intake procedure.

All 8,390 entries of the submitted expanded certificate, and its other
fields except elapsed time, match our previously executed full expanded
replay. That earlier replay remains actual evidence for this exact table;
this comparison does not claim another fresh expanded execution.

Because the machine files are identical, our existing relative Lean theorem
also applies to the submitted table. Neither the new report nor that relative
theorem alone supplies the complete binary-machine consistency endpoint or
the internal PA theorem. The rotated register-program proof and the binary
runtime/bootstrap connection are tracked separately. Compensated244 remains
the smallest machine with the complete external Lean consistency endpoint
at this comparison checkpoint.

The report pins its prior repository inspection to `d91a27b462`; its historical
formal-status descriptions should be read at that revision. Its additional
proof/checker work is credited to this submission, while the two reductions
retain their original attribution. This comparison makes no claim about
personal authorship or priority beyond the recorded provenance.
