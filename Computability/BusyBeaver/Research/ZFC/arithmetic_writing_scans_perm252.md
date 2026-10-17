# Internal scans that replace the read bit

[`ArithmeticWritingScansPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticWritingScansPerm252.lean)
proves exact self-loop scans on the frozen 252-state arithmetic evaluator when
read and written bits may differ. The right-moving endpoint is

```
runFrom length (frame state left (bitPrefix read length right))
 = frame state (bitPrefix write length left) right
```

under the explicit actual-row premise
`actionLookup state (digit read) = 4*state+3+digit write`.
The left-moving version uses `leftFrame`, places the written prefix on the
right half and uses the corresponding left-row equation. Both include every
write and move through the stated endpoint. Length, state and both complete
tape halves range over every IΣ1 model; Boolean labels are external data.
No first-exit or absolute-head statement is required.

Each single-step lemma consumes a read bit and prepends the write bit on
the opposite whole half. Π1 induction universally quantifies both halves,
so the induction hypothesis permits the changed half after that step.
The existing `bitPrefix_push` identity gives the complete written prefix.
Zero-length scans are included. Fixed Nat-state row adapters use actual
literal lookup data and cover all three self-loops that replace the read
bit: arithmetic state 8 writes 1→0 moving left, state 14 writes 1→0 moving
right and state 42 writes 0→1 moving right. Arithmetic state numbers are one
above canonical working-state indices; 0 is halt.

This supplies the writing-scan substrate needed by the actual symbolic
checker. The lookup premises are explicit properties of the frozen table,
not arbitrary register-operation or box assumptions. The native checker
marks scan progress as false even for long scans; its positive final clock
comes from a literal transition. This module similarly asserts exact length,
including zero, without claiming a full symbolic execution or consistency
endpoint. The contracts follow the attributed `WritingRuns` framework;
Mira-Cult, Jeff and Wade retain their machine and verification attributions.

The [first-attempt verification](results/arithmetic-writing-scans-perm252-verification.json)
passes six ordered axiom reports and twelve callers, with standard Lean
axioms only. Source and audit took 5.774 and 2.258 seconds on pinned Lean
4.32.0. The source has zero warnings. The audit has **four style warnings**:
two `unnecessarySimpa` and two unused row-premise parameters in the
zero-length examples, whose goals simplify independently. These successful
source/audit bytes and logs are retained unchanged.

The checker merges the successful SymbolicTape 10/12 and RegisterReturn
11/12 records into exactly 39 project providers, requiring equal shared
source/object identities. Five external first providers, all direct Lean
imports plus Omega, all 99 input identities and the fresh object are checked
before and after. No dependency was rebuilt or downloaded.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_writing_scans_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --tape-evidence /outside/successful-symbolic-tape/verification.json \
  --return-evidence /outside/successful-register-return/verification.json \
  --output /outside/new-empty-writing-scan-check
```

The maintained portable checker is byte-identical to the executed original.
It freshly checks only this module and its audit after verifying the selected
source/object pool, dependency pins and actual first providers. `--cache`
relocates all selected project objects with their hashes preserved. The
maintained-default preflight is **PREPARED_NOT_BUILT**, with no proof commands;
three argument/provider rejection controls pass without proof compilation.
The [publication record](results/arithmetic-writing-scans-perm252-publication.json)
keeps those scopes and all four audit warnings explicit.

The [independent final review](results/arithmetic-writing-scans-perm252-review.json)
binds the complete proof, audit, unchanged portable checker and preflight.
It checks 671 identities across 105 paths, preserves all four warnings and
performs no reviewer proof replay. The prebuild review remains separate.
