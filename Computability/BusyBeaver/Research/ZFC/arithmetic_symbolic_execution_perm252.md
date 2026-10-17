# Arithmetic soundness of the actual symbolic checker

[`ArithmeticSymbolicExecutionPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicExecutionPerm252.lean) proves the arithmetic meaning of the
existing `SymbolicPerm252.sstep`, `exec`, `verifies` and `verifiesHalt` functions.
It uses the actual frozen252 transition table, finite symbolic syntax,
normalization, branch tests and progress flags. There is no new acceptance
language or supplied box-execution premise.

For nine arbitrary internal primary values, an internal spare count and gap,
the interpretation is the checked SymbolicTape configuration value with the
concrete box prefixes. A successful symbolic step gives an internal time
whose actual `runFrom` reaches that entire numeric configuration. When the
step marks literal progress, the time is positive. The same original values
and count interpret source and target effects; positive decrement's appended
spare is already included in the decrement box prefix.

Typed native transitions are connected to arithmetic rows by the existing
`literal_lookup_actual` theorem and all-model numeral adapters. Literal
left/right steps retain every write and move, including the real halt.
Read/write scans use the whole internal affine length. Peeling and recentering
are exact tape identities. Marking, increment and both decrement branches
reuse the concrete box theorems, including the original-value physical guard
and explicit final padding. Terminal-only box placement is retained.

The arithmetic proof-producing checker has different soundness proof fields
from the original Core/Nat checker. The kernel-checked `sstep_eq` theorem
identifies their computed target/progress pairs exactly. It commutes
`Option.map` through equality-indexed Option/Move case analysis and moves
proof-indexed casts into proof arguments before erasure. These small generic
lemmas are proved by equality/case elimination. Finite structural cases then
prove the actual checker equality. No enumeration of all machine states,
execution oracle or replacement checker is assumed.

External induction on the existing executor fuel composes internal clocks.
Long scans and register boxes keep the native false progress flag; only a
literal transition supplies the positive clock needed by an initially false
progress flag. Accepted comparisons use checked `isMatch_value`, including
only the permitted discarded blank exterior. `verifiesHalt_sound` projects
state zero after retaining the complete reached configuration and final move.

Fuel, finite syntax, coefficients and branch labels are external standard
data. Values, gap, spare count, tape halves and resulting clocks range over
every IΣ1 model. This is **not** an internal-variable-fuel/syntax graph theorem,
a first-exit or dispatch invariant, full binary runtime internalization, a PA
consistency endpoint or a state reduction. A fixed definable nine-field
relation and arithmetic decoder-path/dispatch composition remain separate.
The existing external 252-state endpoint is unchanged. Mira-Cult, Jeff and Wade
retain their machine and verification-framework credit.

The final fifth check passes **25 ordered axiom reports and 20 callers**, with
only standard axioms and **zero new source/audit warnings**. It checks actual
write-changing scan and halt cases as well as the generic all-model APIs.
Pinned Lean 4.32.0 took 6.193s for source and 2.560s for audit. The four earlier
source nonpasses are preserved: direct rfl erasure failed, initial finite
control rewriting encountered dependent recursors, and a too-general erasure
rewrite also matched equality propositions. The final Option.map-specific
lemmas resolve those proof issues. No operational guard or semantic claim was
weakened. The successful source/audit bytes and original record are unchanged.

The guarded runner source/object-matches exactly 49 project providers from the
successful ConcreteBoxes record, five actual first external providers, all
direct Lean imports plus Omega, all 118 input identities and the fresh object.
No dependency is rebuilt or downloaded. The 49 reused objects are not a new
fresh compilation of that whole project or external cache closure.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_symbolic_execution_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --boxes-evidence /outside/successful-concrete-boxes/verification.json \
  --output /outside/new-empty-symbolic-execution-check
```

The portable runner changes only the default source hash to the successful
585-line module; the executed driver used an explicit source override. No
proof replay was performed for that pin-only change or file placement.
The maintained-default preflight is PREPARED_NOT_BUILT, with no compiler
commands. Python-O, a nonempty output and a shadowed first Omega provider are
separately rejected without proof compilation. Publication evidence keeps
those checks distinct from the successful proof build and independent review.
