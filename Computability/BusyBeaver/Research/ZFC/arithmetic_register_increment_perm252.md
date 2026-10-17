# Internal increment of a marked register with zero spares

[`ArithmeticRegisterIncrementPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterIncrementPerm252.lean)
increments a marked unary register followed only by an arbitrary internal
number of zero spare blocks and the blank exterior. The exact endpoint is

```
runFrom (2*value+4*count+7)
  (frame 72 left (4*bitPrefix true value (zeroBlocks count 0)))
 = leftFrame 48 left (registerBlock (value+1) (zeroBlocks count 0))
```

The value, zero-spare count and complete left tape half range over every IΣ1
model. Two actual states 72/82 restore the marked 00 prefix to 01. The checked
[suffix shift](arithmetic_zero_spare_shift_perm252.md) moves across the unary
target and zero-spare tail, writes the added one and turns left. The return
lemma crosses the reversed zero blocks and nonempty target, preserving the
entire right half. Its Π1 induction quantifies entry state, value and both
complete halves, with the literal entry-row equation kept explicit. The
successor may therefore use entry 48 and changed right half 4*right+2.
The return target is value+1, yielding total time 2*value+4*count+7.

Zero values and zero spare counts are included. A caller instantiates 56+count
for the known boot family's zero suffix. Nonzero intervening/following
registers, first exit, absolute head/register-file framing, dispatch preservation
and the complete internal binary/scheduler comparison are separate. This
checkpoint alone does not cover the nonzero spare in the full boot file or
introduce a new consistency endpoint. The framework follows the attributed
`RegisterIncrementPerm252` contracts and mira-emmy PR20 `Box.v`; Mira-Cult,
Jeff and Wade retain their machine, verification and framework attributions.

The [fresh check](results/arithmetic-register-increment-perm252-verification.json)
passes five named axiom reports and eight callers, with standard Lean axioms
only and zero warnings. Source and audit took 7.279 and 2.147 seconds on pinned
Lean 4.32.0. Thirty-three project providers, five external first providers,
toolchain Omega, all 86 input identities and the fresh object were checked;
no dependency was rebuilt or downloaded. Earlier nonpasses retain the
ordinary multiply/numeral/digit normalization and the explicit Σ0-to-Δ1 lookup
definability lift. All theorem and audit statements remained unchanged.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_increment_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --shift-evidence /outside/successful-zero-spare-shift/verification.json \
  --output /outside/new-empty-register-increment-check
```

The portable checker freshly checks only this source and its exact audit.
It verifies the actual direct Lean imports of new and selected source files,
always including the first Omega provider. `--cache` relocates all 33 selected
project objects while preserving their required identities. The final
maintained-default preflight is **PREPARED_NOT_BUILT**, with no proof commands.
Only the portable default sourcehash differs from the executed original
checker, which used an explicit source override. Three argument/provider
rejection controls pass without proof compilation. The
[publication record](results/arithmetic-register-increment-perm252-publication.json)
keeps these statuses and the historical nonpasses separate.

The [independent final review](results/arithmetic-register-increment-perm252-review.json)
binds the complete proof delta, audit, portable guard and maintained preflight
to their exact bytes. Its 483 identity comparisons cover 92 paths; it performs
no further Lean build. The earlier source-only review remains preserved.
