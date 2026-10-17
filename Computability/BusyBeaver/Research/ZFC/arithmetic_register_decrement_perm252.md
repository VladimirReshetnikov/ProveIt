# Internal positive decrement with a variable zero-spare tail

[`ArithmeticRegisterDecrementPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterDecrementPerm252.lean)
ports positive decrement on the frozen 252-state table. For fixed finite lists
`pre` and `rest` of arbitrary internal register values, its exact endpoint is

```
runFrom (2*fileTime pre+2*value+2*fileTime rest+4*count+9)
  (frame 43 left (fileCode pre
    (4*bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0)))))
 = leftFrame (positiveExit pre) left (fileCode pre
     (registerBlock value (fileCode rest (zeroBlocks (count+1) 0))))
```

The marked positive target decreases from `value+1` to `value`; all other
registers remain unchanged and exactly one zero spare is appended. An empty
prefix keeps return state 63, while a nonempty prefix returns to probe 48.
Every register value, spare count and complete left tape half ranges over
an arbitrary IΣ1 model. List lengths are externally fixed. The full positive
endpoint specifies a blank right exterior; the local block-shift and return
lemmas retain arbitrary complete right halves.

State numbers here use arithmetic coding: working state `q` is canonical
table state `q-1`, and state 0 means halt. Arithmetic states 111/130
(canonical 110/129) shift a single block left. Their exact intermediate
zero/header accounting is composed with a Π1 induction over the internal
zero-spare count, universally quantifying both whole tape halves. A finite
`weaveFile` fold describes the temporarily displaced headers, and its checked
reconstruction identity restores the normal register-file representation.
The actual 84/96 suffix scanner, 43/59/74 positive test and final 130-to-63
turn supply the remaining literal transitions. The total time includes the
seek and return over the prefix, both suffix crossings and all changing
zero spares.

This extends the [register-file increment](arithmetic_register_file_perm252.md)
with the positive-decrement spare-growth effect. It does not assert first
exit, absolute head framing, a complete dispatch invariant or the internal
binary/scheduler comparison. It changes no machine table or calculus and
introduces no consistency endpoint. The underlying contracts are attributed
to mira-emmy PR20 `Box.v` and the maintained `RegisterDecrementPerm252`;
Mira-Cult, Jeff and Wade retain their machine, verification and framework
attributions.

The [fresh verification](results/arithmetic-register-decrement-perm252-verification.json)
passes ten ordered axiom reports and twelve callers, with standard Lean
axioms only and zero warnings. Source and audit took 5.366 and 3.195 seconds
on pinned Lean 4.32.0. Exactly 35 project providers, five external first
providers, toolchain Omega, all 90 input identities and the fresh object are
checked. No dependency was rebuilt or downloaded. Run1 retains six ordinary
state-label numeral-coercion errors; run2 passed the source and reached the
audit's default recursion limit. Explicit numeral adapters and audit resource
limits fixed those failures without changing any statement or caller.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_decrement_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --file-evidence /outside/successful-register-file/verification.json \
  --output /outside/new-empty-register-decrement-check
```

The portable checker verifies the successful file 7/14 predecessor, exact
source and selected-object closure, dependency pins, actual direct Lean
imports and the first Omega provider. It freshly checks only this source and
its audit. `--cache` relocates all selected project objects with their hashes
preserved. The maintained-default preflight is **PREPARED_NOT_BUILT**, with no
proof commands. Its source and audit match the successful snapshots exactly;
only the portable default hashes differ from the executed original checker,
which used explicit overrides. Three argument/provider rejection controls
pass without proof compilation. The
[publication record](results/arithmetic-register-decrement-perm252-publication.json)
keeps fresh proof checks, preflight, negative controls and historical failures
separate.

The [independent final review](results/arithmetic-register-decrement-perm252-review.json)
binds the complete proof delta, audit, portable guard and maintained preflight
to their exact bytes. It checks 507 identities across 96 paths without a
reviewer proof rebuild. The earlier prebuild review remains separate.
