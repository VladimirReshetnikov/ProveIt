# Increment in a fixed register file over an arithmetic model

`ArithmeticRegisterFilePerm252` proves the actual machine's marked-register
increment endpoint for a fixed finite file of arbitrary internal values,
followed by an arbitrary internal number of zero spares. It includes the
forward seek through preceding registers, the suffix shift, and the full
return. Every value, the spare count and the retained left tape may be
nonstandard elements of any model of IΣ1.

The prefix and suffix are external `List V` values. Their lengths are ordinary
finite lengths; this is not a representation of arbitrary internally long
lists. That distinction permits ordinary Lean list induction while covering
the machine's fixed nine primary registers. The growing zero-spare tail uses
the preceding internal induction proofs.

Let `T xs = ∑ (value + 2)` be the length of a fixed finite register file.
`fileCode` folds the unary register encodings onto a supplied right tape;
`reverseFile` folds their reversed encodings onto a supplied left tape.
The main theorem is the exact endpoint

```text
runFrom (2*T pre + 2*value + 2*T rest + 4*count + 7)
  (frame 72 left
    (fileCode pre (4*bitPrefix true value (fileCode rest (zeroBlocks count 0)))))
=
leftFrame 48 left
  (fileCode pre (registerBlock (value+1) (fileCode rest (zeroBlocks count 0)))).
```

The right exterior is blank as specified in the input. The entire left tape
is arbitrary and retained. Separate forward and return theorems permit an
arbitrary right tape. The theorem does not assert first exit or complete
dispatcher refinement.

The shift induction retains an explicit target register. Its carry identity
turns the newly written one and a crossed separator into the next ordinary
reversed register block. The return induction uses that same nonempty target
to avoid an incorrect zero-step change from entry state 63 to state 48 when
the finite suffix is empty. Preceding-register seek and return each take
`T pre` steps.

Audit callers cover an empty suffix, a nonzero arbitrary following register,
eight arbitrary following registers, zero target value, zero spare count,
and the bootstrap's fixed spare prefix: eight zeros, one register of value
one, then `56+count` zero spares. This verifies the endpoint's applicability
to that shape; a complete invariant connecting all instruction families and
the dispatcher remains separate. No state reduction or PA consistency
comparison follows from this module alone.

The construction extends the attributed `RegisterIncrementPerm252` contracts
and Mira's `mira-emmy` PR20 `Box.v` framework. Mira-Cult, Jeff Ketchersid and
Andrew James Wade retain the machine and verification attributions recorded
in this repository.

## Verification

The first guarded run passes pinned Lean 4.32.0: **seven named axiom reports,
14 callers, standard three axioms only, zero warnings**. Source and audit
take 2.397 and 2.999 seconds. The guard uses one thread and `-M4096`, reuses
34 source-matched project objects, five named external boundaries and the
actual first Omega provider, and rebuilds no dependency. The original
[successful record](results/arithmetic-register-file-perm252-verification.json)
is retained unchanged; publication preparation and independent review are
recorded separately.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_file_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/dependency-checkout \
  --increment-evidence /path/to/register-increment/verification.json \
  --output /fresh/external/register-file
```

The source and audit default to the maintained files. `--cache` selects
relocated predecessor objects with the recorded hashes; `--library-path`
selects existing dependency libraries. `--prepare-only` performs no Lean
compilation. The guard checks the exact project import closure, frozen
source/audit identities, compiler/dependency identities, all selected objects,
and actual direct toolchain imports plus Omega before and after the run.
