# Whole binary frames for represented control states

`ArithmeticControlFrame254.lean` supplies a fixed Sigma1 relation between the
numbered literal program's coded nine-register state and its actual binary
entry frame. It also proves a positive actual binary runtime for each source
instruction case. Arithmetic values, spare count, gap and runtime witnesses
range over any `IΣ1` model. The control catalogue is the existing external
finite set of 6,460 actual leaves; valid arithmetic keys are classified by its
proved lookup theorem.

The file prefix uses the nine internal physical register projections. It is
followed by the exact spare pattern: eight zeros, one register of value1, and an
internal number of zero registers, with the checked final padding. The PC field
comes from the same actual catalogue index as the opcode and register selector.
The fixed 40-bit format and whole numeric tape halves agree with the existing
`ArithmeticSitePerm252.startValue` format at every numbered source.

`Related logical binary` explicitly requires a nonzero logical state and a
valid nonzero opcode, then existentially supplies the internal spare count and
gap for that whole frame. Invalid control0, even when packed into a positive
logical state, cannot satisfy the relation. Every related binary frame is
active. The relation has a fixed parameter-free Sigma1 formula and a checked
definability instance.

The six source-case contracts use the existing accepted actual-site proofs;
they do not recompute the 8,391 guard checks. Increment updates its physical
register and leaves the spare count unchanged. Zero decrement preserves the
file and count. Positive decrement truncates the selected value by one and
adds exactly one zero spare, including when its old value is1. Break and
continue preserve the file. The runtime output is the resolved numbered next
source, with the exact path-overflow gap adjustment. The halt contract retains
the literal final binary write/move and proves its numeric state is zero.

The resolver link uses `next_checked`'s actual walk witness and
`resolve_source`, so rebasing cannot select a different continuation through
an unproved path-identification assumption. Each runtime witness is positive.
The file/list conversion helpers concern externally fixed lists and finite
nine-field projections; no internal variable-length list encoding is assumed.

The pinned Lean 4.32 check passed the 332-line source in 7.566459s and the
124-line audit in 3.350305s: 27 ordered axiom probes, 30 caller examples,
standard axioms only and zero warnings. It reused 83 exact project source/object
providers and six external boundaries. All 189 inputs were checked before and
after; the fresh object remained unchanged after the audit. No dependency,
coverage-guard or 82,552-step bootstrap replay occurred.

Two nonpassing attempts remain explicit. The first source attempt failed on
ordinary tactic indentation, an untyped `Nat` cast-map binder, numeral
normalization and a definability tactic's proof reconstruction. The formula
arities had already been corrected, before the original unbuilt preparation,
to match their existing three-argument and two-argument uses. The eventual
explicit definability witness proves the same relation. The second attempt
passed the full source and all 27 axiom reports, then its last audit caller hit
the default recursion limit while simplifying the first catalogue entry.
Replacing that final simplification with explicit source-path and numeral
rewrites passed without increasing an option. The successful source was
unchanged between those last two attempts. Original records, sources, audits,
executed drivers, diffs and prebuild reviews are archived separately.

A focused portable replay uses the exact matching prerequisite objects:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_frame254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --step-evidence /path/to/arithmetic-control-step254-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` validates providers and writes snapshots without compiling the
source or audit; compiler-version discovery may run. The portable driver
changes only the final maintained default source/audit pins from the unchanged
executed driver. Optional cache and library paths must select the recorded
objects. No dependencies are downloaded or rebuilt.

This checkpoint's source-case runtimes still have to be calibrated against the
represented coded step to obtain a single `Related` step/halt theorem. A
represented iterator and the all-internal relation to the actual L2/Enum
scheduler remain separate obligations. This module alone does not establish a
binary/validator equivalence in PA, a new machine bound or a smaller calculus.
