# Compiler audit and finite register-program certificate

The included **269-state control reproduces prior work**. The **283-state
PSC+IR control is a new compiler measurement** that retains every original
logical/equality row. Neither is presented as a new smaller ZFC-consistency
machine. `compiler-audit.txt` explains the exact recipes, proof boundaries,
destructive-parameter hazard, and bounded searches.

## Offline verification without a repository checkout

From the archive root, run:

```sh
python3 compiler/recheck_included_certificate.py --self-test
```

This uses only Python 3.10 or later, its standard library, and the included files. It checks
the **4,533-pair operation-site bisimulation** between the original 219-node
register program and its 207-node rebracketing. The result reports 1,931
decrement-test pairs, 2,601 increment pairs and one halting pair. Both branches
of every decrement test are checked. The optional self-test deliberately
swaps a zero/positive branch pair in a temporary certificate and verifies that
the independent checker rejects it.

The verifier imports neither the grammar generator nor the TM compiler. Its
independent string/integer path engine and wrapper are copied unchanged from
the attributed prior incoming report. See
`independent_verifier/ORIGINAL_NOTICE.txt` and
`independent_verifier/NOTICE.txt`. Run without Python `-O`; the inherited
checker uses assertions. The runner rejects assertion-disabled execution and
launches the inherited verifier with Python environment flags ignored.

`offline-verification.json` records the successful authoring-time run. This
is executable finite evidence. It is **not a proof-assistant theorem**, a
proof of the binary TM interpreter, or a theory-consistency calibration.

## Selected measured controls

| Control | Decision states | Framework states | Working states | Total binary rows |
|---|---:|---:|---:|---:|
| Original source, attributed Re-Pair seed 341/exponent 4 |207|62|269|538|
| PSC+IR with all original logical rows, seed 46/exponent 4 |221|62|283|566|

`original-269.tm` and `psc_ir-283.tm` are complete numeric tables. Both
include initialization. Their named sources contain the public backend's
missing `1.inc/read1` row; normalization makes it a tape-preserving write-1,
right-move transition to halt under the source missing-row-halting convention.
The exact row adjustment and table hashes are in `compiler-controls.json`.

The PSC control retains the original base-four codec and equality, emits the
fresh-offset PSC template with `k=c+2`, adds `All(1, Rel(1,1)->F)`, and keeps
gated membership/equality vacuity and the cleanup tail. Its emitted-code
falsity/PSC/calculus adapters and complete binary simulation remain unproved.
The 283-state count is the minimum of the explicitly recorded 1,024-member
search family; it is not an optimality theorem.

## Optional compiler regeneration from the pinned inputs

```sh
python3 compiler/compiler_controls.py \
  --repo /path/to/ProveIt \
  --prior-grammar /path/to/rebracket_axioms.py \
  --output /tmp/compiler-controls

python3 compiler/check_parameter_acquisition.py \
  --repo /path/to/ProveIt \
  --output /tmp/parameter-acquisition.json
```

Use ProveIt commit `96836f9eea3540e96322c3d28c7127a582aae223`.
The prior grammar source is the version in the incoming
`zfc_small_machines_20261016.zip` archive, at
`vendor/one_schema_machine/rebracket_axioms.py`, SHA-256
`bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119`.
These optional regeneration commands require those original inputs; the
offline certificate command above requires neither of them.

The parameter audit verifies that exactly 12 of 24 abstract rho8 parameter
permutations keep the emitter's destructive fourth-parameter read at one
occurrence, and checks a Boolean counterexample for an inadmissible
permutation. The prior 248 generator already enforces that acquisition
condition; this audit does not allege a defect in it.

All distributed file identities are recorded in `SHA256SUMS.json`. No
compiler or theory bound follows merely from a hash or a finite run.
