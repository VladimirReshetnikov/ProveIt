# The arithmetic Site entry reached by the blank bootstrap

`ArithmeticSiteBootPerm252.lean` binds the existing checked 82,552-step blank
bootstrap to the arithmetic interpretation used by the per-instruction Site
contracts. In every IΣ1 model it proves

```text
ArithmeticMachineRunPerm252.run 82552 =
  ArithmeticSitePerm252.startValue (replicate 9 0) 56 0 []
```

This entry has canonical state 94, hence arithmetic state code 95, an empty
PC path, gap zero, and nine zero primary registers. The spare representation
has eight zero registers followed by one register of value one, then the
56 zero-spare blocks in the variable suffix. Together these are the original 65 spares.
The one final false padding cell is retained exactly once.

The proof first establishes reusable compatibility laws. An externally finite
Boolean list is interpreted as a nearest-first numeric prefix with an arbitrary
internal untouched suffix. External-Nat induction identifies finite repeated
bit prefixes and register blocks with the corresponding arithmetic functions.
Finite list induction then identifies `fileCode` with the actual
`RegisterBoxesPerm252.registerBits` encoding. All four actual Box forms agree
with `SymbolicPerm252.boxBits` when the primary list has length nine. The raw `.decrement` Box uses truncated
subtraction and always appends the native zero block. The actual zero branch of
a decrement instruction instead uses `.unchanged`, as retained by the Site
contracts. The comparison retains an arbitrary internal suffix.

These compatibility results concern external finite lists and natural register
data cast into the model. They do not represent an internal variable-length
list or claim that every internal register value is standard. The previously
checked arithmetic box execution contracts cover arbitrary internal values.

A generic polynomial pairing identity identifies arithmetic Cantor pairing
with the live `Code254.P` on every natural input, and hence identifies numeric
configuration encoding. The closed boot binding uses these generic identities
and a small literal bit-list equality. It does not evaluate the huge paired
boot numeral, rebuild the bootstrap, or replay its machine steps. The existing
`ArithmeticBootstrapPerm252.internal_boot` supplies the execution result.

The new theorem supplies an actual blank-start entry for subsequent arithmetic
runtime work. It does not supply a represented internal PC decoder, dispatch
invariant, unbounded runtime simulation, or a new PA endpoint. The frozen
252-state machine and its external consistency theorem are unchanged.
Mira-Cult, Jeff and Wade retain their machine and framework attribution.

## Verification and reproduction

The final focused check passed 15 ordered axiom probes and 17 generic caller
examples using only `propext`, `Classical.choice` and `Quot.sound`. The source
and audit produced no warnings, taking 3.376 and 2.506 seconds respectively.
The official absolute Lean 4.32.0 compiler used one thread and a 4 GiB limit.
The guard reused exactly 57 source-and-object-matched project providers and
six external boundary providers, with actual first `Init` and `Omega`
toolchain objects. All 138 selected inputs and the fresh object were checked
before and after the commands. No dependency was built or downloaded.

The original successful record is preserved byte for byte in
[the verification record](results/arithmetic-site-boot-perm252-verification.json).
[Publication metadata](results/arithmetic-site-boot-perm252-publication.json)
preserves the three earlier nonpasses: cast/lambda elaboration and small
normalization errors in the first two attempts; then a successful source
check followed by a recursion-depth failure in an extra explicit Nat-clock
audit specialization. The final audit uses a generic numeric-frame consumer
in its place. The all-model source theorem and the other generic clock caller
were unchanged. The source changes repaired intended Nat-to-model annotations
and proof normalization; no machine operation, gate or tape convention changed.

The maintained portable checker differs from the executed driver only in its
default frozen source and audit hashes. Placement preflight and guard controls
perform no source or audit proof compilation; compiler discovery may invoke
`lean --version`.

From the repository root, with already-built pinned dependencies available:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_site_boot_perm252.py \
  --repo "$PWD" \
  --dependency-root /path/to/built/Proofs \
  --site-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-site-perm252-verification.json \
  --bootstrap-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-bootstrap-perm252-verification.json \
  --output /outside/empty/site-boot-check
```

Add `--prepare-only` to validate the selected providers without compiling.
Optional `--cache` and repeated `--library-path` arguments relocate existing
objects only when their selected source and object hashes still match the
recorded evidence. This is reuse of checked prerequisites, rather than a fresh
build of their source closure.
