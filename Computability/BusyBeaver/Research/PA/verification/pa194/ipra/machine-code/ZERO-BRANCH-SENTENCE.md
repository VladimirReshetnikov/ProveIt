# Native iPRA sentence for the PA194 zero branch

`PA194ZeroBranchSentence.lean` states an explicit universally closed equality
of primitive-recursive terms. One term applies `PA194Stepper.stepper` at the
finite-branch clock defined by `clock` to the packed control-24 configuration;
the other is the packed control-24 result. Both configurations have left tape
code 1. The source file is `sourceFileCode` applied to eleven arguments, with
logical argument 8 replaced syntactically by the zero term. The other source
arguments, including spare and numeric suffix, remain universally quantified.
There are twelve object-language variables in the construction: k and the
original eleven argument slots; the slot corresponding to argument 8 is unused.

Writing `Z(k,t)` for the model interpretation of the primitive-recursive
`zeros` code and `f` for the source file term, the numeric right tape codes
are `1 + 256*Z(k,2*f+1)` at input and `17 + 128*Z(k+1,2*f+1)` at output.
The exact clock is specified by the finite PR term `clock`, which follows the
clock expression of `PA194Site27Step.zeroBranchSite27`; the source file is the
authoritative specification, not an externally evaluated estimate.

`modelSentence` derives this equality in every candidate-PRA model using the
zero-branch theorem after proving the substituted argument is zero.
`classicalPRA` uses completeness to derive its universal closure in classical
candidate PRA. `nativeIPRA` applies the existing equality-transfer theorem to
obtain the corresponding universally closed equality in
`IPRAStandardTheory.standardTheory`. This is a machine-specific, model-uniform
finite-step result; it does not assert either direction of the consistency /
nonhalting equivalence, or a source-controller equivalence. Lean's printed
axiom audits for all three theorems are `propext`, `Classical.choice`, and
`Quot.sound`, without `sorryAx`. Those are metatheoretic Lean axioms, not extra
axioms added to the object iPRA theory.

## Replay and limitations

`check-zero-branch-sentence.sh` pins and builds seven sources into one fresh
output, in dependency order: `PRAEqualityToIPRA`, `PA194ZeroOutputFile`,
`PA194ZeroOutputArithmetic`, `PA194TwoPassesZeroTo24`, `PA194Site27Step`,
`PA194StartupSentence` (its term helpers are reused), and the sentence source.
It checks the three named sentence axiom reports and rejects `sorryAx`. The
startup sentence and transfer sources are rebuilt here, but their own imports
and all other transitive prerequisites remain precompiled.

The successful original sentence check used several prebuilt PA194 overlays in
the exact search order below. The replay accepts that ordered list explicitly;
it does not rebuild or authenticate the mixed transitive object closure, and
source pins alone do not establish object compatibility. The result is therefore
a staged suffix replay with a material provenance limitation, not a clean
single-output full-closure rebuild. Its machine-specific baseline and general
project/foundation/Lake dependencies must be independently established from
matching sources before relying on this as a reproducible full verification.
The indicated paths are temporary session-local artifacts.

From the repository root:

```sh
roots=/dev/shm/pa194-dense-startup-agent:/dev/shm/pa194-standard-bridge:/dev/shm/pa194-startup-preserved:/dev/shm/pa194-model-neighborhood:/dev/shm/pa194bridge-probe/build:/dev/shm/binary-tape-code.1tywTlrA:/dev/shm/pa194-header-coherent/hardlink-baseline:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-zero-branch-sentence.sh" \
  "$PWD" \
  "$base/PA194ZeroBranchSentence.lean" \
  "$roots"
```

The checker rejects inherited `GIT_DIR`, `GIT_WORK_TREE`, `GIT_INDEX_FILE`,
`GIT_OBJECT_DIRECTORY`, and `GIT_ALTERNATE_OBJECT_DIRECTORIES`, and does not
set Git internal environment variables.
