# Full static review of the held balanced-shear implementation

**CHANGES_REQUIRED. One workflow finding; no additional mathematical or
collector finding. No execution approval.** This record binds the unchanged
seven-payload checkpoint at HOLD SHA-256
`11444fb3dadefec4ea147da06789d748c55a0f00b5dac87b3fbb6175b7ff8c43`
and SOURCE_PINS SHA-256
`db0511289e3508d0df41719cff33139fc161736f3ed05d24df9becdd16fb246c`.
All paths below are relative to `Computability/DiophantineConsistency/`.

## Finding: no fresh-replay receipt route

At `research/balanced-crt-gate-shear-finite/guard.py:70`,
`external_receipt(path, role)` permits exactly
`/tmp/balanced-crt-shear-{role}.json`, then requires that path not to exist.
The first five TOOLCHAIN commands consume all five accepted role paths.
Consequently the unchanged normal/optimized checker and pure-rebuild
programs cannot subsequently create fresh independent ROOT receipts at
distinct stems. Reusing the original paths is rejected; using distinct
ROOT paths is rejected as unreviewed. This is a workflow obstruction to
the intended preserved-first-results/fresh-replay process, not an algebraic
counterexample to the fixed shear or to those first five commands.

Before release, provide a bounded, explicitly reviewed fresh receipt route
for the four read-only roles, while retaining absent-file checks, fixed
external destinations, deterministic same-mode report bytes and the original
first files. A fixed second whitelist per read-only role is one possible
repair. The choice, corresponding command plan, changed core pins and final
held inventory require renewed exact-checkpoint review. No repair, deletion,
renaming, retry or execution is performed or authorized by this record.
ROOT independently identified this issue and this review confirms it.

## Complete read and immutable closure

Read every line of the 164-line guard, 184-line producer and 441-line
independent checker; all PROOF, README, TOOLCHAIN, SOURCE_PINS and HOLD;
the complete ordinary shear note and its translation-height dependency;
and the retained source/evidence boundaries. No code was imported to read it.
The parent centered proof, complete accepted verification and its source-map
scope were reviewed in the immediately preceding ordinary acceptance review;
their bytes authenticate unchanged here. All older executable files occur
only as authenticated evidence; none is adopted as runtime code.

Fresh inert authentication checked all seven held payloads, 125877 bytes,
the 1248-byte HOLD, all 186 external pins and six own-core pins. The eight
whole-tree declarations match every actual member, byte count and hash:

| Whole tree | Files | Bytes |
| --- | ---: | ---: |
| `research/balanced-crt-gate-shear` | 3 | 27019 |
| `research/fast-sparse-substitution-replay` | 6 | 55419 |
| `research/fast-sparse-substitution-replay-verification` | 24 | 244448 |
| `research/round16-common-name-centering` | 34 | 611657 |
| `research/round16-common-name-centering-plan` | 3 | 34844 |
| `research/round16-square-weighted-projections` | 51 | 1589004 |
| `research/signed-pell-cap-nine-factor-projections` | 54 | 1514504 |
| `research/translation-height-obstruction` | 3 | 7796 |

Every tree entry also equals its flattened direct pin. The held folder
contains only the seven declared payloads and HOLD, with no generated data.
The old centered folder still has no MANIFEST. All sixteen first-run data,
receipt, stdout and stderr destinations were absent at inert inspection.
This observation is not a first-execution release or a future freshness
guarantee; ROOT must check them again before any later release.

## Ordinary identities and independent arithmetic routes

The fixed map is x21=z21-2z10-2z11, with every other coordinate fixed.
Its inverse adds2z10+2z11. Both are integer linear maps inverse on the
whole integer space. Rowwise substitution preserves quadratic degree;
its SOS is precisely the old quartic under this map, in both directions.
No positivity or private-witness identity is imposed by the new chart.

The producer correctly accumulates integer coefficients, multiplies every
input factor using the three-term replacement only at21, substitutes every
complete row and squares every full transformed residual. Its norm/term
serialization handles cancellation and canonical monomials. It copies all
original metadata except the specified variant suffix, then independently
counts the complete generated coefficients. No changed-row list or selected
height is used instead of generating every row and coefficient.

The checker imports neither producer nor old arithmetic. For each monomial
with k copies of21, its double loop emits coefficient
binom(k,r)*binom(k-r,s)*d^(r+s), for every r,s>=0,r+s<=k, at the remaining
monomial times z10^r*z11^s*z21^(k-r-s). This is exactly the trinomial
substitution for d=-2 and inverse d=2. Its SOS collector uses unordered
pairs, with diagonal multiplier1 and off-diagonal multiplier2. These routes
are mathematically correct and independent of the producer's factor route.

Preparation recollects the whole accepted parent SOS, verifies all13 actual
occurrences of21, and compares every transformed occurrence with the full
ordinary formula, including constants and linear terms. The two shifted
weighted bilinear/addition row numbers and output indices are handled
explicitly. The corrected full row15 expression is used. Every other
row is checked unchanged. The complete forward quartic and inverse quartic
identities are checked coefficientwise before any saved output is trusted.

Actual profile verification checks the exact certificate schema, input and
output records, policy and inverse, full equation/header/variable/row-label
metadata, every row coefficient, the complete SOS, full reverse identity,
exact degree4, quadratic row bound, complete liveness, full support/height
and per-degree census. Boolean and floating coefficients or indices are
rejected using exact integer types. JSON comparison distinguishes Boolean
and floating metadata from integers. The seven selected coefficient checks
match the ordinary theorem; the lower bound98336 does not replace the
complete height computation or predict a new endpoint.

## Witness maps and source calibration

The complete centered maps, old translation certificate and endpoint are
embedded without removing fields. The inverse first applies the shear,
then all58 fixed translations, initializes all83 actual free factored
coordinates, reverses204 plain or203 weighted monic rules, performs the
mandatory original Horn private overwrites and applies the accepted source
ordinary maps. Forward order is the reverse semantic construction followed
by the inverse shear. Only the new shear and old translation are whole-space
bijections; the accepted private maps remain existential witness maps.

ENDPOINT binds all five other actual profile objects, both ordinary/evidence
seals, the original data index and whole copied source calibration. INDEX
binds all twelve actual profile files and all current code/pin bytes.
No new native/compiler/Pell program is called. The inherited ordinary
source131/Round15/C222/ZF-to-ZFC/native contract, fresh interval witnesses
and Hstar/H0 distinction stay within their accepted scope. The earlier
optimized exit143 remains historical and is not relabeled by this prep.

## All control and I/O paths

All33 negative controls per profile were traced statically. Each mutates an
actual loaded artifact, rebinds the affected chart/output/endpoint/index
records and uses the same semantic verifier as main. The required exact
error strings are reached by the intended row, coefficient/type, schema,
direction, inverse, coverage, map, census, calibration, endpoint or index
check. In particular outer hash rebinding does not repair the corrupted
mathematical or map payload. No control merely asserts an arbitrary claim
or depends on a disabled Python assertion.

The four valid controls per profile reorder a row's terms, split a row
coefficient, reorder quartic terms and add a canceling mixed pair. They
retain the full SOS/inverse/census/map/endpoint checks after rebinding.
Canonical saved term lists are a separate main guard, so algebraically
equivalent control presentations can be accepted without weakening the
semantic checks. The planned totals66 negative/eight valid are explicit;
no test or fixture has actually run in this review.

Both bootstraps use only standard libraries, disable bytecode and authenticate
all held payloads before importing the sole local guard. The guard is
authentication/JSON/path I/O only. main authenticates all direct pins and
whole trees before arithmetic, and again around data writes or before the
receipt. Duplicate JSON keys and nonfinite values are rejected. No producer,
optimizer, old checker or adopted polynomial module is loaded by the checker.

The data path is exactly one external absolute nonsymlink directory. Its
first creation and every data/receipt file use exclusive creation. All13
data objects are computed before writing, then read back with exact member
and canonical-byte comparisons. Pure rebuilds recompute the entire bundle
in memory and compare all canonical data, not only hashes or summaries.
Receipt bytes are the complete stdout and have no timing/path/process
fields. The fixed-path freshness restriction is sound for the initial
five commands; its missing fresh-role route is the sole finding above.

Only inert text, JSON, file-hash, whole-byte, path-existence and inventory
inspection was performed. No application or local helper/module import,
Python AST, collector, substitution, fixture, test, compiler, Lean or
TeX/PDF execution occurred. No new source/polynomial/data was emitted.
Only this outside review pair is authored; all held and parent bytes remain
unchanged. Execution remains HOLD until the workflow repair and both full
reviews bind the same final checkpoint and ROOT separately releases it.
