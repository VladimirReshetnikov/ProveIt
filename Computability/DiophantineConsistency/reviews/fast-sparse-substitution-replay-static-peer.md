# Complete fast sparse-substitution overlay static peer review

Verdict: **PASS — full static review only**. No blocking finding remains.
The exact accumulator identity, explicit support adapter, complete old
main invocation, report-byte gate and immutable source boundary are sound
on static inspection. This approval does not release execution or assert
a runtime result or speed improvement.

This review binds `research/fast-sparse-substitution-replay` at HOLD SHA-256
`6f18aaaa2899a9552bafc05110ec6cc309aa6458ac952dfe6bba53ed61bda059`
and SOURCE_PINS SHA-256
`29277dd37b33fc6a10f6afa46246ee8ecff126c3ac893beb62faecb2da42f135`.
Paths below are relative to `Computability/DiophantineConsistency/`.
I authored no implementation and changed no held, old-source, parent,
data or maintained-page file.

## Complete read and fresh authentication

Read every line of the complete new `replay.py` (213/11577 bytes),
`substitution.py` (16/599), PROOF (140/8122), README (53/3509), SOURCE_PINS
(652/30627) and HOLD (26/985), including all fixtures, error paths,
restoration branches, serialization, command and output code.

The entire adopted old checker (238/18542 bytes) and vendor (407/30079)
were read completely in the immediately preceding inert API challenge.
Both full hashes authenticate unchanged here. The old checker was also
reread completely for this full review, as was its complete 184-line
ordinary centering proof. The vendor's active normalization, multiplication,
substitution, sorted-term and literal-SOS primitives and whole translation
path were reread; the prior complete read of all other vendor code is
reused transparently. No module was loaded to inspect it.

Freshly authenticated all 144 external pins and four own core pins, the
five held payloads totaling 54434 bytes, and the 985-byte HOLD. The exact
overlay inventory is those five payloads plus HOLD. Independently derived
the required closure from the entire observed tree, both outside ROOT
observation records, and each complete parent inventory; it equals the
144 declared external paths exactly.

The observed old tree has exactly 34 files and 611657 bytes, all unchanged,
with no final MANIFEST. Its outside observation JSON is 5914 bytes, SHA-256
`af2b80aecbdf8bf701700df3b1e1184e09259c5fdcaec04f1a0c45379b944959`.
Read the complete JSON and explanatory Markdown and authenticated both.
Every original code/vendor/data/receipt/stdout member is bound, rather
than only the pre-execution HOLD or selected expanded polynomials.

Authenticated every member and exact membership of all three parents:

| Parent | Payloads | Payload bytes | Manifest SHA-256 |
| --- | ---: | ---: | --- |
| `research/round16-common-name-centering-plan` | 2 | 34390 | `ed0f0365d85209797f50fd450bde8b929fc853772e9ae2fb1d1346d090bff4e1` |
| `research/round16-square-weighted-projections` | 50 | 1581561 | `34b2b1b6f27dea48cfc7692ad64e5a034304e76cb0d3ef47eae87ec194862acd` |
| `research/signed-pell-cap-nine-factor-projections` | 53 | 1508981 | `c48ecc2d0cf12e125ecc9ab45849073e6d06a303a38e130aa6fd42859168aefd` |

These are 105 parent payloads and 3124932 bytes. Both string-only and typed
manifest records are checked under their actual schemas; nested payload
manifests remain included. All runtime dependencies authenticate before
any nonstdlib import, and the whole authentication runs again after the
old main finishes. No source/calibration application is imported or run.

## Universal substitution proof and all twelve controls

For every input monomial the helper retains the exact original `con(c)`
and every original `mul(a,r if j==i else v(j))` call. Thus both algorithms
produce the same expanded contribution a_m. For each output monomial,
both accumulate the same finite sum of integer coefficients. Removing a
zero intermediate coefficient changes no later sum; one final zero
filter therefore gives the same extensional polynomial. There is no
degree/support bound, changed replacement rule or special treatment of
unchanged monomials hidden in the helper.

All writes go to fresh temporary and result dictionaries. The adopted
con/v/mul functions also return fresh dictionaries and never mutate their
inputs. Empty/absent/zero cases, shared p/r inputs and a replacement
containing i retain the original one-level substitution semantics.
Insertion order may differ after cancellation and revival; that distinction
is correctly documented instead of asserted equal.

Manually checked every handwritten expected result without executing a
fixture or collector. Let x_j denote the variable at index j:

| Fixture | Exact expected polynomial checked manually |
| --- | --- |
| empty | 0 |
| constant | -5 |
| absent_index | 3*x_1^2-2*x_2+5 |
| unit | 2*x_1-3 |
| zero_replacement | 4*x_2 |
| negative_constant | 6*x_1 |
| square_cancellation | x_1^2 |
| replacement_contains_index | x_0^2+2*x_0*x_2+x_2^2-x_0*x_1-x_1*x_2 |
| quartic_cross_terms | 3*x_3^4-24*x_3^3+72*x_3^2-96*x_3+48-2*x_1*x_3^2+8*x_1*x_3-8*x_1+5*x_2 |
| nonlinear_replacement | x_1^4+4*x_1^2*x_2+4*x_2^2-x_1^2-2*x_2 |
| cancel_then_reappear | 1+x_1^2+x_1 |
| aliased_inputs | x_0+2 |

The order fixture is effective: old repeated pruning yields key order
constant, x_1^2, x_1; final-only pruning yields x_1, constant, x_1^2.
Both sorted term lists and extensional dictionaries agree. Each planned
case compares the literal saved old sub, helper and explicit expected
coefficients, checks input contents/order unchanged, checks fresh output
distinct from both inputs and the old result, and checks canonical sorted
monomials with nonzero exact integer coefficients. The controls supplement
the universal proof; none was run by this reviewer.

## Correct integration with the entire original verifier

The preliminary unused-patch trap is resolved explicitly. The wrapper
loads the old checker only after authentication, saves its original
support function, and installs a one-call adapter. The unchanged old main
calls that adapter; it invokes original support, performs the differential
checks against the saved literal sub, replaces A.sub, verifies every other
vendor attribute by identity and unchanged attribute membership, and
returns that same module. The only vendor arithmetic attribute replaced
is sub. The support adapter and argv are restored in finally; redirected
stdout is also restored if old main fails.

Vendor translation looks up sub in its own module globals, so forward
row translation uses the patched function. The old checker's reverse
quartic chain calls the same module's A.sub directly. No discarded
support module, replacement old main, producer import, cached summary,
weakened check or skipped profile is introduced.

The unchanged main retains exact twelve-payload membership, canonical
serialization of all thirteen data JSON files, complete independent index
comparison, fixed58 policy derivation and both real verify/control calls.
It checks exact shift/name/index/type/schema/convention fields, every row
and metadata field, literal complete raw/chart residual-square collectors,
all SOS coefficients, degree/liveness/whole census, source/map/endpoint
bindings and inverse order. Reverse substitution still traverses all 58
shifts on the complete quartic, compares every raw coefficient and the
whole leading form, then retains two signed fixtures per profile.

All 64 original actual negatives retain their intended error sites,
including rebound inner equation hashes; all four valid algebra controls
retain refreshed endpoint inventories. Whole parent maps still include
all 83 free coordinates and 204/203 reverse monic rules, followed by the
mandatory Horn overwrites and accepted source maps. Translation inversion
precedes those maps. No private-tuple identity or stronger native theorem
is inferred by this overlay.

The consumers tolerate the documented dictionary order change: translated
rows serialize through sorted A.terms; reverse/leading comparisons use
dictionary equality; degree, extrema, counts and exact integer evaluations
are order independent; used coordinates are sorted. The mixed negative's
monomial selection comes from the immutable serialized base's A.norm,
not an accumulator result. Consequently existing ordered control labels
and the whole report need not change.

## Report, output, determinism and historical boundary

The literal old main really writes its newly computed report to a separate
external old-output path. Its entire bytes and captured stdout must equal
the pinned mode-specific CHECK.json/CHECK_OPTIMIZED.json, with exact sorted
JSON, indentation and final newline. The comparison is an extra gate
after actual complete verification, not a replacement for running it.
The outer report nests that produced report and adds separately identified
overlay hashes, adapter/control evidence and historical status. The old
source-pins hash, real optimization flag, summaries, control lists and
scope remain intact.

All checks use explicit raises and remain active under optimized Python.
No elapsed times, object identities or unordered-set iteration enter a
receipt. Sorted JSON and fixed source metadata support deterministic
mode-specific reports. No speed, new height or term-count result is
predicted. Failures propagate without a synthesized outer PASS.

Both resolved output paths must be distinct ordinary files outside the
entire repository, with no symlink component. The original safe-receipt
and changed-existing-content checks remain, and the wrapper refuses a
different existing outer receipt. Only the old report and outer report
are written; stdout contains the complete outer report. The two proposed
normal/optimized commands use distinct external JSON/stdout/stderr paths,
require no empty tracked directory, and explicitly stop at first failure.
Bytecode writing is disabled before imported modules could create caches.

The observed source is explicitly not a finally accepted endpoint.
All five original author PASS results, original fresh normal PASS and
pure-build replays remain historical evidence. The original fresh
optimized exit143 remains unresolved, with no report or diagnostic and
unestablished cause. Its exact status is carried in overlay provenance;
any future overlay PASS is a separate program/run and cannot relabel it.
New full runtime and fresh replay evidence, endpoint decisions and any
later promotion remain ROOT's separate responsibility.

This review used only inert text/hash/JSON reads. No new or old application,
helper, module, fixture, substitution, compiler, Python AST, benchmark,
Lean, TeX/PDF or source/native program was imported or executed; no tuple,
polynomial or source data was generated. Only these two outside peer
records were authored. The exact held overlay has full static peer
approval; both full approvals and ROOT's explicit release are required
before either proposed command.
