# Final verified result

Implementation SHA-256: `42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61`.

The evaluator is proved equal to the frozen ordered factor composition on every finite binary support. It preserves factor order, simultaneous active-key semantics, exact reverse order, malformed raw competitors and contexts, and rediscovery after every change. It constructs source metadata and individual encountered factors only.

## Regression suite (each normal and `-O`)

- 12 small accepted sources
- 3,580 complete factor-descriptor matches
- 17,517 complete lazy-versus-eager composition comparisons, each with inverse and mass checks
- 71,695 sparse individual-factor comparisons
- 241 complete candidate-completeness sweeps over a source's full factor array
- 35 invalid-input/immutable-metadata checks
- An explicit malformed five-particle four-factor cascade

## Independent audit (each normal and `-O`)

- 5 source fixtures and 1,471 descriptor matches
- 14,710 raw-endpoint candidate checks
- 52,956 sparse individual-factor comparisons and 268 contextual guard checks
- 830 shape/random whole-step comparisons
- 8,192 exhaustive support/order comparisons, representing all subsets of two eleven-site universes in both orders
- Inverse roundtrips after whole-step comparisons
- 1,000 validation acceptance/exact-error fuzz cases and 15 typed invalid cases
- Independent universal source count without factor construction

The two suites are separate code paths, though both intentionally compare against the same pinned frozen compiler. Tests are not a formal verification; the all-finite-input argument is in PROOF.md and the independent audit.

## Literal universal source benchmark

Pinned source counts: m=122,622; p=66,066; a=75,495; J=0. E contains 134,645,688,597 factors and P contains 134,645,669,658, total 269,291,358,255. The declared composed radius is 3,292,955,588,459,274,804.

On this execution environment, final normal run:

- Metadata compilation: 3.811 seconds
- 128 actual startup CA microsteps with reverse checks: 0.0412 seconds
- 128 arbitrary endpoint/noise global cases with reverse checks: 0.0373 seconds
- Process peak RSS: 376,048 KiB (about 367.2 MiB), including parsed source, metadata and traces
- Largest tested-factor count per startup step: 4; largest changing-factor count: 2
- Largest tested-factor count among malformed cases: 8; largest changing-factor count: 2

The final optimized run also passed; metadata compilation was 5.461 seconds under concurrent test load. Timings are observations, not complexity guarantees.

The 128 steps do not finish startup, a Turing-machine step, or a halting computation. The global correctness claim follows from the ordered-evaluator proof plus small-source reference comparisons, not an unavailable eager universal comparison.

## Limits

Worst-case costs remain sensitive to changing and tested factors, each bounded above by the full factor count. Metadata validation retains explicit (J+2)^2 class tables and associated integer-mask costs. Exact coordinate bit lengths and adversarial Python hashing are accounted for in PROOF.md. No uniform fast bound over all malformed supports is claimed. There are no changes to frozen reports, source tables, or original compiler files.
