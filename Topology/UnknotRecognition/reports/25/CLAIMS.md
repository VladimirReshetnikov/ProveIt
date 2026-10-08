# Claim and validation audit

| Claim | Evidence | Boundary |
|---|---|---|
| Exact Artin braid states | Classical Garside normal form; article Section 3; tests | Not permutation equality, not a finite quotient |
| Optimal disjoint one-pass kernel | Article Theorem 4.1; independent exhaustive interval oracle | Not global geodesic, conjugacy, Markov, or saturation optimality |
| Shared all-cut algebra | Article Theorem 4.2; exact append counters | Scalar O(n^2 M) term remains |
| Height/bit bound | Article Theorem 5.1 and explicit potential | Radius and target dictionary are charged |
| Replay soundness | Article Theorem 6.1; separate verifier; corruption tests | No Lean proof of Python execution; does not certify optimality |
| Infinite radius separation | Article Theorem 7.1, lattice and signed-pair proof | Whole-word Garside normalization also handles the family |
| Geodesic unknot family | Article Theorem 8.2, C2*C3 syllable/parity proof | Does not obstruct conjugacy, Markov moves, or compressed-object algorithms |
| Quasi-polynomial recognition class | Article Theorem 9.2 and Corollary 9.4 | Requires a small kernel and uncapped exact fallback |
| 47 tests pass | `data/test_log.txt` | Package tests, not the upstream 272-test suite |
| Compressor timing gains | `data/benchmarks.json`, seven paired rounds and A/A | Not end-to-end recognizer gains or broadly representative samples |
| Optional integration adapter | `integration/probe.py`, inspected Diagram API | Not installed, executed against upstream, or production validated |
| Suggested OpenAI/math inspiration | Pinned inspected BraidRestriction.lean | No imported new theorem needed; no wholesale endorsement |

All source citations and exact repository identifiers are in the article and
source manifest. The implementation uses classical mathematical facts plus
the proofs developed in the article. Priority across the entire literature
has not been established. There is no general quasi-polynomial recognition
claim and no claim of having run an unavailable full checkout.
