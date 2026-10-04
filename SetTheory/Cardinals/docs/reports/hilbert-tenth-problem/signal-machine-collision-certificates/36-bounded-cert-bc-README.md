# Three positive witnesses for bounded two counter halting

This separate arithmetic proof packet establishes an explicit three-positive-witness integer-polynomial family for fixed-horizon halting of any fixed deterministic two-counter program. It leaves the earlier physical, finite-trace, and native-gap packets unchanged.

Start with `PROOF.md`. The main theorem and unique-witness proof are independent of both physical simulation and Pell arithmetic. Section 8 gives an optional, completely specified native-gap composition using the retained POWER theorem dependency.

The construction uses K=T+1, N=K^2, an N-entry clipped-input acceptance table, and denominator-cleared integer Lagrange interpolation. Its ledger is three witnesses, six listed residuals, and one polynomial equation of degree at most 4N-4 for T>=1. At T=0 the displayed polynomial has degree two. The exact-first-halt variant has identical counts.

The expanded native polynomial has at most 16N-5 monomials for T>=1, with O(N log(N+1)) coefficient magnitude bits. A straightforward expanded binary description therefore has O(N^2 log(N+1)) bits. These bounds are proved in Section 6; no polynomial-time-in-log(T) claim is made.

The native-gap composition has 57 positive witnesses, 38 listed residuals, and three external inputs. Its degree is max(12,deg P), hence at most max(12,4N-4) for T>=1 and exactly twelve at T=0. Its full witnesses are infinite-fold, although its counter, power-output, and compressed-witness projection is unique.

The horizon indexes the polynomial family. Degree and coefficients change with T. No fixed-polynomial unbounded-halting, single-fold MRDP, novelty, or minimality claim is made.

Files:

- `PROOF.md`: definitions, all polynomial equations, proofs, bounds, caveats, and sources
- `static_algebra.py`: fresh exact polynomial construction and declared-fixture checks
- `evidence/static_results.json`: machine-readable finite algebra evidence
- `evidence/static_stdout.txt`: successful check summary
- `SOURCE_PINS.json`: exact inert dependency hashes and provenance
- `MANIFEST.json`: packet inventory and hashes
- `HANDOFF.md`: concise independent-review guide

The fresh checker passed 140 interpolation-node checks, 28 arbitrary-table polynomial ledgers, 1,904 input-grid class-uniqueness checks, 73,600 literal positive-witness tuples, nine declared fixtures, and 18 complete native-gap compositions. It executes no prior packet, author/upstream program, counter interpreter, physical simulator, schedule search, or Lean.

Finite evidence supports but does not replace the all-input proofs. The optional POWER composition depends on the exact source theorem identified in the proof. Physical transport is conditional on the separately retained physical theorem.
