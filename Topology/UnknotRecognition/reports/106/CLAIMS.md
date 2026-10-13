# Claims and evidence

## Proved in the article

- Exact exceptional-schedule reduction to disjoint mandatory groups and a
  bounded number of overlapping ancestor requirements.
- Exact special-row closure criterion and SCC quotient.
- Boolean and order-ideal determinant filters. Valid basis coefficients
  retain their original nonzero value; the filter multiplier is zero or one.
- Deterministic fixed-evaluation extraction in characteristic greater than
  the copy count, using repeated deletion scans.
- `J poly(N)` one-sided randomized discovery, `8**k poly(N)` for native
  unit triples, and `J (m+1)**w poly(N)` deterministic width search.
- `2**q J poly(N)` deterministic Kirchhoff counting and extraction as a
  theoretical alternative.
- Raw triangular-face arity, its normal-arc zero-pattern refinement, and
  the optimal lower-forest objective `|E3| - rank_G(E3)`.
- Exact static-gap quotient and inverse, with authenticated endpoint
  replay improving from `O(p*g)` to `O(g+p*log(g+2))` arithmetic work.
- A conditional composition bound: global quasi-polynomial time follows
  only if the explicitly listed completeness, state-count, size, production,
  transport, and width assumptions are proved separately.

## Implemented and independently checked

- Finite history, randomized covering, ideal, and deterministic width solvers.
- 15 solver test methods, including 4,096 exhaustive binary instances.
- Independent schedule, basis-polynomial, Boolean-closure, ideal-lattice,
  and live-code audits in `results/independent/`.
- Fresh source/reference equality on all 106 native cuts.
- 109 native implementation tests, with their commands in
  `results/validation/native_validation.json`.
- Five complete source-bound packets verified with the unchanged native
  whole-cut checker, yielding optional census coverage 97/106.
- Clean pinned-source application of four patches and byte-hash comparison
  of all 24 resulting source files.

## Empirical results only

- 55.7582 s → 42.6671 s full native query time (sum of per-case medians),
  23.48% reduction, five paired repetitions of the 106-case corpus.
- Canonical raw-core completion 100/106 → 106/106 with the `E3`-first forest.
- Native parameter histograms and preservation of all prior raw successes.
- Small observed `k`, `d`, `J`, and raw dual rank; no infinite-family bound
  is inferred from them.
- The eight-positive/six-nonhandlebody refusal split is historical oracle
  evidence tied to the exact corpus hash, not a fresh oracle experiment.

## Not claimed

- A complete quasi-polynomial algorithm for unknot recognition.
- Completeness of raw positive cancellation for all handlebodies.
- 106 full handlebody censuses or a 97/106 standalone knot-recognition rate.
- A polynomial bound on `J`, `d`, or `w` throughout all unknot hierarchies.
- Geometric correctness of an arbitrary unauthenticated graph/matrix input.
- A portable negative certificate for every exhaustive finite refusal.
- Deterministic polynomial identity testing for the general signed sieve.
- Formal Lean proofs or an exhaustive literature-priority certification.
- A full rerun of every test anywhere in the ProveIt repository.
