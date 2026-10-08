# ProveIt Unknot Recognition - Report 25

## Causal-branch parameterization of Reidemeister-III unlocking

This bundle continues the performance work in
`Topology/UnknotRecognition` at reviewed ProveIt commit
`23893144e3aafd074a23cfb633222ab7e03e6d2e`.  It develops a new conditional
complexity theorem for the Reidemeister-III (RIII) preprocessing search, an
opt-in integration adapter, executable finite models, negative controls, and a
29-page article.

The central parameters of a first-unlocking RIII trace are:

- `k`: the number of RIII moves before an RI/RII reduction first appears;
- `b`: the number of **births**, meaning moves whose conservative fixed-dart
  footprints are disjoint from every earlier footprint.

Under explicit bounded-local commutation hypotheses, every first-unlocking trace
can be reordered, possibly truncating when a reduction appears earlier, so that
all births occur first and every later move meets the accumulated footprint.
The resulting complete bounded search runs in

```text
N^(b + O(1)) (C k)^k
```

with polynomial working memory.  For the reviewed fixed-dart RIII rules, the
article proves absolute footprint and incidence bounds.  Consequences include:

| Birth bound | Unlock depth | Running-time regime |
|---|---:|---:|
| `b = O(1)` | `k = O(log N / log log N)` | polynomial |
| `b = O(1)` | `k = O(log N)` | `N^O(log log N)` |
| `b = O(log N)` | `k = O(log N)` | `N^O(log N)` |

These are **restricted-class results**.  The bundle does not prove that every
unknot diagram has logarithmic birth number or unlock depth, does not prove a
general quasi-polynomial unknot-recognition algorithm, and does not replace the
exact Khovanov fallback.

## Main deliverables

- `article/report25.pdf` - compiled 29-page article.
- `article/report25.tex` and `article/sections/` - complete LaTeX source.
- `prototype/causal_search.py` - dependency-free reference implementation of
  the abstract rewrite model and the birth-front search.
- `tests/` - seven unit tests, including strict counterexamples and adapter
  mutation-contract tests.
- `experiments/exhaustive_validation.py` - deterministic comparison with an
  unrestricted BFS oracle on 5,000 generated six-site systems.
- `experiments/exhaustive_catalog.py` - exhaustive check of 608,400 three-site
  instances through depth four.
- `integration/clustered_r3_snippet.py` - opt-in accumulated-support and
  bounded-birth adapter for the reviewed private `_Darts` interface.
- `integration/connected_r3_simplify.patch` - review patch preserving the
  legacy `last` search as the default.
- `claims/claims_ledger.yaml` and `claims/research_log.md` - scope, rejected
  conjectures, proof-audit corrections, and open claims.
- `PROVENANCE.json` and `SHA256_MANIFEST.txt` - source pins, environment,
  verification status, and checksums.

## Verified in this bundle

The local unit suite passes all seven tests.  The deterministic generated-system
run produced:

```text
3,209 initially reducible
131 with no witness through depth 6
1,660 witnessed
0 front-loading failures
0 birth-front completeness discrepancies
0 disconnected shortest dependency graphs
```

The exhaustive finite catalog contains 608,400 instances, of which 171,968 have
a witness through depth four.  It produced zero front-loading, completeness, or
dependency-connectivity discrepancies.

These computations test finite abstract Boolean rewrite systems.  They are not a
substitute for the mathematical proof and are not tests on actual knot diagrams.

## Important audit corrections

The packaged version incorporates several proof and implementation corrections:

1. Connectedness is proved for the **full dependency graph**, not for every
   chronological prefix.  Two independent preparatory branches may be joined by
   a later move.
2. The completeness theorem is parameterized by the number of births; the
   one-birth accumulated-support search strictly contains the legacy
   last-touch search in the abstract model.
3. The search state includes accumulated support.  A repeated physical state
   cannot be pruned merely because its bits repeat.
4. The adapter suppresses only the exact inverse RIII triangle, not every move
   on the same crossing triple.
5. The repeated simplification theorem is stated for a fixed deterministic
   RI/RII and trace-selection policy; existential success under some different
   greedy choices is not silently assumed.

## Reproduce

From the bundle root:

```bash
./verify.sh
```

This syntax-checks the Python files, runs the seven unit tests, reruns both
finite validations into temporary files and checks their exact structural
counts, rebuilds the PDF, and performs a PDF preflight.  The PDF build uses a
fixed `SOURCE_DATE_EPOCH`; on the recorded toolchain it is byte-for-byte
reproducible.

Individual commands are also listed in Appendix A of the article.

## Integration status

The integration helper was checked against a twelve-dart contract gadget for
exact failure restoration and replayable inversion.  It was not executed in a
full ProveIt checkout in this environment.  Therefore:

- the 431 maintained tests reported by the reviewed commit were not rerun;
- no claim is made that the patch improves the maintained knot corpus;
- no actual PD-diagram fixture is claimed to separate last-touch from
  accumulated support;
- clustered mode must remain opt-in until repository-native replay, invariant,
  regression, and paired timing tests pass.

See `integration/INTEGRATION.md` for the merge checklist.
