# Scalar-separator elimination for normal-surface search

Research continuation for Vladimir Reshetnikov's **ProveIt** project, 12 October 2026.

**Read `article/article.pdf` for the complete article and proofs.** The editable TeX,
exact Python implementation, independent replay routines, tests, raw evidence,
and integration notes are included. This package does not modify the native
recognizer and is not a standalone unknot recognizer.

## Main results

A homogeneous subtree attached through one signed scalar has an exact
positive-objective continuation consisting of a positive-zero-port flag,
two sign-availability bits, and at most two rational slopes. Independent
subtree compatibility choices are summarized before reaching the parent.
The resulting cost is a sum of local searches, not their Cartesian product.

A source compiler verifies that each proposed column cut has
`rank(A_S) + rank(A_complement) - rank(A) <= 1` and that every forbidden pair
remains local. It creates signed flux equations and an independently checked
source-equivalence record. A proved no-new-rays theorem for these source-bound
flux-sign chambers shows that ray-based gluing produces an extreme ray of the
original matching cone. Primitive genuine standard-normal rays therefore
represent connected surfaces. Redundant arbitrary scalar models do not have
this extra guarantee; the tests include a counterexample.

The implemented active-zero-set enumerator has a proved local-binomial bit
bound. A sharper theorem, using polynomial-time rational LP locally, replaces
the global cone dimension by a sum of local intrinsic-dimension costs. The LP
backend itself is not included. A complete quasi-polynomial recognition
criterion is stated with decomposition-production and geometric costs explicit.
No universal width theorem or unrestricted quasi-polynomial implementation is
claimed.

## Validation included

The frozen run has 27 passing test methods. It also includes 96 seeded models,
768 global-oracle queries and the same 768 queries on source-recompiled models,
1,536 independently replayed result packets, and 455 checks that source-bound
positive supports have one-dimensional kernels. Source compilation replay
passes on all 96 models.

Two actual repository face-pairing fixtures have independently checked complete
admissible ray sets. On the two-tetrahedron fixture, the split `{0,1,10}` versus
its complement reduces candidate zero sets from 3,432 to 1,856. Seven paired
trials cover matching and Euler construction, source compilation and replay,
ray preparation, eight anchored Euler queries, and positive arithmetic checks.
The measured paired speedup is about **1.94 times** in this delivered kernel.
The naive split by tetrahedra is rejected: its cut-space dimension is three.
These are not native full-knot timings.

An algebraic gain chain has `2**m` global compatible ray histories but only
`2*m+2` retained local rays. The benchmark retains small cases where the
rational method loses. A two-coordinate counterexample proves an exponential
lower bound for literal finite-union-of-convex-cones messages, not for all
possible compressed representations.

## Run the package

Python 3.10 or later is sufficient; the exact tested environment is in
`evidence/results.json`. There are **no third-party Python dependencies**.
Run from the unpacked package root:

```bash
python -m unittest discover -s tests -v
python experiments/reproduce.py --out /tmp/scalar-separator-new-evidence
```

The optional output directory keeps the delivered evidence unchanged. The
reproduction script executes new experiments and timings; timings naturally
vary by machine and load. There are no asynchronous tasks or network requests.

A source-bound example:

```python
from scalar_separators import (
    Prepared, compile_source, verify, verify_source_compilation,
)
from scalar_separators.fixtures import solid_torus, normal_matching, normal_euler

tri = solid_torus()
A, n, pairs = normal_matching(tri)
chi = normal_euler(tri)
bags, parents = [tuple(range(n))], [-1]  # exact one-bag fallback
model, generators = compile_source(A, n, bags, parents, pairs)
assert verify_source_compilation(A, n, bags, parents, pairs, model, generators)

objective = {str(j): chi[j] for j in range(n)}
answer = Prepared(model).solve(objective, zeros=["2"])
assert verify(model, objective, answer, zeros=["2"])
assert answer["status"] == "POSITIVE"
print(answer["coordinates"])
# {'0': '1', '1': '1', '2': '0', '3': '0', '4': '0', '5': '0', '6': '1'}
```

The fixture adapters check reciprocal face pairings, not all manifold links or
knot-diagram ancestry. Production input must come from validated maintained
source producers. Do not turn `POSITIVE` into `UNKNOT` without the geometric
checks described in the article.

## Compile the article

The provided PDF is already compiled. With standard TeX Live packages:

```bash
python experiments/build_tables.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The table generator reads the frozen `evidence/results.json`; it does not run
experiments. Keep all article `.tex` files together. `build.sh` provides the
same test-and-build sequence.

## Integration and limitations

Read `INTEGRATION.md`, `CLAIMS.md`, and `SOURCE_AUDIT.md`. The reference
checkpoint is `4840e384b5a2961aabbb9cc78023b9ac5990acb0`; only a targeted source
review was possible, not a full checkout or native test run. Four currently
listed incoming ZIPs were inventoried but their contents were not accessible.
No claim of exhaustive overlap review is made.

The delivery is additive and self-contained. It assigns no report number,
changes no default behavior, and requires no copying of font files or upstream
binary artifacts. A production adapter, decomposition discovery, resource
budgets, cancellation, and native corpus validation remain separate work.
