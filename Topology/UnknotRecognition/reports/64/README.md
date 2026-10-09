# Optimal Disc-Completion Bases

**A research contribution for ProveIt — 9 October 2026**

The article proves an exact `2^(r-1)` weighted representative-family bound for disc completion along `r` individually labelled boundary intervals, with matching lower bounds and grade dimensions `binomial(r-1,d)`. It also proves the exact size of the classical rank-stratified cut bases on the full partition family: `(r-1)*2^(r-2)+1` for `r >= 2`.

This specializes established rank-based and linear-matroid representative methods. The connected-and-acyclic partition predicate is prior work, particularly Bergougnoux–Kanté (arXiv:1707.03584, Theorem 3.8). The article distinguishes the sharp refinement, the surface-gluing contract, and the conditional global implication from that background. It does not assert priority over every possible earlier use of exterior representatives.

## Status

The mathematical gluing, feature, rank, optimality, and weighted-reduction statements have complete proofs. The Python reducer, independent checker, graph/minor/ribbon oracles, and relation-level composition tests were executed. The geometric assembly algorithm is proved for a supplied input contract but is not implemented here. A complete quasi-polynomial geometric producer for arbitrary unknot inputs is **not** established.

The incoming GitHub directory was inventoried, but its ZIP files were not unpacked in this environment. Relevant earlier manuscripts were inspected through the user's Library. There was no runnable native checkout: no production recognizer test or native geometric benchmark was executed. See `integration/source_audit.json`.

## Read first

`article.pdf` is the compiled article. `article.tex` is self-contained apart from the two generated tables in `results/`; its bibliography is embedded. `references.bib` is supplied for integration convenience and is not required by the build.

`CLAIMS.md` separates proven, executed, conditional, and unexecuted claims. `integration/README.md` gives proposed additive placement and review gates.

## Reproduce

Python 3.10+ and its standard library suffice for the code; execution here used Python 3.13.5. A standard pdfLaTeX installation is needed for the article.

```sh
make test
make audit
make benchmark
make tables
make example
make check-example
make pdf
make checksums
```

`make benchmark` reruns measurements and replaces raw benchmark JSON. `make tables` only converts retained JSON into TeX/CSV; it does not rerun benchmarks. The narrative numerical discussion in `article.tex` describes the delivered run and is intentionally not silently rewritten when measurements change. `make pdf` rebuilds the tables and article, not the experiments.

`make verify-checksums` checks the delivery manifest. Rebuilding the PDF or rerunning experiments changes the corresponding hashes; regenerate the manifest only after reviewing those changes.

## Minimal API

Run from the package root with `PYTHONPATH=code`:

```python
from disc_basis import Candidate, reduce_family
from check_certificate import verify

candidates = [
    Candidate("left-01", (0, 0, 1), cost=1),
    Candidate("left-02", (0, 1, 0), cost=2),
    Candidate("left-12", (0, 1, 1), cost=3),
]
kept, result = reduce_family(candidates, r=3)
assert [c.id for c in kept] == ["left-01", "left-02"]
assert verify([c.record() for c in candidates], result["certificate"])
```

Partitions are canonical restricted-growth strings on zero-based labels. A cost is a Python integer, not a Boolean. Signed hexadecimal serialization supports very large costs. `control` distinguishes geometric interface types; the reducer never combines rows from different controls or grades.

The high-level `reduce_family` function validates all candidate records and enforces resource limits. Lower-level algebra helpers expect already validated partitions. `ResourceLimit` is an exception, not a knot verdict. Defaults cap the producer at 18 labelled intervals and 100,000 rows; the slower independent checker caps width at 12 unless explicitly changed.

## What the certificate does not certify

It proves a minimum-preserving reduction of the **supplied table**. The table digest covers labels, partitions, types, costs, and identifiers. It does not authenticate geometric witness bytes referenced only by an identifier, normal admissibility, embedding, a knot exterior, or the completeness of candidate generation. Those require a separate source-bound adapter.

A compressed port containing many seam copies is not one labelled interval for the theorem. Counting and Khovanov homology are not preserved by this minimum/existence reducer. Arbitrary pointwise attachments, caps, cuts, and hidden geometry-dependent compatibility are outside the contract.

## Executed evidence

18 unittest methods passed. The audit includes 44,168 exhaustive partition-pair checks, 1,155 independent minor comparisons, 3,336 weighted completion queries, 72 independently checked certificates, 2,000 ribbon-surface checks, 1,800 staged-join completion queries, and 5,295 Boolean projection checks.

The timed code compares full, A/A, cut-basis, and exterior-basis arms with seven shuffled rounds. It includes preprocessing, grade-indexing, cost-order early exits, signed weights, and a no-compression control. Most easy-query fixtures are slower after reduction; the cycle-rich rejection fixture improves locally by about 9.09x. These are abstract kernel measurements, not native knot-recognition results.
