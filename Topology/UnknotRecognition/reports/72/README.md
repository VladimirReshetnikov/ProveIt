# Rooted Disc Components and Sharp Ternary Completion Kernels

Research continuation for ProveIt, 9 October 2026. Reviewed repository snapshot:
`66098968e88bba797143ac1bf7ad0ac4c5f697df`.

The article proves a sharp finite-interface compression theorem for finding a **distinguished disc component**, while unrelated components may be non-discs. This extends, rather than replaces, the incoming whole-disc kernels. It is not a general quasi-polynomial unknot recognizer and makes no native whole-knot speed claim.

## Main results

For `r >= 1` individually labelled boundary intervals, one distinguished, the uncharged rooted compatibility matrix has binary rank exactly `3**(r-1)`. Component charges in `H = (F_2)**k` give rank `q*3**(r-1)` for each exact charge, and the same rank for nonzero charge when `q=2**k >= 2`. Cost-ordered original-witness bases of that size preserve all these completion optima. The weighted bound is sharp for universal exact-charge queries; no matching weighted sharpness claim is made for the nonzero-only query or a restricted ambient completion class.

A complete finite layered patch language of width `b` (excluding a permanent root marker) can be searched in `poly(I,B,b) * q**3 * 27**b` bit time with elementary elimination. Non-root components with no remaining ports can be forgotten without deleting their costs or witness material. A separate root-selection theorem gives a factor-two frontier-width bound for cyclically rotated site orders. The delivered executable implements layered languages, not a general site-order compiler.

## Start here

`article.pdf` is the complete article, and `article.tex` is its source. The `results/*.tex` files are generated tables and macros required for compilation; the full ZIP includes them. `INTEGRATION.md` describes the native admission gate. `THEOREM_LEDGER.md` separates proved, executed, conditional, and unimplemented claims. `SOURCE_AUDIT.json` records the inspected repository paths and prior material.

## Run without installing dependencies

From this directory, using Python 3.10 or later (tested with CPython 3.13.5):

```sh
python -m unittest discover -s tests -v
python -m experiments.audit
python -m rooted_disc examples/workload.json --check --output checked.json
```

The last command reruns the finite-language search, independently checks complete option generation and all reductions, and replays the selected surface as a triangle mesh. It prints only abstract-language statuses. The saved `examples/checked_answer.json` contains the search transcript; `examples/cli_checked_answer.json` also includes the executed checking summary.

To check an already saved transcript without invoking the producer:

```python
import json
from pathlib import Path
from rooted_disc.assembly import Grammar
from rooted_disc.search_verify import verify_search

grammar = Grammar.from_dict(json.loads(Path("examples/workload.json").read_text()))
answer = json.loads(Path("examples/checked_answer.json").read_text())
assert verify_search(grammar, answer)
```

This proves the reported result for the supplied abstract language, including negative answers. It does not prove that the language is complete for any knot exterior.

For the full timing experiment and article build:

```sh
python -m experiments.benchmark
python -m experiments.make_tables
sh build.sh
```

The benchmark uses three repetitions of exact, basis, and duplicate exact-control arms in randomized order. It may take longer on a slower host. Original raw results are supplied. Re-running replaces local timing files; generated manuscript macros keep the corresponding timing statements consistent with those files.

## Code map

- `rooted_disc/kernel.py`: validated states, sparse ternary features, graph predicate, exact-charge/nonzero pairings, weighted basis and source-bound expressions.
- `rooted_disc/verify.py`: independent saturation/transversal feature reconstruction and algebraic certificate checking.
- `rooted_disc/assembly.py`: exact-state and basis-reduced complete layered searches.
- `rooted_disc/search_verify.py`: independent complete-language replay using BFS rather than the producer's union–find transition; detects omitted candidates even with fresh valid linear evidence.
- `rooted_disc/mesh.py`: literal discs/annuli, separated boundary-edge gluings, manifold-link checks, componentwise Euler counts and formal charges.
- `tests/` and `experiments/`: tests, exhaustive/randomized audits, workload constructors and paired measurements.

## Executed validation

42 test methods pass. The audit checks 53,869 uncharged ordered pairs and 137,440 charged pair-target cases, plus 302,622 direct tensor-rank matrix entries. It verifies 1,000 randomized weighted families and 10,000 optimum queries, 1,000 mesh gluings comprising 24,567 triangles, and all 3,200 assignments in 200 finite languages. All 200 complete search transcripts pass the independent checker, including 109 negative languages. The 91 positive witnesses also pass independent mesh replay. A regression test handles 20,000-bit signed costs without decimal-conversion limits.

Final paired measurements show approximately 2.59x, 6.13x, and 13.27x gains on the three wider abstract workloads, and slowdowns on two controls. These figures are local measurements, not native recognition results. See `results/benchmark.json` for every sample and the duplicate-exact controls.

## Contracts that must not be omitted

All seams are individual, separated, collared boundary intervals. A “bad” component is irreversible only within an interval-gluing phase; circle capping and surgery are outside this contract. A geometry key must bind the actual source region, active labels, maps, peripheral basis, charge ownership, and all legal-continuation conditions. The key string does not authenticate those facts.

Costs are **total assembly costs**, including unrelated components. They are not root-only costs. Charges are per component, not aggregate over the whole surface. The abstract mesh checker realizes bad components as annuli and uses formal charge labels; it does not construct a three-dimensional embedding or boundary-torus cocycles. A root marker's dummy cap is only an algebraic device and is not appended to the physical output.

Binary multiplicity does not reduce the number of actual seams. No source-complete bounded-width producer, native integration, production test rerun, or proof-assistant formalization is included. Resource limits raise `ResourceLimit` or produce CLI exit code 2 with `INCONCLUSIVE_RESOURCE_LIMIT`; they never establish nonexistence.

JSON costs are signed hexadecimal strings (`"0xa"`, `"-0x10"`), and charges are small integers representing bit vectors. Public Python constructors accept integer costs. The complete source and every declared interface remain available for independent review.
