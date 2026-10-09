# Arithmetic continuation and checked Montesinos tangles

This continuation adds complete exact recognition for a **supplied Montesinos
presentation**, plus an **opt-in local obstruction search** for ordinary PDs.
The source-based decision uses rational-tangle arithmetic and the topology of
the associated Seifert-fibred double cover. The local test uses
[Nogueira--Salgueiro, Theorem 4.9](https://arxiv.org/abs/2110.15645).
The general recognizer still has an exponential worst-case bound; recognizing
or finding an unrestricted Montesinos decomposition in an arbitrary PD is not
implemented. The existing Khovanov backends are unchanged.

## Supplied rational tangles and exact source recognition

The new JSON key describes the numerator closure of an integer tangle `e`
followed by a horizontal sum of rational tangles. Each inner list is an
ordinary continued fraction `a0 + 1/(a1 + 1/(...))`. Negative coefficients and
zero intermediate denominators are supported using projective arithmetic;
each final tangle slope must be finite.

```json
{"montesinos":{"e":0,"tangles":[[2,3],[-2,-2,-1,-2]]}}
```

This example is a 12-crossing unknot that the inherited RI/RII simplifier leaves
unchanged. Run a file containing it with `python -m fastunknot recognize FILE`.
The Python interface constructs the same validated planar diagram:

```python
from fastunknot import Diagram, recognize

diagram = Diagram.from_rational(0, [[2, 3], [-2, -2, -1, -2]])
result = recognize(diagram)
assert (result.status, result.method) == (
    "UNKNOT", "montesinos-two-bridge-determinant")

# Compare the inherited pipeline on this exact PD.
baseline = recognize(diagram, use_rational=False)
assert baseline.status == "UNKNOT"
```

`Diagram.from_montesinos` is an alias of `Diagram.from_rational`.
`--no-rational` is the CLI equivalent of `use_rational=False`. In JSON, `e`
defaults to zero and `tangles` is required. Mixed PD/braid/grid/Montesinos
sources, extra source fields, empty continued fractions, booleans, floats,
infinite final slopes and multi-component closures are rejected.

For primitive slopes `p_i/q_i` with positive denominators, integer parts are
absorbed into `e`, leaving `0 < beta_i < alpha_i` for each nonintegral summand.
If `r` is the number of these summands, the exact determinant is

```text
abs(e' * product(alpha_i) + sum_i beta_i * product_{j != i}(alpha_j)).
```

The numerator is **not reduced across different summands**. For example,
`1/2 + 1/2` reduces as a number to one, but this tangle closure has determinant
four and is a link. Collapsing the sum to one reduced fraction would invalidate
the recognition criterion. For a knot with `r <= 2`, determinant one is
equivalent to the unknot. For `r >= 3`, the orbifold group quotient of the
branched-cover group proves nontriviality, including determinant-one examples
such as `Diagram.from_rational(-1, [[0, 2], [0, 3], [0, 5]])`.

## Compressed arithmetic and the PD expansion boundary

The direct API performs arithmetic without constructing crossing objects:

```python
from fastunknot import montesinos_certificate, verify_montesinos_certificate

coefficient = (1 << 20000) + 1
source = [[0, coefficient]]
witness = montesinos_certificate(0, source)
assert witness["status"] == "UNKNOT"
assert verify_montesinos_certificate(0, source, witness)
```

Here a 20,001-bit coefficient describes an exponentially long twist region.
Certificate integers larger than 1,024 bits use exact hexadecimal records, so
JSON serialization avoids Python's decimal-digit conversion limit. The
certificate includes the exact expanded crossing tally and arithmetic sizes.
The verifier evaluates the continued fractions using forward matrices and
recomputes the determinant using a denominator-product sum, independently of
the production recurrences. It checks the cited sufficient conditions; it is
not a formal verification of the topological theorems.

`Diagram.from_rational` instead constructs every crossing. Its default
`max_crossings=100000` limit is checked before crossing allocation; pass an
explicit larger limit or `None` to request a larger expansion. The ordinary
CLI reads a Diagram and uses this cap. Huge compressed inputs belong in the
direct `montesinos_certificate` API; the CLI does not silently change to a
different compressed input/output mode.

## Strict source provenance

The constructor realizes actual boundary twists, reciprocals, horizontal
gluing and numerator caps, then validates the resulting PD and records an
immutable `rational_source`. An unrelated PD plus a claimed slope or source
does not authorize this decision. Ordinary `Diagram.from_pd` does not attach
provenance, even when its PD equals a sourced diagram.

`diagram.to_json(preserve_rational=True)` retains the source explicitly;
default JSON output remains PD. Mirrors retain the mirrored source. Pickle
loading reconstructs the supplied source and requires its PD to match, up to
the choice of starting under-port in each row. Reinitializing an existing
Diagram is rejected. These safeguards define the public immutable-record
contract; they do not claim to defend against arbitrary hostile Python code
mutating `__dict__` or calling `object.__setattr__`.

## Opt-in local obstruction in an arbitrary PD

`fastunknot.tangle_obstruction` checks an actual connected four-port disk
subdiagram against a generated Montesinos pattern. It verifies crossing
slots, internal edges, an injective crossing map, four actual cut edges,
boundary order and exactly two open strings. A graph cut or a supplied
fraction by itself is insufficient. A successful check proves `KNOTTED`;
failure to find a pattern is inconclusive and the wrapper continues ordinary
recognition.

```python
import json
from pathlib import Path
from fastunknot import Diagram
from fastunknot.tangle_obstruction import (
    recognize_with_subtangles, verify_subtangle_certificate,
)

diagram = Diagram.from_json(json.loads(
    Path("examples/conway_double_three.json").read_text()))
result = recognize_with_subtangles(diagram)
assert (result.status, result.method) == ("KNOTTED", "montesinos-subtangle")

certificate = json.loads(
    Path("certificates/conway_double_three_certificate.json").read_text())
assert verify_subtangle_certificate(diagram, certificate)["status"] == "KNOTTED"
```

The default six-pattern catalogue is intentionally small. Custom patterns
use records such as `{"e":0,"tangles":[[0,-3],[0,5],[0,7]]}`:

```python
from fastunknot.tangle_obstruction import find_subtangle_obstruction

diagram = Diagram.from_json(json.loads(
    Path("examples/conway_forbidden_pretzel.json").read_text()))
pattern = {"e": 0, "tangles": [[0, -3], [0, 5], [0, 7]]}
certificate, evidence, stats = find_subtangle_obstruction(diagram, [pattern])
assert evidence["status"] == "KNOTTED"
```

Current patterns require `e=0`, at least two nonintegral finite summands, a
connected crossing shadow, four distinct boundary labels and no closed tangle
components. They must satisfy the imported non-embeddability criterion;
invalid or inapplicable supplied patterns raise `PatternError`. For each
fixed `k`-crossing pattern, its rooted rotation-system map propagates through
the internal edges in `O(n*k)` word operations over an `n`-crossing input.
The pattern is an exact diagram pattern: general tangle isotopy or arbitrary
rational-decomposition discovery is outside this search.

Local search is not enabled in default `recognize`. Benchmarks include
regressions when existing Seifert or invariant filters already decide the
input cheaply, so the explicit wrapper preserves the user's control over this
cost. `recognize_with_subtangles(..., seconds=...)` shares the remaining
cooperative time budget with the inherited recognizer and returns `UNKNOWN`
on exhaustion.

## Validation and integration

The maintained suite has 411 test methods, including 12 arithmetic/construction,
six local-pattern and two additional resource/option regression tests. The new tests include
independent Khovanov cubes, exact Alexander comparisons, large binary inputs,
the continuation identity family, determinant-one nontrivial knots,
provenance and certificate tampering, reordered crossings and local-search
controls. All required local examples and certificates are under this `fast/`
directory; the tests do not depend on report or experiment directories.

```bash
python -m unittest discover -s tests -p test_rational.py -v
python -m unittest discover -s tests -p test_tangle_obstruction.py -v
python -m unittest discover -s tests -v
```

The delivered report 22 retains its exact baseline patch and archive evidence.
Maintained audits and paired benchmark drivers are in `rational_research/`;
the current theory and interpretation are in `../synthesis/rational.tex`. Performance
claims distinguish recognition time from diagram construction, retain failed
baseline runs as censored entries and make no universal quasi-polynomial
claim.
