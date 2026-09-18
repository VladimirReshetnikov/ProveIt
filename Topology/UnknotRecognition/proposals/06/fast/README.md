# fastunknot 0.2.0 — accelerated exact recognition

A standard-library-only Python implementation for classical **one-component**
knot diagrams. It accepts the same planar-diagram, braid and grid JSON formats
as the supplied `fast/` implementation. Python 3.10 or newer is required; this
release was tested on CPython 3.13.5.

The default pipeline is:

```
validated diagram -> decreasing R1/R2 -> descending-diagram test
                  -> Alexander obstruction -> bounded modular Jones obstruction
                  -> exact, optionally factored F2 Khovanov scan
```

Every completed verdict is exact. Neither an Alexander polynomial equal to 1
nor a modular Jones value equal to 1 is an unknot certificate. Limits can produce
`UNKNOWN`, never a guessed verdict.

**There is no general quasi-polynomial guarantee.** The complete fallback remains
exponential in the worst case. Visible connected sums are computed factorwise:
if every visible factor has at most `b` crossings, the cost is polynomial
preprocessing plus `n * 2^O(b)`. This is a restricted input-class bound, not a
bound for arbitrary diagrams. A small scan boundary alone does not bound the
number of retained chain generators.

## Run without installation

Run these commands from this `fast/` directory:

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot khovanov examples/kinoshita_terasaka.json
python -m fastunknot jones examples/trefoil.json
python -m unittest discover -s tests -v
```

Or install from this directory with `python -m pip install .`, then use the
`fastunknot` command. No third-party runtime packages are required.

Input examples:

```json
{"braid": {"strands": 2, "word": [1, 1, 1]}}
```

```json
{"pd": [[0, 3, 1, 4], [2, 5, 3, 0], [4, 1, 5, 2]]}
```

A crossing row is cyclically counterclockwise, under-strand at positions 0 and 2,
over-strand at 1 and 3. Edge labels may be arbitrary integers; they are normalized.
An empty PD is one crossing-free unknot, not an empty link. Use `-` for stdin.
Grid inputs use `{"grid": [[a,b], ...]}` with rows ordered bottom to top.

## Controls

```sh
# Force the exact backend; no shortcut from the polynomial obstructions.
python -m fastunknot recognize examples/conway.json --no-alexander --no-jones

# Cooperative 30-second deadline and generator ceiling.
python -m fastunknot recognize examples/conway.json --seconds 30 --max-objects 100000

# Trade higher transient memory for fewer expensive categorical cancellations.
python -m fastunknot khovanov examples/conway.json --tail-crossings 3

# Validate differentials, disable factorization, and use the default two-crossing tail.
python -m fastunknot khovanov examples/trefoil.json --check-d2 --no-decompose
```

`--tail-crossings 2` is the default. The last two crossings are not separated by
categorical Gaussian elimination: the penultimate stage is retained, and the
closed differential is handled by packed F2 linear algebra. `1` reduces every
nonclosed intermediate stage. Larger values may be faster but can greatly
increase transient memory. A requested object ceiling can therefore be reached
sooner than with the original elimination schedule.

The Jones filter defaults to at most 4096 frontier states. `--jones-max-states B`
changes that cap. Overflow **skips only the filter**, then runs the complete
fallback. `--no-jones` disables it. `--no-reduction`, `--no-descending`,
`--no-alexander` and `--no-decompose` control the other stages.

CLI exits: 0 for a completed result, 2 for invalid input, 3 for a resource limit
(or an inconclusive standalone `jones` state cap), 4 for an internal arithmetic
error. An exit code of 0 from standalone `jones` means an evaluation completed;
its value 1 is not a recognition result. Inspect JSON `status` from `recognize`.

## Python API

```python
from fastunknot import Diagram, khovanov_rank, recognize

d = Diagram.from_braid(3, [1, 2] * 5)
verdict = recognize(d, seconds=30)
assert verdict.status in {"UNKNOT", "KNOTTED", "UNKNOWN"}

kh = khovanov_rank(d.pd, tail_crossings=2, check_d_squared=True)
print(kh["reduced_rank"], kh["by_degree"])
```

`khovanov_rank` does **not** simplify the diagram. `by_degree` is the original
unnormalized cube degree, summed over quantum degrees. It is not integral
homology and does not compute torsion or a quantum grading. For knots over F2,
unreduced dimensions in every homological degree are twice reduced dimensions.
When a factorization is used, `order` is empty and `factor_results` contains
local orders; `decomposition` contains a replayable splitting tree.
An explicit `order=` must be a permutation of all crossings and bypasses
factorization, so that the requested crossing identifiers are honored.

```python
from fastunknot import connected_sum_factors, verify_decomposition
factors, certificate = connected_sum_factors(d)
assert verify_decomposition(d, certificate) == factors
```

These certificates verify visible connected-sum cuts, not all the homology
arithmetic. No prime-decomposition or isotopy search is claimed.

## What changed

- Frozen, bounded, stage-local memoization of crossing maps, composition plans
  and surface coefficients; identity and endomorphism fast paths.
- In F2 dual-number endomorphism rings every unit is its own inverse.
- Bit-packed scalar elimination at an empty boundary; final homology is stored
  as dimensions rather than separate indistinguishable generators.
- A configurable deferred tail before closure.
- Certified visible connected-sum factorization and reuse of identical factors.
- A bounded exact modular Jones obstruction at A=2 modulo 1,000,000,007.
- Correct writhe for arbitrary valid PD row orientations; matching Alexander
  arc-direction adjustment, full explicit-order validation, cooperative limits.

`reference_algebra.py` retains the original surface formulas as a test oracle.
It shares geometry helpers with the optimized implementation and is therefore
not a fully independent implementation. The tests also include independent
full smoothing-cube Jones evaluation and the original dense reduced-Khovanov
cube oracle on small diagrams.

## Limits and reproducibility

`--seconds` is cooperative, not an OS-enforced wall-time guarantee. A single
large integer/polynomial operation, sorting, or allocation can overrun it.
`--max-objects` is a generator-count ceiling, **not** a byte-accurate RAM cap.
Boundary caches have bounded entry counts, not fixed byte sizes. Use a separate
process with OS limits for hostile or very large inputs.

The top-level `docs/report.pdf` and `docs/report.tex` give the correctness and
complexity arguments and benchmark limitations. `tools/benchmark.py` compares
against the untouched `baseline/fast/` in fresh sequential processes. All current
results, complete inputs and test logs are in the top-level `results/` directory.
The original `benchmark.py` is retained for compatibility; the new top-level
benchmark driver is the one used in the report.
