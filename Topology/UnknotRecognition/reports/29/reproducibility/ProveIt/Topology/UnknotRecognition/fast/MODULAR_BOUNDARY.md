# Modular boundary response backend

This optional backend reuses the suffix's checked cut-face Tait graph and evaluates completed integer Euler vectors modulo validated odd primes. The Khovanov complex itself remains over **F₂**. It extends the existing marked four-residue observer and the earlier rational boundary response prototype.

```bash
python -B -m fastunknot recognize examples/conway.json \
  --backend shadow-modular --shadow-primes 65521
```

The normal filters can decide an input before this backend is reached. The default backend remains `standard`. Raw scans on the seven recorded recognition examples were slower with the new observer, although repeated observations with large suffix interiors were substantially faster. See the article and `results/modular_benchmarks.json` for both results.

## What is guaranteed

- The matching must cover the actual frontier, preserve inherited checkerboard colors, and pass the spherical rotation-system check.
- With `b > 0` frontier darts, there are exactly `b/2` black open face fragments. Each potentially nonzero residual determinant has dimension at most `b - 2`.
- Every prime rebuilds its own singular-safe symmetric elimination. A singular interior is retained through radical directions; it is not confused with a zero quotient determinant.
- Integer four-vectors are aggregated across a **whole differential component before taking a norm**. CRT combines prime information; norms from separate primes are never added.
- The exact component Euler sum gives a minimum-norm integer lift. If the accumulated modulus exceeds every certified component coordinate bound, the threshold-one comparison agrees with the exact integer observer.
- A positive modular lower bound is deterministic. A small or zero residue is inconclusive. Only the complete rank-two unreduced scan can return `UNKNOT` on this path.

The default prime palette is `(65521,)`; the supported interface accepts distinct odd primes below `2**31`. A finite supplied palette may not certify threshold completeness. The recorded `modular_observation.threshold_exact` distinguishes a proved Boolean comparison from an incomplete negative observation. A positive obstruction makes the Boolean comparison certain even without reaching the modulus-size bound.

## Public Python entry points

```python
from fastunknot import Diagram, recognize

D = Diagram.from_braid(3, [1, 2] * 5)
result = recognize(D, backend="shadow-modular", shadow_primes=(3, 5, 7, 11, 13))
```

For a validated raw diagram and a fixed scan order:

```python
from fastunknot.modular_shadow import modular_shadow_khovanov_decide
from fastunknot.modular_verify import replay_modular_shadow

claim = modular_shadow_khovanov_decide(
    D.pd, order=list(range(10)), shadow_max_work=None,
    primes=(3, 5, 7, 11, 13))
assert claim["method"] == "marked-residue-four-modular"
assert claim["stage"] == 9
assert replay_modular_shadow(D.pd, claim)["verified"]
```

`replay_modular_shadow` accepts raw modular `KNOTTED` observations only. It reconstructs the prefix, checks component identity, recovered shifts, multiplicities, prime products, residues, exact sums, coordinate bounds, and the claimed minimum. It computes completion vectors with the old integer `ClosureShadow` and uses a separately coded minimum-norm formula. Invalid claims raise `ModularVerificationError`; resource exhaustion raises `ScanLimit`. The Boolean convenience wrapper `verify_modular_shadow` returns `False` for invalid claims and propagates resource exceptions.

Replay shares the maintained scanner and may be as expensive as the original prefix. It is **not** a short independent NP certificate or a formally verified scanner. Statistics and timing metadata are outside its authenticated scope.

## Resource behavior

The modular observer shares the existing completed-state allowance with the exact Euler reserve. Exhausting determinant work disables the modular path and retains Euler observations. Exhausting the observation-state allowance continues the capped scan. A geometric inherited-color decline also triggers fallback. Global time and object exhaustion become `UNKNOWN` through the public recognizer. Partially computed responses are never installed in caches, and cache hits still check the global deadline.

The active response is small, but the dense preparation, value caches, matching keys, and scanner objects also consume memory. No total `O(b²)` memory claim is made.

## Reproduction

From this `fast` directory:

```bash
python -B -m unittest discover -s tests -p 'test_modular_*.py' -v
python -B modular_research/demo.py --output results/modular_demo_rerun.json
python -B modular_research/audit.py --help
python -B modular_research/benchmark.py --help
```

The new tests comprise 31 cases. The actual-diagram audit checks 138 diagrams against independent reduced F₂ cubes, 868 proper prefixes, 15,096 modular vectors, and 50 replayed positive claims. Preserve the sibling archived reference packages used by the research drivers; production imports do not depend on them.

The benchmark uses five shuffled paired rounds, excluded warmups, identical integer controls, and fresh preparation inside each timing. Its 24,200 vector and 2,013 status comparisons count repeated validation events, not distinct inputs. All timed modular interiors are nonsingular; separate tests exercise singular cases.

The full maintained suite has a separately documented inherited optional-worker communication error on the recorded CPython 3.12.14 runtime. The new 31-test modular suite passes. Do not represent the broader suite as entirely green.

## Mathematical limit

This work bounds observation cost and the modulus needed to recover the existing Euler threshold. It does not bound the number of differential generators or the first decisive scan stage. General quasi-polynomial complexity for the maintained recognizer remains unproved. The next priorities are response scheduling, incremental geometry, singular-safe block decomposition, and continuation-compatible compressed complex representations.
