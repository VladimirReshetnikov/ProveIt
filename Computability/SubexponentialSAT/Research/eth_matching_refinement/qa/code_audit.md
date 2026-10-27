# Independent component-code audit

Date: 27 October 2026 (UTC).

## Result and scope

**PASS on the final audited files:** the six supplied test methods and seven additional independent test methods pass both normally and under `python -O`.

This is a source audit and finite executable validation of exact component routines. It is **not** execution or verification of a complete SAT solver, a proof-assistant verification, a runtime comparison, or independent validation of the full inherited contraction interface or the report's asymptotic theorem. No external publication or repository modification was performed by this audit. The audit added only files in `qa/`; the author applied the contained helper correction below.

## Finding corrected during audit

The initial `log_interval_positive(2, 32)` accepted a Python integer but computed `(x-1)/(x+1)` as a float. Its purported lower and upper endpoints both became `0.6931471805599451`; converting the upper endpoint back to `Fraction` put it **below** the certified lower endpoint from `log_interval_positive(Fraction(2), 64)`. Thus the helper's integer-input route did not produce its advertised exact interval.

`exact_budget` itself was unaffected: it already passed exact `Fraction` arguments. The final helper normalizes integers and fractions to `Fraction`, rejects floating inputs, and validates a positive integer term count. The author also added positive-integer validation for `exact_budget`'s lambda and divisor; previously a zero divisor raised `ZeroDivisionError` and a negative divisor could return a negative budget. The original suite now includes the relevant regression/negative controls, and the independent suite checks the integer-input interval against a strictly finer certified rational interval.

No further component-correctness defect was found for the intended exact-integer parameters and finite lists of endpoint pairs.

## Formula and implementation checks

- **Multigraph coloring:** endpoints on the two sides remain distinct types. Parallel edges are preserved and separated into matching classes. The greedy coloring uses at most `2*Delta - 1` nonempty classes. The implementation uses its actual class count rather than the report's conservative `c=2*Delta`; this is a valid sharper instance of the same potential argument.
- **Packing threshold:** `tau = ceil(log2(8*c*labels**2))` is computed by integer bit length. Since `2*lambda*tau` is integral, the implemented threshold is exactly the ceiling of `(1+1/lambda)*m_k/D + 2*lambda*tau`.
- **Conditional expectation:** the exact `Fraction` product matches direct enumeration of all completions of partial assignments. Conditional averaging is an explicit checked equality, not a Python `assert`. The next label is the smallest label attaining the minimum potential.
- **Budget:** `ln(54) = 6*ln(2) - ln(32/27)` and the positive atanh-tail bounds give valid enclosing ratio intervals. Returning only when both endpoint floors agree certifies the integer budget. Positive integer lambda/divisor avoid an exact positive equality between powers of 54 and 2.
- **Schedule:** `r=54`, the `18` depth base, taper denominator `9`, `g=6*ceil(log2(lambda))`, and the deduction `(depth+1)*g+k**2` agree with the stated schedule. For nonpositive `U`, the prototype clamps the taper to zero and returns a false `basic_guard`; those values are diagnostics, not an admissible recursive schedule. `basic_guard` is not the collection of all guards required by a complete contraction implementation.
- **Precision:** the supplied closed-form loss agrees with an independently evaluated rational loss sum; the returned multiplier `h` is the least integer giving more interpolation conditions than degree. This audit does not check the inherited Hermite recovery theorem itself.
- **Mode count:** `1+3*b-2*popcount(b)` agrees with `1+b+2*v_2(b!)`. The count uses the strict bound `weight < precision`. Independent truncated generating-polynomial multiplication agrees, including zero colors and precision one.

## Additional executed coverage

| Check | Cases |
|---|---:|
| Exhaustive 2-by-3 bipartite multigraphs, edge multiplicities 0 through 3 | 4,096 |
| Partial-assignment potentials checked by enumerating all completions | 1,011 |
| Nonvacuous packing examples, with every threshold at most its matching size | 6 |
| Explicit smallest-minimizing-label checks on those examples | 432 |
| Empty graph or single-label boundary cases | 3 |
| Exact budget threshold crossings, divisors 1, 7, 20, 53 | 800 |
| Schedule boundaries and root constants 1, 2, 7, 100 | 164 |
| Independent precision parameter combinations | 1,584 |
| Independent exact precision-loss rows | 9,744 |
| Generating-polynomial mode counts, precision 1 through 35, colors 0 through 3 | 140 |
| Integer-log helper regression | 1 |

The six nonvacuous packing cases supplement the supplied small-graph cases, whose large thresholds alone do not force balanced loads. They include disjoint matchings, duplicate parallel-edge matchings, and matchings with shared vertices across classes.

## Replay and records

From the package root:

```sh
python code/verify.py qa/audit-normal.json
python -O code/verify.py qa/audit-optimized.json
python qa/independent_code_checks.py qa/independent-normal.json
python -O qa/independent_code_checks.py qa/independent-optimized.json
```

All four executions completed with exit status zero. Matching `.log` records contain the individual method outcomes. The independent suite uses `unittest` assertion methods, which remain active with optimization enabled.

Audited SHA-256 digests:

```text
05278d34e890d06dba42e4283971ccce4f64a093dd4dfe6846506a587c28ad34  code/refinement.py
197eceeef3b127e4871506b60aa531d6169b50b80659bb1240ae987f738606e0  code/verify.py
81006f065154ea2890dcfaa0dfacfc64984f6b8ca964c1164d8c3b720e941bc9  qa/independent_code_checks.py
```
