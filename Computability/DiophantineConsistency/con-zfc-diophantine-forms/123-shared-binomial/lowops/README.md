# Eleven-integer product equations

The single polynomial is `delta*Z^2 - S^2*P*Df*Cy`, with every abbreviation
and fixed coefficient binding supplied in the literal DAG and `PROOF.md`.

| Equation | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `product11_degree966.json` | all integers | 11 | 966 | 111 |
| `product11_degree882.json` | all integers | 11 | 882 | 112 |

The first uses the original index modulus `XY`; the second uses `4q^4`.
The arithmetic proof composes with the same retained source34/native and
finite-refutation calibration. No new complete Lean/Rocq or object-ZFC
certificate is asserted. The new zero-existence reductions are ordinary
mathematical proofs; the finite checks certify polynomial artifacts,
coefficient bindings, exact degrees, arithmetic counts, and identities.

## Reproduce

Python 3.10 or newer and its standard library suffice. From any directory:

```
python3 -B /path/to/lowops/build.py --check
python3 -B /path/to/lowops/check.py
python3 -B -O /path/to/lowops/build.py --check
python3 -B -O /path/to/lowops/check.py
```

The producer writes its two outputs and `METRICS.json` when `--check` is
omitted. The independent checker does not import the producer. It uses
the small exact sparse polynomial module `exact_poly.py` and rejects ten
mathematical corruption controls, five in each actual graph.

The coefficient path is `../norm/coefficients/BINDING.json`; the entire
unchanged six-port tuple and its finite reconstruction recipe are shared
there. Retained mathematical dependencies are under `../norm/source/`.
Keep those sibling directories when moving this component. All paths are
relative; no network access or development checkout is required.

`SOURCE_PINS.json` identifies the six immediate source texts by complete
SHA-256 digests. `CHECK.json` and `CHECK_OPTIMIZED.json` record the exact
artifact checks. `section.tex` is the report section; `PROOF.md` gives the
full standalone arithmetic argument and dependency order. The companion
independent mathematical review is retained by the overall release.

## Format

Each DAG node is a variable leaf, fixed-coefficient leaf, literal integer
leaf, or binary `add`, `sub`, or `mul` operation on earlier node indices.
`output` identifies the complete polynomial. All eleven variables range
independently over unrestricted integers. `named_registers` supplies
readable aliases but creates no extra quantified variables.
