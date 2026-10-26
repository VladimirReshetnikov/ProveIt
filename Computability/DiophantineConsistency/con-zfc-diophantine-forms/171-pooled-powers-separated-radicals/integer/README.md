# Strict-frame pooling: direct Con(ZFC) quartics in 217 integers

The principal fixed polynomial is `integer217/equation.json`: the sum of
squares of **154 explicit quadratic residuals in 217 independently
unrestricted integers**, exact degree4. Every collected coefficient is in
`expanded_polynomial.json`. Its height is **4576**.

| Profile | Variables | Rows | Collected terms | Height |
|---|---:|---:|---:|---:|
| `integer217` | 217 | 154 | 25949 | 4576 |
| `integer217_sparse` | 217 | 154 | 14615 | 16866 |
| `integer218` | 218 | 155 | 15631 | 4576 |
| `integer218_sparse` | 218 | 155 | 8817 | 16866 |

Each residual coefficient has magnitude<=64. These four are achieved
tradeoffs, not global optima. The ordinary theorem, using the retained
C222/ZF/ZFC calibration, is that each polynomial's integer nonsolvability is
ZFC-provably equivalent to Con(ZFC). No proof of consistency is claimed.

The advance is a **new compatible composition**, not a new claim to incoming
lemmas: Strict Horizons' factorial-free/mod-four source, Pooled Powers'
two-row blocks and Pell differences, Quadratic Projection234's integral
radical maps, and Linear CRT's odd-linear beta idea. Our full proof checks
their compatibility, notably the unchanged 34-atom frame and a noncircular
signed-beta bootstrap. Each matched235/236-coordinate source loses18
variables and18 rows. The other incoming225-coordinate pooled-power branch
has lower support but coefficient height128446; no branch is misrepresented
as globally best.

## Read and reproduce

- `PROOF.md`: complete changed arithmetic, both directions and boundaries.
- `report_section.tex`: article-ready statement and proof.
- `sources/`: pinned strict parents and explicit frame identities.
- `credited/`: original component proofs and notices.
- `inherited/`: unchanged Strict Horizons archive with its proof closure.
- Each endpoint has a literal equation, full expansion, readable residuals,
  variable table, metrics, and frozen row certificate.

Python3, standard library, offline:

```sh
python3 -B verify_all.py
python3 -B -O verify_all.py
# Also recheck/rebuild the retained arithmetic parent:
python3 -B verify_all.py --parent
# Reconstruct every stage in a separate directory, without optimization:
python3 -B build.py --out /tmp/conzfc217-rebuilt
```

The verification commands are read-only unless an explicit `--receipt` path
is supplied. They create disposable reconstruction directories. Deliberate
corruptions must fail. No numerical zero search or proof-assistant closure
is claimed. The semantic pooling/beta changes preserve zero existence;
only the subsequent exact coordinate/row maps assert zero-set bijections.

No publication, remote write, or repository commit is part of this package.
