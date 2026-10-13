# Projective Port Atlases for Normal-Surface Discovery

Research continuation for Vladimir Reshetnikov's **ProveIt** project, 12 October 2026.

Read **`article/article.pdf`** for the complete mathematical article. The editable
sources are under `article/`; `Projective_Port_Atlases.tex` is an additional
standalone, inlined source. This is an additive research delivery, not a native
recognizer replacement, and it has no assigned report number.

## Main result

For compatible nonnegative matching cones sharing the **same d-coordinate port**,
a finite projective atlas decides every linear positive-objective query. The atlas
is independent of the objective and remains complete under all coordinate-zero
restrictions. For two ports it consists only of local normalized ray slopes;
three or more ports may require new domain-intersection points.

The complete direct cost after local ray preparation is
`poly(input_bits, d) * (R+d+1)**(d*d-d+1)`, where `R` is the total local ray count.
Two complete local producers are included: support enumeration and a
nullity-sensitive zero-set method. The latter handles large low-nullity blocks.
The article states exact quasi-polynomial parameter regimes, without asserting
that every knot exterior admits them.

Source compilers retain the original equations and incompatibilities. A primitive
assembled vector need not be a source ray; the included support descent repairs
this and an independent checker verifies its result. Connectedness follows only
when the source is authenticated standard normal coordinates. Essential boundary,
knot-diagram ancestry, and the global hierarchy accounting are separate.

## Evidence

The delivery contains **46 passing unit-test methods**, 960 seeded global-oracle
queries, 480 independent local ray-list checks (both producers), 814 exact
normalized-optimum comparisons, and 1,173 positive/tamper checks. A repository
face-pairing fixture adds 104 source queries and 24 variable-compiler comparisons.
All 64 deliberately nonextreme assemblies are successfully reduced and checked.

Seven paired source-query trials have medians of **402.745 ms unsplit** and
**19.751 ms split**: about **20.39x** against the delivered unsplit support
enumerator. The workload includes matching and Euler construction, preparation,
eight anchored queries, source witnesses, independent positive checks and
serialization. It excludes a trivial zero-port disc shortcut and includes two
negative queries. It is not a native whole-knot benchmark.

The algebraic synchronized-mode benchmark replaces 65,536 mode histories at 16
blocks by four atlas points, with a 166.35x preparation-plus-query ratio in the
frozen run. Small-input regressions are retained: the one- and two-block examples
are substantially slower with general atlas preparation. Raw samples and scopes
are in `evidence/`; no recognition speedup is extrapolated from these numbers.

## Run

Python 3.10 or later, no third-party Python dependencies:

```bash
python -m unittest discover -s tests -v
python integration/source_query.py
python experiments/reproduce.py all --out evidence-new
```

To reproduce the frozen trial counts specifically:

```bash
python experiments/reproduce.py audit --models 120 --out evidence-new
python experiments/reproduce.py normal --out evidence-new
python experiments/reproduce.py descent --out evidence-new
python experiments/reproduce.py modes --trials 5 --max-m 16 --out evidence-new
python experiments/reproduce.py timing --trials 7 --out evidence-new
```

Fresh runs go to a separate destination; delivered evidence is unchanged.
Measured milliseconds naturally vary with hardware and load.

A source-bound example:

```python
from projective_ports import Prepared
from projective_ports.fixtures import capped_solid_torus, matching, euler
from projective_ports.source import compile_two_block, extreme_witness
from projective_ports.verify import verify_vector

tri = capped_solid_torus()
source, objective = matching(tri), euler(tri)
compiled = compile_two_block(source, range(7))
prepared = Prepared(compiled.blocks)
costs, master, zeros = compiled.query(objective, zeros=(10, 2))
answer = prepared.solve(costs, master=master, zeros=zeros)
assert answer['status'] == 'POSITIVE'
witness = extreme_witness(source, compiled.reconstruct(answer['vectors']), objective)
assert verify_vector(source.n, source.equations, source.conflicts, objective,
                     witness['coordinates'], zeros=(10, 2), extreme=True)
print(witness['coordinates'])
# (1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0)
```

Use `Prepared(..., ray_method='zeros')` for the complete nullity-sensitive
producer. Keep a prepared object for repeated objectives/zero faces. Resource
budgets raise `ResourceLimit`, never a complete negative answer. The example
adapter maps such exceptions to `INCONCLUSIVE`.

## Build the article

The PDF is already compiled. With standard TeX Live packages:

```bash
python experiments/build_tables.py
cd article
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`build.sh` runs the tests, refreshes the standalone source, and compiles with three
LaTeX passes. Tables read frozen evidence, not fresh timings.
`Projective_Port_Atlases.tex` can also be compiled independently. To regenerate it
after editing the modular article, run `python experiments/inline_article.py`.

## Integration and audit

Read `INTEGRATION.md`, `CLAIMS.md`, and `SOURCE_AUDIT.md`. The reference revision is
`74de08949619863b002b5fcf01813a2faddde212`. The review was targeted, not a full native
checkout audit. Four binary incoming archives were inventoried but could not be
decoded through the available retrieval routes. Their overlap has not been
exhaustively checked. No repository defaults, original files or incoming archives
were changed.

The article also proves a bounded-degree obstruction to a naive logarithmic
raw-tetrahedron master strategy. Its positive parameter claims must not be
advertised as a universal small-separator theorem for connected triangulations.
