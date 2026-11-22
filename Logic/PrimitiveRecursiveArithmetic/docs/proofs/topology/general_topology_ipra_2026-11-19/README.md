# General topology in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 19 November 2026.

Start with **`general_topology_ipra.pdf`** (55 pages). The editable master is
`paper/main.tex`; it includes all nine chapters and the bibliography. No
network access is needed to read or rebuild the mathematical content.

## What this package establishes

The report develops **83 numbered human-readable results and supporting
lemmas**: 2 arithmetic proof rules, 24 finite-topology results, 17 metric
results, 20 finite algebraic/sheaf results, 6 dimension results, 8 sphere
results, and 6 additional finite replacements or obstruction results.
These are not 83 distinct theorems quoted from MathWorld. The scope ledger
covers all **33 direct entries** of the General Topology index and records
which assertions are treated and which remain outside the package.

The principal constructions include finite topology from preorders,
constructive finite separation and extension, exact finite compact-open
exponentials, quantitative metric products and Urysohn separation,
equipped Hilbert-cube embeddings, rational finite homology and gluing,
a rational-grid dimension obstruction, and approximate hairy-ball
theorems with explicit bounded searches.

The arithmetic discipline is first-order intuitionistic primitive recursive
arithmetic with quantifier-free induction. Infinite presentations are
fixed primitive-recursive schemas, finite tables, or bounded computation
traces. Every use of a modulus, a locator, a positive separation bound,
completion data, or a geometric certificate is stated as an assumption.
The report explains why arbitrary higher-type objects and an unrestricted
universal evaluator cannot silently be introduced.

## Exact formalization status

All five Lean files compile with **Lean 4.32.0**, using only `Init`/`Std`.
They contain **43 proved theorem declarations**, and every one has a
recorded `#print axioms` audit. There are no admitted proofs or user-declared
axioms. No audited theorem uses `Classical.choice` or `sorryAx`. Some
semantic proofs use Lean's ordinary `propext` or `Quot.sound`; the logs say
exactly which dependencies occur. The 24 finite-topology theorems have
empty axiom lists.

| Module | Proved Lean theorems | Role |
| --- | ---: | --- |
| `FiniteTopology.lean` | 24 | Preorder opens, interior/closure, continuity, products and map identities |
| `MetricBlueprint.lean` | 4 | Uniform composition, image-net cover and limit uniqueness |
| `AlgebraicBlueprint.lean` | 7 | Chain-homotopy algebra, Euler telescoping and function gluing |
| `DimensionBlueprint.lean` | 0 | Definitions and explicit dimension proof obligations |
| `SphereBlueprint.lean` | 8 | Sign/parity and the terminal antipodal-chain contradiction |

**This is not a completed object-language `Prf PRAAx` formalization of the
collection.** A Lean definition whose name ends in `Target` states a
remaining obligation; it is not a proof. Chapter 9 gives the definitions,
target numerical sentences, invariants, and a seven-stage completion route
through the inspected ProveIt interfaces. The full dimension and approximate
hairy-ball arguments are proved in the report, with their remaining Lean
work explicitly identified. Python checks are finite regression evidence,
not universal mathematical proofs or proof-assistant certificates.

## Files

- `general_topology_ipra.pdf`: complete human-readable report.
- `paper/`: LaTeX sources, bibliography, and the finite-normality figure.
- `lean/`: five standalone Lean modules and the compilation/audit script.
- `lean-toolchain`: the toolchain pin at package root for elan.
- `code/`: exact-arithmetic Python reference implementations and checks.
- `data/source_map.csv` and `.json`: all 33 direct source entries, with
  proved scope and residual claims.
- `data/theorem_ledger.csv`: all 83 numbered results and their status.
- `sources/repository_manifest.json`: pinned ProveIt files and provenance.
- `validation/`: exact check results, all final Lean audits, LaTeX logs,
  and the final verification summary.
- `SHA256SUMS.txt`: integrity checksums for the packaged files.

## Reproduce the checks

Run these commands from the extracted package directory:

```sh
sha256sum -c SHA256SUMS.txt
python3 code/run_checks.py
bash lean/check.sh
bash build.sh
```

Requirements:

- **Python 3.10 or later** for the checkers (recorded run: Python 3.12.14).
  They use only the standard library and exact integers/fractions.
- **Lean 4.32.0**, either selected by elan using the root `lean-toolchain`
  or supplied explicitly as `LEAN_BIN=/absolute/path/to/lean bash lean/check.sh`.
  The standalone modules need no Mathlib download and no ProveIt checkout.
- A full **LaTeX** installation with `pdflatex`, Latin Modern, AMS packages,
  `microtype`, `geometry`, `booktabs`, `longtable`, `enumitem`, `xcolor`,
  `graphicx`, `fancyhdr`, `needspace`, `xurl`, `hyperref`, and `bookmark`.
- **Matplotlib** only if regenerating the included figure with
  `python3 code/make_figures.py`; it is not needed to compile the report.

Check the supplied checksums before rebuilding: regenerated logs and PDF
metadata can differ even when the mathematical checks pass. The source
audit can also be rerun independently with `python3 code/audit_sources.py`
after the Lean check. It verifies source declarations and audits, counts
theorem statements, and regenerates the theorem ledger.

The recorded tests include all 390 labeled preorders of sizes 0 through 4;
92,805 closure/interior pairs; 167 finite simplicial complexes; 5,103 prism
identities; 5,223 exhaustive admissible cubical colorings; 625 exhaustive
rational dimension tables; 358 subdivision certificates; and 308 tangent
field samples. Each JSON report specifies its exact scope and bounds.

## Reuse and source baseline

MathWorld index: <https://mathworld.wolfram.com/topics/GeneralTopology.html>.

ProveIt baseline:
`eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98` in
<https://github.com/VladimirReshetnikov/ProveIt>.

The dimension argument is reconstructed from the repository's dimension
packet and reviewed in the report. Its `finite_dimension.py`, `validate.py`,
example input and example certificate are copied from that pinned source;
their Git blob hashes are recorded in the manifest. The other Lean and
reference-checker files are supplied with this report. A complete build of
the upstream ProveIt repository was not performed, and no upstream files
were modified.

## Deliberate limits

The source map is an audit, not a claim that every assertion on every linked
page has been proved. General current compactness, the general disk-production
step in Dehn's lemma, surface classification, the four-color theorem,
unrestricted Tychonoff, arbitrary-cover compactness, and a general exact
zero selector remain outside the delivered proof collection. Where a
weaker result is given, its extra data and precise conclusion are stated.

