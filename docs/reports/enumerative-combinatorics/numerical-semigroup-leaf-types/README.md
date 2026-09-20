# Leaves of Large Type in the Numerical-Semigroup Tree

A genus-34 counterexample and a sharp asymptotic order. Prepared on 20 September 2026.

## Main results

The article disproves Conjecture 4.4 in:

Jonathan Chappelon, Jorge L. Ramírez Alfonsín, and Dumitru I. Stamate,
*Numerical semigroup tree: type-representation*, arXiv:2507.15006v2
(revised 22 November 2025).

The counterexample is

    S = {0, 26, 27, 29, 31, 32} union {39,...,50} union {52,53,...}.

Its multiplicity is 26, Frobenius number 51, genus 34, and type 17.
All 17 minimal generators are below the Frobenius number, so S is a leaf.
The conjecture would bound its type by 16.

The article gives complete elementary proofs of this example, two infinite
families, a general construction from restricted additive bases, and the theorem

    L(g) = (2/3) g - Theta(sqrt(g)),

where L(g) is the maximum type of a numerical-semigroup-tree leaf of genus g.
This statement concerns every sufficiently large integer genus, not merely a
subsequence. Explicit two-sided bounds hold for every g >= 7. The construction
also produces counterexamples to the original conjecture at every g >= 697.

The exact function L(g), the sharp square-root coefficient, and whether that
normalized coefficient converges are not determined here.

## Contents

- `article.tex`: self-contained LaTeX source, including all references.
- `article.pdf`: compiled 18-page article.
- `code/verify.py`: dependency-free, exact-arithmetic verifier.
- `code/search.py`: optional MILP discovery program; never needed for a proof.
- `data/counterexample.json`: complete finite counterexample certificate.
- `data/families.csv`: verified unpadded family examples.
- `data/restricted_bases.csv`: exhaustive restricted-basis counts for maxima 1–12.
- `data/tree_checks.csv`: exhaustive tree data through genus 20.
- `data/verification_report.json`: actual verification-run report.
- `data/discovery_search.jsonl`: historical optimizer results from discovery.
- `data/random_selection.json`: original seed, area list, and random draw.
- `data/research_status.json`: target version, source URLs, and scope of status claims.
- `requirements-search.txt`: optional search dependencies, pinned to the environment used.
- `build.sh`, `build.ps1`: article build helpers.

## Verify the mathematics computationally

From this directory, with Python 3.10 or later:

```sh
python code/verify.py --out data
```

No third-party package is needed. The archived verification run used Python 3.13.5.
The verifier checks the main example both from its finite-tail description and
from its generators, using a separate integer Dijkstra reconstruction of its
Apéry set. It also checks all pseudo-Frobenius sets, all claimed generator sets,
the family formulas, and the new upper bounds on the tested instances.

The default run checks 220 explicit family instances and 1,152 instances obtained
from all 384 restricted bases with maximum between 1 and 12. It independently
reconstructs 26 distinct examples via Dijkstra and enumerates all 93,141 semigroups
at genera 1–20, including 34,001 leaves. Finite data are additional checks; the
infinite assertions are proved in the article.

To extend the tree run:

```sh
python code/verify.py --out extended-data --tree-genus 24
```

The allowed tree range is 1–24. Increasing it uses more memory and time.
The code uses explicit checks rather than Python `assert` statements, so `-O`
does not disable certificate validation. Running verification into `data` changes
its report's timing and environment fields; use another output directory to
preserve all archived checksums.

## Reproduce the random area draw

```python
import json
import random
from pathlib import Path

record = json.loads(Path('data/random_selection.json').read_text())
index = random.Random(record['seed']).randrange(len(record['areas']))
print(index, record['areas'][index])  # 9 semigroup theory
```

The original seed came from `secrets.randbits(128)`. The recorded seed is
84421886621299946913970799425001841153. The area list was fixed before the draw.

## Optional discovery search

```sh
python -m pip install -r requirements-search.txt
python code/search.py --multiplicity 36 --frobenius 71 --seconds 15
```

The archived search used NumPy 2.3.5 and SciPy 1.17.0. Search optimizes a binary
model of a semigroup with fixed multiplicity and Frobenius number. A returned
candidate is checked exactly before being reported as valid. Numerical solver
optimality, reproducibility of a particular time-limited candidate, and the
historical solver log are not premises of any theorem.

The original discovery first found genus 48 and type 24. Analysis of the sumset
pattern yielded the genus-34 example and the infinite constructions. The main
counterexample is not claimed to be the unique or independently certified
smallest counterexample.

## Build the article

With a LaTeX distribution containing the packages named in `article.tex`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or run `pdflatex article.tex` twice. No BibTeX/Biber step or external graphic is
needed. The provided helpers build in `.build` and copy the final PDF to the
package root:

```sh
bash build.sh
```

On PowerShell:

```powershell
./build.ps1
```

## Scope and status

The retrieved arXiv v2 states the target conjecture. A targeted search on
20 September 2026 did not locate a later resolution. This is not a proof of
priority or an exhaustive literature review. The note and its proofs have not
been independently refereed or formalized in a proof assistant.

The counterexample is supported by a direct elementary proof and two exact
computational descriptions. Our own exhaustive genus run ends at 20. The source
paper reports tables through 33, but those tables were not independently
recomputed here; do not interpret genus 34 as an independently proved global
minimum. No claim is made to settle the source paper's other conjectures or its
separate question about the proportion of semigroups that are leaves.
