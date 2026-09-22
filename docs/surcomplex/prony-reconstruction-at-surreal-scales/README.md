# Sharp Moment Reconstruction at Surreal Scales

**Collision geometry, optimal precision, and Hahn-supported inversion**  
Research manuscript prepared with ChatGPT — 22 September 2026

## Contents

- `article.pdf`: the 22-page typeset research manuscript.
- `article.tex`: standalone LaTeX source, including its bibliography.
- `code/verify.py`: exact finite symbolic checks and worked examples.
- `data/verification.txt`: the successful verification output from this delivery.
- `data/build_summary.txt`: compilation and verification scope.
- `requirements.txt`: the tested Python dependency version.
- `SHA256SUMS.txt`: SHA-256 hashes of the other delivered files.

No external figures, bibliography databases, or bundled font files are needed.

## Main mathematical content

The manuscript studies recovery of distinct integral nodes a_i and nonzero
weights w_i from their first 2n power moments in a real or complex Hahn field
k((t^Gamma)), for an arbitrary nontrivial ordered abelian value group Gamma.
Set d_i = sum_{j != i} v(a_i-a_j), r_i = max_{j != i} v(a_i-a_j), and
alpha_i = v(w_i). The main theorem gives the exact uniform precision threshold

    Theta = max_i (alpha_i + 2 d_i + r_i).

Moment errors of valuation at least kappa > Theta admit a unique regular
n-node realization, uniquely labelled by strict nearest-neighbour balls.
The theorem gives separate node and weight error estimates, and proves
sharpness by changing only the last moment. Its statement includes the
n = 1 conventions. Finite surreal and surcomplex data are handled through
set-sized Hahn workspaces; affine normalization handles other node scales.

Additional results concern exact Hermite precision lattices, cancellation
not determined by the node-separation tree, and a directed-path sufficient
certificate for nonuniform moment precision. A symmetric three-node example
proves that an improved first-order weight estimate can fail nonlinearly;
the additional hypothesis for the exact nonlinear precision lattice is
therefore substantive. Arbitrary-rank arguments use strong Hahn summation,
not an unjustified appeal to sequential convergence.

## Novelty and proof status

This is a proof-focused research manuscript, not a certified resolution of a
named published open conjecture. Classical Prony reconstruction, clustered
conditioning estimates, Prony curves, Hermite interpolation, and differential
precision tracking are credited explicitly. The proposed refinements are
identified separately from those antecedents.

The repository comparison is pinned to
`4cf691c7d951e037739d32d9f5c387dcce724f3c` of
`VladimirReshetnikov/Surreal`. The documentation catalogue,
formalization-ledger excerpts, polynomial-algebra report README, and
repository searches were inspected. All archive contents and historical
revisions were not exhaustively inspected. The literature search likewise
cannot establish priority or guarantee that equivalent results do not exist.
See Sections 1.2–1.3 and Appendices A–B for the precise boundary of the audit.

The manuscript supplies mathematical proofs. They have not been independently
refereed or checked in Lean. The included symbolic checks do not prove the
general theorems, Hahn support results, class/universe claims, or novelty.
No source repository was modified.

## Build the PDF

Use a TeX distribution providing pdfLaTeX, latexmk, Latin Modern, AMS packages,
mathtools, microtype, geometry, booktabs, array, longtable, enumitem, xcolor,
hyperref, and fancyhdr. From this directory run:

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

Without latexmk, run `pdflatex -halt-on-error -interaction=nonstopmode article.tex`
repeatedly until the table of contents, citations, and cross-references stabilize.
The delivered source uses an internal bibliography, so BibTeX is unnecessary.

## Run the exact checks

Python 3.9 or newer is expected; the delivery was tested with Python 3.13.5
and SymPy 1.14.0. From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The script uses exact symbolic arithmetic, rational arithmetic, and finite
graph enumeration. It makes no network requests and invokes no external CAS.
It can be run from another working directory as well. A successful run writes
`data/verification.txt`; a stale log is removed before a new run.

The recorded run passed 10,052 exact assertions. The count includes numerous
finite graph-walk checks and is not a count of independent theorems. Tests
cover Hermite duality, Hankel determinants, cofactor and Pade identities,
two-node sharpness, the nonlinear three-node obstruction, rank-two valuation
arithmetic, and a directed-graph example. Read the proofs, not this count,
as the evidence for the general results.
