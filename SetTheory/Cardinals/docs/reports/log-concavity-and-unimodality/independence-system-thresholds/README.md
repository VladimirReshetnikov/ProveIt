# Sharp size thresholds for failures of log-concavity in independence systems

Research report prepared with ChatGPT (OpenAI), September 19, 2026.

## Main result

For each rank r >= 4, the smallest ambient size admitting failure of each
shape is the same among all independence systems, among the systems satisfying
Xie–Xu's rank-dependent augmentation bound, and among systems with exact
additive augmentation parameter 3:

| Rank | Ordinary log-concavity | Ordered log-concavity | Ultra log-concavity |
|---|---:|---:|---:|
| 4 | 7 | 6 | 5 |
| 5 | 7 | 7 | 6 |
| 6 | 8 | 7 | 7 |
| r >= 7 | r+1 | r+1 | r+1 |

Ultra log-concavity is normalized by the ambient ground-set size n, not the
polynomial degree r. The ordinary seven-element witness has coefficients
1, 7, 21, 4, 1, with 4^2 < 21. It consists of all subsets of a fixed
four-element core together with all subsets of the seven-element ground set
of size at most two.

## Attribution and scope

The initial target, Xie and Xu's Conjecture 4.8 (arXiv:2408.09152v1), already
has a September 2026 disproof announced by Alex Chengyu Li. This report does
NOT claim the first disproof. After locating that prior work, the target was
refined to the exact rankwise minimum-size question above. Li's public overview
advertises a thirteen-element example and other asymptotic families. The full
linked SSRN/Zenodo manuscript could not be retrieved during this investigation;
possible detailed overlap and priority for the refinements remain unverified.
The report proves its own statements, but has not received independent peer
review and does not contain a Lean formalization. Parameter-two systems and
graph dependence polynomials are not settled here.

## Contents

- `article.pdf`: compiled research article (18 pages in this build).
- `article.tex`: complete LaTeX source, including bibliography.
- `verify.py`: exact-arithmetic Python verification, standard library only.
- `SOURCE_NOTES.md`: primary sources, retrieval status, and attribution notes.
- `data/small_counterexamples.json`: every face of the 5-, 6-, and 7-element
  witnesses, their facets, counts, augmentation obstruction, and shape defects.
- `data/sparse_counterexamples.json`: variants with 20, 25, and 30 faces.
- `data/family_shape_grid.csv`: all 2,024 parameter triples with 3 <= n <= 24,
  2 <= r < n, and 1 <= s < r, checked against the three closed-form criteria.
- `data/minimality_bounds.csv`: the 26 finite maximal-ratio bounds in the proof.
- `data/minimality_all_cases.csv`: every individual candidate ratio entering
  those maxima, with exact rational values and the maximizing upper count.
- `data/face_vector_counts.csv`: all face-vector counts through seven vertices.
- `data/failing_face_vectors.json`: complete failing-vector lists from that search.
- `data/exhaustive_uniform_shadows.json`: independently enumerated unrestricted
  lower-shadow minima for all uniform layers on at most six vertices.
- `data/exhaustive_core_shadows.json`: independently enumerated core-constrained
  lower-shadow minima for the two exceptional rank/size lower bounds.
- `data/rankwise_thresholds.csv`: rankwise minima for 4 <= r <= 100.
- `data/codimension_one_family.csv`: coefficients, total counts, and exact
  log-concavity ratios for 3 <= r <= 100.
- `data/total_face_sequence.csv`: N_r = 2^(r+1) - 1 - binomial(r+1,2), r=0,...,100.
  The combinatorial family uses r >= 3; the first three terms are a formal extension.
- `data/verification_report.json`: actual verification summary and Python version.

## Reproduce all computations

Python 3.10 or newer is sufficient. No third-party Python packages are needed.

```sh
python verify.py --full --output regenerated-data
```

The full run examines 2,232,706 uniform families: 1,116,354 unrestricted families
and 1,116,352 core-constrained families. The largest individual enumeration has
2^20 states. It also examines 5,459 possible face vectors and explicitly checks
56 independence systems plus six direct sums. It does not enumerate all labelled
complexes on seven vertices. General theorems and infinite-rank assertions are
proved in the article, rather than inferred from a finite search.

For a faster run omitting the independent uniform-family enumerations:

```sh
python verify.py --output quick-data
```

Every mathematical comparison uses integers or `fractions.Fraction`. Verification
checks remain active under `python -O`. A failed check exits with an exception;
success prints a JSON object whose status is `PASS`. The recorded Python version
may differ between machines; this is the only environment-specific report field.

## Rebuild the PDF

A standard TeX Live installation with the packages named in the preamble is enough.
No external image, font file, bibliography database, or code execution is required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The third pass stabilizes the table of contents and cross-references after a fresh
build. Build-generated `.aux`, `.log`, `.out`, and `.toc` files are not included.

## Certificate conventions

A subset is encoded by an integer bit mask. Vertex j, numbered starting at 1,
corresponds to bit j-1. For example, mask 17 means {1,5}, and mask 15 means
{1,2,3,4}. A failed-augmentation witness is `[small_mask, large_mask]` for which
no new element of the larger face extends the smaller face. The exact parameter
is one plus the largest positive size difference of such a pair, or 1 if there
is no positive difference.

Coefficient arrays include a_0 and all terminal zeros through ambient index n.
The shape-defect records contain the integer left and right sides of the
inequalities as written in the article. A negative difference certifies failure.

The maximal-ratio tables deliberately relax some constraints: a_(k-1) is bounded
by binomial(n,k-1), and a_(k+1) by the inverse lower-shadow bound. A ratio at most
one in this larger feasible class proves the needed universal inequality.

## Files deliberately not included

No external copyrighted paper, downloaded font file, incomplete proof-assistant
code, or unexecuted claim of formal verification is included. The source papers
are identified in the article and in SOURCE_NOTES.md.
