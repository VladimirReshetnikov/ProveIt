# A cyclic-coloring obstruction to maximal binary DFAO reversal

Research note prepared for Vladimir Reshetnikov, 20 September 2026.

This package is the merge of two independently prepared research packages,
`dfao-reversal-cyclic-coloring` (the spine) and `dfao-reversal-coloring-bound`.
Both proved the same headline inequality by the same three-case argument with
the same collision-orbit-graph construction; the shared theorem is proved here
exactly once. Everything each package built on top of that shared core was
complementary and is kept. Section 1.3 of the article records the provenance
in detail.

## Result and status

For arbitrary maps a,b:Q→Q and τ:Q→Δ, with |Q|=n and |Δ|=k,
3≤k≤n, the article gives a self-contained proposed proof of

    |τ⟨a,b⟩| ≤ k^n − k! + g(k) < k^n,

where g(k) is the maximum order of a permutation of k objects.
For accessible DFAOs the left side is exactly the state complexity of
reversal. The target is Davies's first open problem in arXiv:1705.07150v2,
Section 5, printed page 17. The k=n special case is classical (Holzer and
König, Theorem 13) and is not claimed as new; the proposed extension handles
k<n. Graph coloring and chromatic polynomials in the transformation-monoid
setting are also prior art and are not claimed as an invention here.

Nonattainment is proved twice, by two logically independent routes: a short
qualitative argument (Lemma 4.1, Theorem 4.2) using no counting and no Landau
function, and the quantitative counting argument that yields the additive
deficit. The article also proves an abelian-permutation extension, a
constructive polynomial-time missing-coloring algorithm with two certificate
formats, two instance-specific chromatic bounds, and a universal structural
bound U(n,k). A complete C++ enumeration settles all 462,066 reduced instances
with n≤4. U(n,k) agrees with the published lower construction for every pair
7≤n≤30, 3≤k<n: 372 exact finite comparisons. That finite result is NOT a
proof of the all-n exact-optimum conjecture.

The principal proofs do not depend on computation. They have not been
independently refereed or checked by a proof assistant. A literature search
found no later resolution of the selected problem, but was not exhaustive and
establishes no priority. See `source_audit.md`, `RESEARCH_STATUS.md` and
`LITERATURE_SEARCH.md`.

## Article

- `article.pdf`: the compiled article.
- `article.tex`: complete editable LaTeX source, including the bibliography.
- `Makefile`: build, check and audit targets.

Rebuild with a standard TeX installation providing newtx, amsmath, amsthm,
microtype, geometry, booktabs, fancyhdr, tcolorbox, TikZ, listings, hyperref,
and cleveref:

```text
latexmk -pdf -interaction=nonstopmode article.tex
```

No external bibliography processor, font file, or downloaded paper is needed:
the bibliography is embedded in `article.tex`, so `pdflatex article.tex` run
two or three times also suffices.

## Python verification (Python 3.10+, standard library only)

Run from this directory, without Python's `-O` flag and with `PYTHONOPTIMIZE`
unset (the checks use assertions deliberately):

```text
python code/run_checks.py --max-n 30
python code/check_bound_certificate.py
python code/check_large_example.py
python code/run_experiments.py
python code/certificate_checker.py results/certificates.json
python -m unittest discover -s code -p 'test_*.py' -v
```

`run_checks.py` writes its records into `data/`. Its checks include:

- 19,683 exhaustive (a,b,τ) triples for n=k=3, fully unreduced, including
  nonsurjective output maps;
- 161,838 CRT membership tests compared with literal cyclic orbits;
- 2,550 deterministic-seed random/mixed automata and missing certificates;
- 1,362 graph coloring/count checks;
- 46,234 permutations for independent small-order-set checks;
- all 372 finite bound comparisons, and ten explicit small witnesses.

`run_experiments.py` writes its records into `results/`. Its audits include
the 4,374 *ordered* three-state pairs with all six output bijections, 1,000
cyclic-membership cross-checks, 252 relabeling-intersection checks against
g(k), 2,724 chromatic-formula checks, 330 random reverse-orbit checks for
n≤8, 1,440 larger structural certificate checks for 3≤n≤50, and the six C++
maximizing witnesses recomputed in Python. The three exhaustive n=k=3 counts
(19,683 unreduced triples, 4,374 ordered pairs with all bijections, 378
symmetry-reduced C++ instances) are kept separate on purpose: the reduction
assumptions are part of what is being checked.

`check_bound_certificate.py` does **not** import `reversal.py`. It uses a
different order-set recurrence, inclusion-exclusion rather than the Stirling
recurrence, and direct displacement enumeration to reproduce the 372 bounds.

`certificate_checker.py` does **not** import `dfao.py`. It recomputes the
collision conditions, the whole pair orbit, properness and cyclic
nonmembership, and uses the pairwise-compatibility CRT criterion
r_i ≡ r_j (mod gcd(p_i,p_j)) instead of the producer's iterative merge. It
prints `ACCEPTED 4 certificate(s)` and exits nonzero on any rejection.

`check_large_example.py` uses a Python set of tuples for the n=8,k=5 witness.
It may use appreciable memory. It independently matches the C++ state count
369020, the sum of state encodings 72076669650, and their exclusive-or 128342.

## The two independent C++ programs (C++17)

`code/orbit_count.cpp` — single-instance BFS over the supplied fixtures:

```text
c++ -std=c++17 -O2 -Wall -Wextra -pedantic code/orbit_count.cpp -o orbit_count
./orbit_count < code/bfs_cases.txt
```

On Windows with a C++ compiler available in PowerShell:

```powershell
g++ -std=c++17 -O2 code/orbit_count.cpp -o orbit_count.exe
Get-Content -Raw code/bfs_cases.txt | .\orbit_count.exe
```

The program checks 20 supplied automata and returns a nonzero exit code on any
mismatching count. The input records give a case label, n, k, number of
letters, expected orbit size, then one transition array per letter and an
output array. State and output labels are zero-based. Every coloring c is
encoded as sum_i c[i]*k^i. No graph bound or mathematical optimality assertion
is used to compute the reached states. The largest included case visits
1,539,561 states. A deliberate universe-size limit prevents accidental
unbounded memory allocation on enlarged fixtures.

`code/exhaustive.cpp` — complete enumeration of all transformation pairs and
output-partition representatives for n≤4, a different job:

```text
c++ -std=c++17 -O3 -Wall -Wextra -pedantic code/exhaustive.cpp -o exhaustive
./exhaustive 4 > results/exhaustive.json
```

It prunes only by input-letter interchange and output-color relabeling: not by
state conjugacy, accessibility, minimality, or the number of permutation
generators. The six rows together contain 462,066 reduced instances. Only the
emitted maximizing witnesses, not every four-state candidate, are recomputed
in Python. `run_experiments.py` should be run after this output exists so that
its six witness checks are included.

## Main code API

```python
import sys
sys.path.insert(0, "code")
from reversal import missing_coloring, structural_bound, u_witness

p, s, tau = u_witness(3, 5, 5)
certificate = missing_coloring(p, s, tau, 5)
print(certificate["target"])
print(structural_bound(8, 5)["upper_bound"])  # 369020
```

```python
import sys
sys.path.insert(0, "code")
from dfao import missing_certificate
from certificate_checker import verify

cert = missing_certificate(a=(1, 2, 0), b=(0, 0, 2), tau=(0, 1, 2), k=3)
assert verify(cert)
print(cert["target"])  # [0, 2, 1]
```

Transformations are tuples whose q-th entry is the image of state q.
`compose(a,b)` means a∘b, so b is applied first. `act(c,t)` and `pullback(c,t)`
are the coloring c∘t. `orbit(tau, generators)` and `reverse_orbit` perform
literal BFS and are suitable only for manageable finite universes;
`reverse_orbit` refuses to return a partial orbit if its `max_states` limit is
reached. `missing_coloring` and `missing_certificate` do not enumerate the
orbit and do not compute g(k). A word `ab` in a reverse-orbit record means
first pull back by `a`, then by `b`, giving `tau o a o b`; it is not the
original forward-state action on that same word.

## Data (`data/`)

- `finite_range_bounds.csv`: 372 rows of exact values with the maximizing
  split and a minimizing graph certificate.
- `verification_summary.json`: primary Python check counts and recorded seed.
- `independent_bounds_check.json`: independent arithmetic-verifier result.
- `small_witnesses.json`, `bfs_witnesses.json`: explicit automata and counts.
- `cpp_orbit_counts.csv`: independent C++ BFS results with checksums.
- `independent_python_bfs.json`: separate large-example Python BFS result.
- `example_certificate.json`: the 8-state, 5-output K(3,5) certificate — an
  explicit unreachable coloring, its collision graph, and the three failed
  candidate tests produced by the three-candidate search.
- `checks_console.txt`: primary test run output.

## Results (`results/`)

- `certificates.json`: four machine-checkable certificates in the second
  schema, produced by the six-relabeling search and validated by
  `certificate_checker.py`. The two certificate schemas are kept distinct on
  purpose and neither is normalized onto the other.
- `exhaustive.json`: per-row search counts, maxima, maximizer counts, and one
  explicit maximizing (a,b,τ) triple per row.
- `examples.json`: the four worked examples with reverse-state counts,
  minimality data, and an unreachable coloring.
- `sharp_n3_orbit.json`: the 24 (coloring, word) pairs of Appendix C.
- `landau_gaps.json`: g(k) and k!−g(k) for k = 3..12.
- `audit_summary.json`, `python_audit_log.txt`, `certificate_check.txt`,
  `unit_tests.txt`, `reproduce_log.txt`, `environment.txt`.
- `pdf_checks.json`: a rendering audit (page count, LaTeX warnings,
  unresolved reference markers, text outside the page box, external links,
  word certificates, cleveref names, 140 dpi render, visual inspection). It
  was run against the 19-page predecessor article from which the certificate
  and enumeration material comes; it has not been rerun against the merged
  35-page article.

## Provenance notes

- `source_audit.md`: the seven numbered locations actually checked in Davies
  v2, the Holzer–König attribution points, search scope, dependency boundary.
- `RESEARCH_STATUS.md`: target, proposed result, status, further results, and
  the seven-item "what is not claimed" list.
- `LITERATURE_SEARCH.md`: inspected URLs, the CIAA 2018 DOI, representative
  search queries, and attribution boundaries.

The source's printed Table 2 contains 368020 for n=8,k=5. Evaluating its own
formula gives 369020, confirmed by both BFS implementations. This is a table
arithmetic correction, not a counterexample to the lower-bound theorem.

No checksum manifest is shipped with this package, and none should be added:
re-running verification rewrites some generated files, including recorded
elapsed times.
