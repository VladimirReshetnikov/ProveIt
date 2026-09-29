# A cyclic-coloring obstruction to maximal binary DFAO reversal

**Nonattainment of the full coloring space for every 3 ≤ k ≤ n, and the exact three-output maximum for every n ≥ 7**

This is a research report in two parts. Part I is the original report of
20 September 2026, itself the merge of two independently prepared packages.
Part II was added on 28 September 2026 in batch 39 of ProveIt's
incoming-report intake, from a later manuscript that answers, for three
outputs, the question Part I left open: the exact value of `R_2(n,k)` beyond
its finite range `7 ≤ n ≤ 30`. All sources were prepared for Vladimir
Reshetnikov and are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | two Cardinals-collection packages of 20 Sep 2026, `dfao-reversal-cyclic-coloring` (the spine) and `dfao-reversal-coloring-bound`, merged into one report | `dfao_reversal_research.zip` + `binary_dfao_reversal_research.zip` (as the collection manifest records them) | (none) | merged `8374aaa79` (Cardinals repository), in ProveIt since `dc54c3cb3` | Part I: Sections 1–12 (pp. 1–28), Appendices A–D (pp. 50–52); Section 1.3 records what each package contributed |
| 02 | batch 39, manuscript 06 (*Exact Binary Reversal with Three Outputs: An all-state solution and rigidity of extremizers*, 28 Sep 2026, 19-page PDF as delivered) | `ProveIt_Three_Output_Reversal.zip` (inner `three_output_reversal/`, main file `article.tex`) | `fbba58593` | `e2b1f016a` (prefix `02-three-output-`) | Part II: Sections 13–27 (pp. 29–49) |

The pin `fbba58593` is ProveIt commit
`fbba58593dc0622aa914972896150d4848f935b5`. At the pin, Part I's
`article.tex` had blob `e6dbd47b…` and its `README.md` blob `13166e22…`;
both were unchanged at the placement commit, so every statement manuscript 06
makes about Part I refers to the text printed here. The archive arrived in
`74f7f5bdb`; its manuscript, PDF and delivery README are not shipped and
survive in the arrival commit. Part II prints every result, proof, example,
remark, limitation and question of the manuscript. What it re-derives from
Part I (the coloring-orbit description, the collision-coloring bound, the two
graph counts) is printed once, in Part I, and credited in Section 14.1; the
manuscript's different proof of the three-color biclique count is kept as a
second proof. Section 27.6 of the article lists where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The finite
computations check stated finite ranges and implementations; they are not a
proof of the all-`n` statements. Attainment in Part II (and in Part I's finite
optimality result) rests on a published external theorem, Davies's
Theorem 3 / Corollary 3, which is cited, not reproved.

## Results

For maps `a, b : Q → Q` and `τ : Q → Δ` with `|Q| = n`, `|Δ| = k`, the
reachable reverse states are the coloring orbit `τ⟨a,b⟩`; for accessible
DFAOs its size is the state complexity of the reversal (Proposition 2.1).

**Part I** (unchanged apart from dated pointers) gives a self-contained
proposed proof of

    |τ⟨a,b⟩| ≤ k^n − k! + g(k) < k^n        (3 ≤ k ≤ n),

where `g(k)` is Landau's function, answering Davies's Problem 1
(arXiv:1705.07150v2, Section 5, printed page 17). The `k = n` case is
Holzer–König's classical bound and is not claimed as new. Nonattainment is
proved twice, by a short qualitative route (Lemma 4.1, Theorem 4.2) and by the
counting argument (Theorem 1.1). Part I also proves an abelian-permutation
extension, a polynomial-time missing-coloring algorithm with two certificate
formats, two instance-specific chromatic bounds and a universal structural
bound `U(n,k)` (Theorem 9.4); a complete C++ enumeration settles all 462,066
reduced instances with `n ≤ 4`; and `U(n,k)` equals the published lower
construction `L(n,k)` on all 372 pairs `7 ≤ n ≤ 30`, `3 ≤ k < n`
(Proposition 10.1), a finite computer-assisted optimality result.

**Part II** (manuscript 06) works at `k = 3`. Let `(A, B) = (A_n, B_n)` be the
closest coprime split of `n`: `(h, h+1)` for `n = 2h+1`, `(h−1, h+1)` for
`n = 2h` with `h` even, `(h−2, h+2)` for `n = 2h` with `h` odd. It proves:

1. **`R_2(n,3) = 3^n − 3(2^A + 2^B − 2) + B` for every `n ≥ 7`**
   (Theorem 13.1), whether the original automaton is required to be accessible
   with `n` states or minimal with exactly `n` states; the upper bound
   `|τ⟨s,t⟩| ≤ 3^n − D_n` holds for arbitrary maps. The upper bound is new; the
   attainment is Davies's published construction. This settles the `k = 3`
   slice of Davies's Problem 2.
2. Every extremizer has one permutation letter with cycles of lengths `A, B`
   and one rank-`(n−1)` singular letter with exactly one cross-cycle double
   fiber; the output is constant on the `A`-cycle and primitive on the
   `B`-cycle; and the reachable set is every improper coloring of `K_{A,B}`
   plus one `B`-element proper orbit (Theorem 19.1). These conditions are
   necessary, not sufficient (Example 19.3).
3. A `6AB` penalty for a second cross collision (Proposition 19.2), the orbit
   inventory of the missing colorings (Theorem 20.1), residue-class
   asymptotics `(3^n − R_2(n,3))/2^{n/2} → 9/√2, 15/2, 51/4` and an order-12
   linear recurrence for the deficit (Corollaries 21.1, 21.2).

Added in the merge (not stated by the manuscript): Remark 18.3 shows that the
manuscript's comparisons bound every entry of Part I's structural collection,
so `D(n,3) = D_n` and `U(n,3) = L(n,3) = R_2(n,3)` for every `n ≥ 7` — the
`k = 3` case of the equality Part I's Section 12.1 asks for. In the write
phase the closed form was compared with the 24 rows `k = 3` (`n = 7..30`) of
`data/finite_range_bounds.csv`: it equals both the `upper` and the `lower`
column in every row, and the recorded split `(ell, m)` is `(A_n, B_n)` in every
row (Section 18.2).

## Not claimed

- Nothing for `k ≥ 4`: the exact maximum, and the equality `U(n,k) = L(n,k)`
  beyond Part I's finite range, remain open (Question 23.1). Part II does not
  settle Davies's full Problem 2 for variable `k`, nor the
  largest-two-generated-transformation-monoid problem, nor any other open
  question of Davies's Section 5 besides the `k = 3` slice of Problem 2.
- No new proof of Davies's lower construction (the two-generator
  monoid-generation theorem); Part II proves the upper bound and the equality
  restrictions and uses the published theorem for attainment. Finite
  breadth-first searches do not replace that dependency.
- No classification of extremizers: the rigidity theorem gives necessary
  conditions only (Example 19.3 is a machine satisfying (i)–(iii) that is not
  extremal); the `6AB` penalty is proved only under its stated hypotheses
  (optimal cycles, injective on each cycle, proper output).
- No novelty for the orbit reduction, the lower witness, the graph
  classification method, primitive-word counting, the small values
  24, 67, 218, 699 (exact in Davies's Table 3), the ternary witness, the
  Landau function, the diagonal specialization `k = n`, or graph coloring as a
  method. The threshold `n ≥ 7` is essential: at five states the coprime
  two-cycle construction is not optimal.
- No priority. Both literature checks were targeted (Part I on
  20 September 2026, Part II on 28 September 2026: the Davies text and the
  Holzer–König metadata); neither is an exhaustive citation-index review,
  a survey of theses, or correspondence with the author.
- No claim that random tests or finite enumerations establish a universal
  theorem, and no claim that all improper colorings are reachable in arbitrary
  cases (Part II proves it only for extremizers at `k = 3`).

## Labels

Part I's 90 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`rem:`, `tab:`, `fig:`, `app:`) and are unchanged, with unchanged numbers
(compared in the `.aux` files of the committed and the new build). Part II
added **82** labels, all with the prefix `tor:` ("three-output reversal").
Total: 172. No label was renamed or removed. Part II starts at Section 13 and
its one table continues Part I's numbering (Table 5); Part I's appendices come
after Part II and contain no numbered equations, tables, figures or
theorem-like items.

One change affects how Part I's references print, not their numbers: Part I
declared its theorem-like environments on the shared `theorem` counter, and
`cleveref` printed every lemma, proposition, corollary and remark as
"theorem" (for example "theorem 3.3" for `lem:rightmost`). The preamble now
declares them through alias counters (`aliascnt`), as manuscript 06 did, so
each reference carries its own name; in the `.aux` files only the recorded
reference type changed.

## Notation

Part I's symbols keep their meanings. Table 5 (Section 13.2) lists Part II's
symbols; watch in particular for:

- `D_n` (one index) is the closed-form deficit `𝓑(A_n,B_n) − B_n`; Part I's
  `D(n,k)` is the minimum of its finite collection (9.11)–(9.15). They differ
  by definition; `D(n,3) = D_n` for `n ≥ 7` is a theorem (Remark 18.3).
- `𝓑(u,v) = 3(2^u + 2^v − 2)` is Part I's `B_3(u,v)`, and `𝓑_k` in
  Question 23.1 is Part I's `B_k`; `B_n` (one index) is the larger split part,
  an integer, not a chromatic count. `C_L`, `P_G` mean Part I's `C_L(3)`,
  `P_G(3)`.
- `(A_n, B_n)` is Part I's `(ell, m)` at the optimum (CSV columns `ell,m`;
  the manuscript's own CSV uses `a,b`).
- `J(r)` is the largest *product* of a partition of `r`, not Landau's `g(r)`
  (a least common multiple) and not Part I's `H_r(t)`; `H_r(t) ≤ t·J(r)`.
- Renamed from the manuscript: `Prop(G) → Col_3(G)` and `𝒪_p(c) → Orb_p(c)`
  (Part I's `𝒪_r` is a set of permutation orders). `s,t` in Theorem 13.1 are
  arbitrary maps (Part I's letters `a,b`); in Part II `a,b` are cycle lengths.
  No normalization changed.

## Files

```
article.tex                            the report, standalone LaTeX with an internal bibliography
article.pdf                            the compiled report, 56 pages (title page, contents pp. i–ii,
                                       Part I pp. 1–28, Part II pp. 29–49, Part I's appendices pp. 50–52,
                                       bibliography p. 53)
README.md                              this guide
Makefile                               Part I: build, check and audit targets (build in place; see below)
source_audit.md                        Part I: locations inspected in Davies v2, attribution, dependency boundary
RESEARCH_STATUS.md                     Part I: status record of the merged-in source dfao-reversal-coloring-bound
LITERATURE_SEARCH.md                   Part I: that source's literature-search record
02-three-output-SOURCE_AUDIT.md        Part II: manuscript 06's source audit (delivered as SOURCE_AUDIT.md)
code/reversal.py                       Part I: primary implementation (composition, orbits, missing
                                       colorings, CRT membership, chromatic counts, structural bound, u_witness)
code/run_checks.py                     Part I: primary Python suite and the finite-range CSV
code/check_bound_certificate.py        Part I: independent re-evaluation of the 372 bounds
code/check_large_example.py            Part I: tuple-set BFS of the n=8, k=5 witness
code/orbit_count.cpp                   Part I: single-instance C++17 BFS over code/bfs_cases.txt
code/bfs_cases.txt                     Part I: the 20 BFS fixtures
code/exhaustive.cpp                    Part I: complete C++17 enumeration for n ≤ 4
code/dfao.py                           Part I: second implementation family
code/certificate_checker.py            Part I: standalone certificate verifier (imports nothing from dfao.py)
code/run_experiments.py                Part I: second audit suite
code/test_dfao.py                      Part I: ten unit tests
code/02-three-output-verify.py         Part II: structural comparisons, witness BFS, inventories (delivered as code/verify.py)
code/02-three-output-independent_check.py  Part II: independent arithmetic checks (delivered as code/independent_check.py)
code/02-three-output-Makefile          Part II: the delivered root Makefile (pdf/check/clean)
data/finite_range_bounds.csv           Part I: 372 rows of exact upper and lower values, split, minimizing graph
data/verification_summary.json         Part I: primary check counts and recorded seed
data/independent_bounds_check.json     Part I: independent arithmetic-verifier result
data/small_witnesses.json              Part I: explicit small automata and counts
data/bfs_witnesses.json                Part I: explicit automata and counts
data/cpp_orbit_counts.csv              Part I: C++ BFS results with checksums
data/independent_python_bfs.json       Part I: the separate large-example Python BFS
data/example_certificate.json          Part I: the 8-state, 5-output K(3,5) certificate
data/checks_console.txt                Part I: primary test run output
data/02-three-output-verification.json Part II: recorded run of the verifier (PASS)
data/02-three-output-console.txt       Part II: its console output (byte-identical to the JSON)
data/02-three-output-structural_checks.csv  Part II: n, a, b, defect, maximum, candidates for n = 7..200 (194 rows, CRLF)
data/02-three-output-independent_check.json Part II: recorded independent run (PASS)
data/02-three-output-independent_console.txt Part II: its console output (byte-identical to the JSON)
data/02-three-output-pdf_audit.json    Part II: rendering audit of the delivered (unshipped) 19-page PDF
results/certificates.json              Part I: four certificates in the second schema
results/exhaustive.json                Part I: per-row counts, maxima and one maximizer per row for n ≤ 4
results/examples.json                  Part I: the four worked examples
results/sharp_n3_orbit.json            Part I: the 24 (coloring, word) pairs of Appendix C
results/landau_gaps.json               Part I: g(k) and k! − g(k), k = 3..12
results/audit_summary.json, python_audit_log.txt, certificate_check.txt,
  unit_tests.txt, reproduce_log.txt, environment.txt   Part I: audit records and environment
results/pdf_checks.json                Part I: rendering audit of a 19-page predecessor article
```

The ten `02-three-output-` files were staged in the placement commit
`e2b1f016a`, byte-identical to the delivery (re-verified in the write phase
against a fresh extraction); the CSV is all-CRLF as delivered (written by
`csv.writer`) and is protected by a `-text` line in
`SetTheory/Cardinals/.gitattributes`. The manuscript's delivered `README.md`,
`article.tex` and `article.pdf` are not shipped.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex article.tex` three times. Build in a scratch copy of
`article.tex`, so that no auxiliary files land here: Part I's `make pdf` and
the `pdf` target of `code/02-three-output-Makefile` both run LaTeX in place.
Needed packages: newtx, amsmath/amsthm/mathtools, microtype, geometry,
booktabs, enumitem, fancyhdr, tcolorbox, TikZ, listings, aliascnt, hyperref,
cleveref. No bibliography processor, font file or downloaded paper is needed.
The shipped PDF was built with MiKTeX (pdfTeX 1.40.26) with no errors, no
warnings, no undefined or multiply defined references, no duplicate
destinations and no overfull or underfull boxes. The build of the committed
Part I text had two duplicate-destination warnings (`page.1`, `page.2`),
because its title page overflowed onto a second arabic-numbered page; the
title page is now respaced to fit one page and excluded from page anchors.

## Rerun the checks

Python 3.10+ (standard library only) for both parts. Do not use `-O` or
`PYTHONOPTIMIZE` for Part I, whose audits use assertions deliberately.

**Part I.** Its scripts write into `data/` and `results/` and would
**overwrite** the shipped records (on Windows also with CRLF line endings), so
run them on a copy:

```sh
W=/path/to/scratch
mkdir -p "$W/01" && cp -r code data results "$W/01/"
cd "$W/01"
python code/run_checks.py --max-n 30        # rewrites data/finite_range_bounds.csv, small_witnesses.json,
                                            #   example_certificate.json, verification_summary.json
python code/check_bound_certificate.py      # reads the CSV; writes data/independent_bounds_check.json
python code/check_large_example.py          # writes data/independent_python_bfs.json (appreciable memory)
python code/run_experiments.py              # writes results/*.json
python code/certificate_checker.py results/certificates.json   # prints ACCEPTED 4 certificate(s)
python -m unittest discover -s code -p 'test_*.py' -v
c++ -std=c++17 -O2 -Wall -Wextra -pedantic code/orbit_count.cpp -o orbit_count
./orbit_count < code/bfs_cases.txt          # 20 fixtures; largest visits 1,539,561 states
c++ -std=c++17 -O3 -Wall -Wextra -pedantic code/exhaustive.cpp -o exhaustive
./exhaustive 4 > results/exhaustive.json    # 462,066 reduced instances; run before run_experiments.py
```

On Windows PowerShell, `Get-Content -Raw code/bfs_cases.txt | .\orbit_count.exe`.
`run_checks.py` covers 19,683 unreduced `n = k = 3` triples, 161,838 CRT
membership tests, 2,550 fixed-seed random automata (seed 20260920), 1,362
graph-count checks, 46,234 permutation-order checks, the 372 finite bounds and
ten explicit witnesses; `run_experiments.py` covers 4,374 ordered pairs with
all output bijections, 1,000 cyclic-membership cross-checks, 252 relabeling
checks, 2,724 chromatic-formula checks, 330 random reverse-orbit checks,
1,440 larger structural certificates and the six C++ maximizers.
`check_bound_certificate.py` does not import `reversal.py`, and
`certificate_checker.py` does not import `dfao.py`. The main API:

```python
import sys
sys.path.insert(0, "code")
from reversal import missing_coloring, structural_bound, u_witness
p, s, tau = u_witness(3, 5, 5)
print(missing_coloring(p, s, tau, 5)["target"])
print(structural_bound(8, 5)["upper_bound"])  # 369020
```

Transformations are tuples whose `q`-th entry is the image of `q`;
`compose(a,b)` means `a∘b`; a word `ab` in a reverse-orbit record means
`τ∘a∘b` (pull back by `a`, then by `b`).

**Part II.** Its scripts still use the delivered names: each takes the report
root as `parents[1]` of its own path and reads or writes
`data/verification.json`, `data/structural_checks.csv` and
`data/independent_check.json`. No name collides with a Part I file, but run in
place the verifier leaves two stray unprefixed files in `data/`, the
independent check fails unless the verifier has run there first, and
`make -f code/02-three-output-Makefile check` runs `python3 code/verify.py`,
which does not exist here (after its shell redirection has already created an
empty stray `data/console.txt`). Restore the delivered layout in a scratch copy
(Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code" "$W/02/data"
for f in code/02-three-output-*.py; do cp "$f" "$W/02/code/${f#code/02-three-output-}"; done
cp code/02-three-output-Makefile "$W/02/Makefile"
cd "$W/02"
py code/verify.py --max-n 200 --bfs-max-n 11 > data/console.txt
                               # writes data/structural_checks.csv, data/verification.json
py code/independent_check.py > data/independent_console.txt
                               # reads data/verification.json; writes data/independent_check.json
```

This was run on 28 September 2026 (Python 3.14.4, about 3 s): both passed;
the CSV is byte-identical to the shipped one, and the three JSON files and
two console captures equal the shipped ones apart from Windows line endings.
The verifier evaluates 752,291 structural candidates over the 194 values
`7 ≤ n ≤ 200`, fully explores the witness orbits for `7 ≤ n ≤ 11` (largest
176,871 states), checks three orbit inventories and 72 unique-cross-pair
colorings; the independent script checks the closed form for `7 ≤ n ≤ 1000`
(994 values) and 982 recurrence instances. `make check` in the scratch copy
does the same with `python3`.

## Discrepancies and delivery names

- **Delivery names.** The Part II scripts use the delivered paths listed
  above; `code/02-three-output-Makefile` names `code/verify.py`,
  `code/independent_check.py`, `data/console.txt` and
  `data/independent_console.txt`, and its `pdf` target builds whatever
  `article.tex` is in the working directory (here: the merged report, in
  place). `data/02-three-output-independent_check.json` (and its console copy)
  says "No imports from verify.py", meaning the delivered name of
  `code/02-three-output-verify.py`. The article quotes the shipped names.
- **Unshipped PDFs.** `data/02-three-output-pdf_audit.json` describes the
  manuscript's delivered 19-page PDF, which is not shipped;
  `results/pdf_checks.json` describes a 19-page predecessor of Part I.
  `article.pdf` here is a new build of the merged text (56 pages).
- **Duplicates.** Each Part II console capture is byte-identical to the JSON
  it prints.
- **Scope of the verifier's bound.** `02-three-output-verify.py` uses the
  product bound `J(r)` instead of Part I's exact residual order sets, so its
  "structural" deficits are relaxations of Part I's `D(n,3)` entries, not the
  same numbers; both give `D_n` as the minimum (Remark 18.3), and the
  `maximum` column of its CSV equals Part I's `upper` for `n ≤ 30`.
- **Stale delivered text.** Part I's `RESEARCH_STATUS.md` ("No proof of the
  exact optimal binary reversal complexity for arbitrary `n,k`") and
  `source_audit.md` describe Part I at its original date; for `k = 3` the
  exact value is now proved in Part II. They are kept verbatim. The article's
  own sentences to that effect (title page, reading-routes box, Sections 1.3,
  1.4, 10.1, 12.1, 12.3, 12.5) now carry dated pointers to Part II.
- **Source-table note.** Part I (Section 10.3) corrects Davies's printed
  Table 2 entry for `n = 8, k = 5` from 368020 to 369020. Manuscript 06 cites
  Davies's Corollary 3 on printed page 12 and Table 3 on printed page 17; it
  does not use Table 2.

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats DFAO reversal, and
manuscript 06 names no report other than Part I, so no reciprocal note was
written. The report sits in the research-report collection of the
`SetTheory/Cardinals` Lean project. That placement confers no formal status:
no Lean or Rocq declaration anywhere in ProveIt formalizes any statement of
Parts I–II (a search of the tracked `.lean` files for DFAOs, automata with
output or Davies finds none). Section 26 records the formalization plan the
manuscript proposes (coloring semantics, the rightmost-singular lemma, graph
classification, the arithmetic comparisons, the equality theorem with the
lower construction as a named hypothesis); none has been started.

## Sources and attribution

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
Automata with Output*, arXiv:1705.07150v2 (17 October 2017): Proposition 4,
Theorem 3 and Corollary 3, Tables 2–3, Section 5 Problems 1–2.
https://arxiv.org/abs/1705.07150

Markus Holzer and Barbara König, *On deterministic finite automata and
syntactic monoid size*, Theoretical Computer Science 327(3), 319–347 (2004),
https://doi.org/10.1016/j.tcs.2004.04.010 — background, Theorem 13 (the
`k = n` bound) and the graph-coloring method.

Marc Deléglise and Jean-Louis Nicolas, *The Landau Function and the Riemann
Hypothesis*, arXiv:1907.07664 — cited only for the name of `g(k)`.

No third-party paper PDFs or font files are included.
