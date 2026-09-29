# Cofinal strata and ordinal absorption

**Finitary powersets of finite lexicographic sums: maximal order types, uniform and nonuniform heights, and exact point ranks**

This is a research report in three parts. Part I is the original article of
19 September 2026. Parts II and III were added on 28 September 2026 in batch 36
of ProveIt's incoming-report intake, merged from four later manuscripts that
answer the question Part I left open: the height of the finitary powerset when
the fibres are not all equal. Every manuscript was prepared for Vladimir
Reshetnikov with ChatGPT.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 | *Cofinal strata and ordinal absorption* | (none) | unpacked `a3fe9660e`, filed here `f0f61b70d`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–14, Appendices A–B (pp. 1–16, 68–70) |
| 07 | batch 36, manuscript 07 | `ProveIt_Nonuniform_Powerset_Heights` (*Retirement paths and exact heights of nonuniform finitary powersets*) | `e21766d04` | `1a1396d4d` (prefix `02-retire-`) | in Part II, notably the second proof of Theorem 21.1 (Section 21.3), examples in Section 23, Sections 24 and 25 |
| 09 | batch 36, manuscript 09 | `ProveIt_Persistent_Frontier_Heights` (*Persistent frontiers and exact heights: a pure-height substitution theorem, a limit-ordinal calculus, and finite certificates*) | `e21766d04` | `1a1396d4d` (prefix `03-wpo-`) | Part III: Sections 26–36 (pp. 50–61) |
| 11 | batch 36, manuscript 11 | `persistent_frontier_heights` (*Persistent frontiers and exact ordinal heights ... with exact local ranks*) | `e21766d04` | `1a1396d4d` (prefix `04-peel-`) | in Part II, notably the second proof of Theorem 17.4 (Section 17.4), Sections 18–19, 22, examples in Section 23, Section 25 |
| 12 | batch 36, manuscript 12 | `ProveIt_Ordinal_Heights_Research` (*Exact ordinal heights of finitely generated downsets: persistent coordinates, mixed ordinal fibers, and a finite-state rank calculus*) | `e21766d04` | `1a1396d4d` (prefix `05-ranks-`) | base of Part II: Sections 15–25 (pp. 17–49) |

The pin `e21766d04` is ProveIt commit
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`; at that commit this directory was
byte-identical to the one the addition was made to, and 11 and 12 quote the
blob `57498d1b…` of the `article.tex` they read. The archives arrived in
`e13affd32`. Their manuscripts, PDFs and delivery READMEs are not shipped; they
survive in the arrival commit. Archives 09 and 11 wrap inner directories of the
same name (`persistent_frontier_heights/`) but are different packages. The
"Closing the addition" part (Sections 37–40, pp. 62–67) gathers the questions,
non-claims and merge provenance of all four sources.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean or
any other proof assistant, and no source claims otherwise. The computations
are finite checks of implementations, not proofs of the transfinite
statements.

## Result and scope

Let `K(P)` be the finitely generated downsets of `P`, including the empty
downset, ordered by inclusion. For a finite poset `Q`, replace each `q` by a
fibre and order distinct fibres according to `Q` (a lexicographic sum). Let
`M(Q)` be the inclusion-maximal antichains of `Q` ("frontiers") under Hoare
domination.

**Part I** (unchanged). For uniform ordinal fibres `alpha = omega^rho`,
`rho > 0`,

    o(K(S_alpha(Q))) = sum, in decreasing k, omega^(rho natural-product k) c_k(Q)
    h(K(S_alpha(Q))) = alpha * height(M(Q)),

where `c_k` counts size-`k` maximal antichains not dominated by a larger one;
the sum and the multiplication in the height formula are ordinary ordinal
operations. The maximal-order-type theorem allows nonuniform WPO fibres with
known pure values `o(K(P_q)) = omega^beta_q`. Part I's own text says that it
does not claim a nonuniform height formula; that sentence describes the report
at its pinned state and now carries a dated pointer to Parts II–III.

**Part II** (chain fibres, base 12). For positive pure fibres
`alpha_q = omega^rho_q`, `rho_q > 0` (Theorem 21.1, proved by 07, 11 and 12):

    h(K(sum_Q alpha_q)) = max over chains A_0 < ... < A_m in M(Q) of
        max(alpha_q : q in A_0 \ A_1) + ... + max(alpha_q : q in A_(m-1) \ A_m)
        + max(alpha_q : q in A_m).

Every `+` is ORDINARY ordinal addition in the written order: a coordinate is
charged when its vertex leaves the frontier, not while it persists. An
explicit chain attains the value. Part II also proves a finite persistence
theorem for abstract state systems with convex coordinate lifetimes
(Theorem 17.4, two proofs), an exact dynamic program over all downsets of the
skeleton (Theorem 20.2), the height for **every** finite ordinal
lexicographic sum, including zero, finite and successor fibres
(Theorem 22.2), exact ranks of individual downsets (Theorems 19.4 and 22.4),
phase refinement for arbitrary capacities (Theorem 19.1), a retirement-box
height theorem (Theorem 21.11), NP membership of the threshold problem for
the explicit pure-block encoding (Corollary 20.4), bounds and exponent-scale
invariance (Section 24), and a sufficient extension to non-chain coordinates
(Proposition 24.3).

**Part III** (09). The same formula holds when the fibres are arbitrary
well-partial-orders whose finitary powersets have positive pure **height**,
`h(K(P_q)) = omega^rho_q`, with `h(K(P_q))` in place of `alpha_q`
(Theorems 27.1 and 31.2). The upper bound uses Wolk's maximal-chain theorem.
Part III also proves that local stratum heights leave unbounded ambiguity
(Theorem 34.3), a height-two scheduling formula (Theorem 35.1), a pure-height
congruence and exponent-chamber invariance.

## Not claimed

No formula for ordinal width, for maximal order type or maximal
linear-extension type of these powersets beyond Part I's, for iterated
finitary powersets, or for infinite skeletons or infinite state systems. No
large-cardinal conclusion. Part III does not cover nonpure, finite or
successor WPO components, and `h(P_q)` alone does not suffice. No complexity
statement is polynomial in the skeleton size or in binary Cantor
coefficients; NP membership is not NP-completeness. No bound on lengths of
controlled executions. No priority: every source's literature search was
targeted, and non-discovery is not evidence of novelty. The uniform formula
and the persistent counterexample are Part I's and are credited, not claimed
anew. Section 38 lists every non-claim of the four sources; Section 39 lists
where the merge had to choose.

## Labels

Part I's 56 labels are bare (`sec:`, `eq:`, `thm:`, …) and are unchanged. The
addition added 181 labels, all with the prefix `nh:` ("nonuniform heights"):
130 plain `nh:` labels for Part II, the closing part and one new label
`nh:sec:remainedopen` on Part I's Section 14 heading, and 51 with the
sub-prefix `nh:wpo:` for Part III. Total: 237. No label was renamed or removed.
Every Part I section and theorem number, and 55 of Part I's 56 label numbers,
are as in the pinned article. The one exception is equation `eq:truncation`
(Theorem A.2's truncation formula in Appendix A): equations are numbered
continuously and Part I's appendices now come after Parts II–III, so it moved
from (24) to (83). The commit that wrote Parts II–III (`3a15f3421`) said no
number changed; that was wrong for this equation. Section 39 of the article
records the move.

## Notation

Part I's macros and meanings win: `#` is the natural sum (07, 09 and 11 print
it with the circled plus), `M(Q)` and `≼` are the frontiers and Hoare
domination, and `D(A)` is the set of strict predecessors of an antichain.
Table 4 (Section 15.4) lists every symbol of the addition and its name in each
source. Watch in particular for:

- **Empty exits.** Part II gives a transition with no departing coordinate
  the weight 1 (11, 12); Part III keeps 09's weight 0. The final heights agree
  for positive pure weights, but dynamic-programming tables and certificates
  do not (Remark 32.2), and weight 0 is wrong for finite fibres.
- **`h_q` versus `alpha_q`.** In Part III, 09's `alpha_q := h(K(P_q))` is
  renamed `h_q`: a height of a finitary powerset, not a fibre, and not
  `h(P_q)`.
- **"Ideal"** means any downset of the finite skeleton, not a directed ideal
  (unlike `Idl` in the neighbouring report on intrinsic approximations).
  09's "active frontier" `max I` need not be a frontier.
- **Labels of examples.** The N-poset is `a<c, b<c, b<d` throughout; 09's
  examples (drawn `a<c, a<d, b<d`) were transcribed by `a<->b, c<->d`. The
  delivered data files keep their own labels.

## Files

```
README.md                                   this guide
article.tex                                 the report (Parts I-III); \inputs references.tex
article.pdf                                 73 pages: unnumbered title page, contents i-ii, pages 1-70
references.tex                              bibliography included by article.tex (9 entries)
references.bib                              the same 9 entries in BibTeX, for reuse
build.py                                    Part I's build helper (runs code/verify.py, then latexmk)
PROOF_AUDIT.md                              Part I's proof-dependency and scope audit
SOURCES.md                                  Part I's literature and status record
code/ordinals.py                            Part I: exact hereditary CNF arithmetic below epsilon_0
code/frontiers.py                           Part I: frontier formulas, CLI, lex-sum truncation
code/verify.py                              Part I: verification suite (216,386 assertions recorded)
data/verification.json                      Part I: recorded run
data/quality_assurance.json                 Part I: build and inspection record
data/poset_census.csv                       Part I: 5,231 naturally labelled posets through six vertices
data/examples.json                          Part I: named examples and outputs
data/N.json, data/weighted_N.json, data/natural_exponent.json, data/lexicographic_tails.json,
data/mixed_height_counterexample.json       Part I: sample inputs
data/weighted_N_result.json, data/natural_exponent_result.json, data/lexicographic_tails_result.json,
data/mixed_height_counterexample_result.json   Part I: sample outputs
02-retire-PROOF_AUDIT.md                    07's proof and scope audit, as delivered
02-retire-SOURCES.md                        07's source record, as delivered
code/02-retire-Makefile                     07's Makefile (calls python3; see below)
code/02-retire-retirement.py                07's height evaluator (integer exponents; limit fibres)
code/02-retire-verify.py                    07's suite (3,210,888 assertions recorded)
data/02-retire-verification_results.json    07's recorded run
data/02-retire-{branching_frontiers,limit_fibres,mixed_N,persistent_large_coordinate,
      retiring_large_coordinates,uniform_N}.json             07's six inputs
data/02-retire-{same six names}_certificate.json             07's six certificates
03-wpo-PROOF_AUDIT.md                       09's proof and scope audit, as delivered
03-wpo-SOURCES.md                           09's source record, as delivered
code/03-wpo-Makefile                        09's Makefile (calls python3; builds its unshipped article.tex)
code/03-wpo-build.py                        09's build helper (builds its unshipped article.tex)
code/03-wpo-frontier_heights.py             09's programs, limit expansion and certificate checker
code/03-wpo-verify.py                       09's suite (167,920 checks recorded)
data/03-wpo-verification.json               09's recorded run
data/03-wpo-run_output.txt                  09's console output: byte-identical to the previous file
data/03-wpo-examples_summary.json           09's example summary
data/03-wpo-DELIVERY_CHECKS.json            09's delivery record (see "Discrepancies")
data/03-wpo-{height_two_overlap,limit_fibers,nonuniform_N,parallel_chains,
      persistent_large_coordinate,transfinite_exponent_labels}.json   09's six inputs (delivered in examples/)
data/03-wpo-{same six names}_certificate.json                         09's six support certificates
04-peel-PROOF_AUDIT.md                      11's proof audit, as delivered
04-peel-SOURCES.md                          11's source record, as delivered
code/04-peel-build.py                       11's build helper (builds its unshipped article.tex into _build/)
code/04-peel-ordinals.py                    11's ordinal engine (below epsilon_0)
code/04-peel-persistent_height.py           11's solver: paths, peeling, phases, point ranks
code/04-peel-verify.py                      11's main suite (129,593 assertions recorded)
code/04-peel-check_local_ranks.py           11's local-rank suite (940 systems, 6,132 ranks, 37 regressions)
data/04-peel-verification.json, data/04-peel-verification_console.txt              11's main run
data/04-peel-local_rank_verification.json, data/04-peel-local_rank_console.txt     11's local-rank run
data/04-peel-examples_results.json          11's example outputs
data/04-peel-package_quality.json           11's delivery record (see "Discrepancies")
data/04-peel-{N_high_a,N_high_b,empty,mixed_successor_product,persistent_large_coordinate,
      single_impure,successor_product,transfinite_exponents,uniform_N,weighted_N}.json   11's ten inputs (delivered in examples/)
05-ranks-PROOF_AUDIT.md                     12's proof audit, as delivered
05-ranks-SOURCES.md                         12's source record, as delivered
code/05-ranks-Makefile                      12's Makefile (calls python3; builds its unshipped article.tex)
code/05-ranks-ordinals.py                   12's ordinal engine (below epsilon_0)
code/05-ranks-heights.py                    12's heights, CNF refinement, point ranks, checker
code/05-ranks-check_certificate.py          12's command-line certificate checker
code/05-ranks-verify.py                     12's suite (63,270 assertions recorded)
data/05-ranks-verification.json             12's recorded run (delivered at its root)
data/05-ranks-quality_assurance.json        12's delivery record (delivered at its root)
data/05-ranks-{complete_two_levels,finite_top,mixed_CNF,persistent,point_rank,
      transfinite_exponent,weighted_N,weighted_N_three_terms}.json   12's eight inputs (delivered in examples/)
data/05-ranks-{same eight names}_certificate.json                     12's eight certificates (delivered in examples/)
```

The directory holds 112 files: 24 of Part I and 18, 22, 23 and 25 staged from
07, 09, 11 and 12. Every staged file is byte-identical to its delivery.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex article.tex` three times; build in a scratch copy so that no
auxiliary files land here. BibTeX is not needed: `article.tex` inputs
`references.tex`, and `references.bib` repeats the same nine entries for
reuse; keep the two consistent when editing. The shipped PDF was built with
MiKTeX with no errors, no undefined or multiply defined references and no
overfull boxes. `build.py --verify` first runs Part I's `code/verify.py` in
place, which rewrites `data/verification.json` and `data/poset_census.csv`;
use it only on a copy.

## Rerun the suites

Every suite rewrites its own evidence files under its delivered names, so run
it on a copy, never here. Python 3.10 or later, standard library only; the
recorded runs used Python 3.13.5. The delivered Makefiles call `python3`,
which may hit the Windows app alias; use `py` (or `python3` elsewhere). From
this directory, in Git Bash or another POSIX shell, with `W` a scratch
directory outside the repository:

```sh
W=/path/to/scratch

# Part I (original layout)
mkdir -p "$W/01" && cp -r code data build.py "$W/01/"
(cd "$W/01" && py code/verify.py)

# 07 (02-retire-): delivered layout Makefile, code/, data/
mkdir -p "$W/07/code" "$W/07/data"
cp code/02-retire-Makefile "$W/07/Makefile"
for f in code/02-retire-*.py; do cp "$f" "$W/07/code/${f#code/02-retire-}"; done
for f in data/02-retire-*; do cp "$f" "$W/07/data/${f#data/02-retire-}"; done
(cd "$W/07" && py code/verify.py)

# 09 (03-wpo-): delivered layout Makefile, build.py, DELIVERY_CHECKS.json, code/, data/, examples/
mkdir -p "$W/09/code" "$W/09/data" "$W/09/examples"
cp code/03-wpo-Makefile "$W/09/Makefile"
cp code/03-wpo-build.py "$W/09/build.py"
cp code/03-wpo-frontier_heights.py "$W/09/code/frontier_heights.py"
cp code/03-wpo-verify.py "$W/09/code/verify.py"
cp data/03-wpo-DELIVERY_CHECKS.json "$W/09/DELIVERY_CHECKS.json"
for n in height_two_overlap limit_fibers nonuniform_N parallel_chains \
         persistent_large_coordinate transfinite_exponent_labels; do
  cp "data/03-wpo-$n.json" "$W/09/examples/$n.json"
  cp "data/03-wpo-${n}_certificate.json" "$W/09/data/${n}_certificate.json"
done
for n in examples_summary.json verification.json run_output.txt; do
  cp "data/03-wpo-$n" "$W/09/data/$n"
done
(cd "$W/09" && py code/verify.py)

# 11 (04-peel-): delivered layout build.py, code/, data/, examples/
mkdir -p "$W/11/code" "$W/11/data" "$W/11/examples"
cp code/04-peel-build.py "$W/11/build.py"
for n in check_local_ranks ordinals persistent_height verify; do
  cp "code/04-peel-$n.py" "$W/11/code/$n.py"
done
for n in N_high_a N_high_b empty mixed_successor_product persistent_large_coordinate \
         single_impure successor_product transfinite_exponents uniform_N weighted_N; do
  cp "data/04-peel-$n.json" "$W/11/examples/$n.json"
done
for n in examples_results.json local_rank_console.txt local_rank_verification.json \
         package_quality.json verification.json verification_console.txt; do
  cp "data/04-peel-$n" "$W/11/data/$n"
done
(cd "$W/11" && py code/verify.py && py code/check_local_ranks.py)

# 12 (05-ranks-): delivered layout Makefile, verification.json, quality_assurance.json, code/, examples/
mkdir -p "$W/12/code" "$W/12/examples"
cp code/05-ranks-Makefile "$W/12/Makefile"
for n in check_certificate heights ordinals verify; do
  cp "code/05-ranks-$n.py" "$W/12/code/$n.py"
done
cp data/05-ranks-verification.json "$W/12/verification.json"
cp data/05-ranks-quality_assurance.json "$W/12/quality_assurance.json"
for f in data/05-ranks-*; do
  n=${f#data/05-ranks-}
  case "$n" in verification.json|quality_assurance.json) ;; *) cp "$f" "$W/12/examples/$n";; esac
done
(cd "$W/12" && py code/verify.py)
```

These recipes were run on 28 September 2026 (Python 3.14.4): all five suites
passed with the recorded counts, and every regenerated file equals its shipped
counterpart apart from Windows line endings, except the five ledgers (Part
I's `data/verification.json`, 07's `verification_results.json`, and the
`verification.json` of 09, 11 and 12), which differ only in interpreter
version and elapsed time. Part I's suite recorded 216,386 assertions. Individual examples
then run as in the delivered READMEs, inside the copy, for example
`py code/retirement.py data/limit_fibres.json` (07),
`py code/frontier_heights.py examples/limit_fibers.json` (09),
`py code/persistent_height.py examples/successor_product.json` (11) and
`py code/heights.py examples/point_rank.json` (12). An input with a
`generators` field asks 12's program for a point rank; 11's point-rank API is
`exact_point_rank` in `persistent_height.py`. Do not use the `pdf` or `all`
Makefile targets or the `build.py` helpers of 09 and 11: they build the
delivered manuscripts, which are not shipped (11's helper would also write
`_build/` and `article.pdf` in its directory).

## Discrepancies and delivery names

- **Delivery names.** The staged scripts, Makefiles, audits and source records
  still use the delivered paths: `code/verify.py`, `examples/*.json`,
  `data/*.json`, and, for 12, `verification.json` and `quality_assurance.json`
  at the package root. They also name the manuscripts' `article.tex`,
  `article.pdf` and `README.md`, which are not shipped. The recipes above
  recreate those paths in a copy. Part II's text quotes the shipped names.
- **Delivery records describing unshipped PDFs.** `data/03-wpo-DELIVERY_CHECKS.json`
  records 09's 26-page PDF and the SHA-256 values of 09's `article.pdf` and
  `article.tex` (both verified at placement); neither file is shipped.
  `data/05-ranks-quality_assurance.json` and `data/04-peel-package_quality.json`
  record the 23-page PDFs of 12 and 11 and their inspection, also not shipped.
- **Duplicate.** `data/03-wpo-run_output.txt` is byte-identical to
  `data/03-wpo-verification.json`: 09's verifier prints the ledger it writes.
- **New files from the CLIs.** 09's README suggests
  `--output data/rebuilt_N_certificate.json`, and 12's `--output result.json`;
  both write new files. 09's command-line certificate lacks the
  `compressed_frontier_count` and `maximal_antichain_chain` fields that its
  verifier adds to `nonuniform_N_certificate.json`.
- **Stale statements in Part I's delivered files.** `data/weighted_N_result.json`
  and `data/mixed_height_counterexample_result.json` say "No nonuniform height
  formula is asserted."; `PROOF_AUDIT.md` says there is "no nonuniform height
  formula here" and that its nonuniform counterexample "shows what fails when
  the largest coordinate persists". These predate the addition and stay
  byte-identical; Parts II–III now give that formula. Likewise
  `data/quality_assurance.json` records the original 20-page PDF; the
  current `article.pdf` has 73 pages.
- **Label conventions in data.** The inputs number vertices from 0. 09's
  `nonuniform_N` input has edges `0<2, 0<3, 1<3`, its own labelling of the
  N-poset (`a<c, a<d, b<d`), the mirror image of the article's `a<c, b<c, b<d`
  under `a<->b, c<->d`; the inputs of 07, 11 and 12 use the article's
  orientation (`0<2, 1<2, 1<3`).
- **Cross-check not shipped.** The placement commit reports a 152-instance
  comparison of all four programs with no disagreement; that script is not in
  this directory.
- **Bibliography.** 11 cited Vialard's lexicographic-product paper by the
  author's publication page only; the article uses Part I's published record
  with its DOI.

## Relation to neighbouring reports and to the formal project

- [`intrinsic-ordinal-approximations`](../intrinsic-ordinal-approximations/)
  proves `h(P_f(lambda + F)) = lambda + |F|` for a limit `lambda` and a finite
  cap `F` (its Theorem `thm:caps`). That is a special case of Theorem 22.2 here,
  and its Remark 8.2 (label `ioa:rem:nonuniform-heights`, added in batch 36)
  says so. Its table `tab:products` computes `h(P_f(product))`, the finitary
  powerset *of* a Cartesian product, which is a different object from
  `h(K(disjoint union)) = h(product of (1 + alpha_i))` here: for two `omega+1`
  factors the values are `omega^2+1` there and `omega*2+1` here.
- [`ordinal-order-maps-and-grids`](../ordinal-order-maps-and-grids/) computes
  heights of `K(alpha x P)` for Cartesian products, a different construction.
- [`hoare-powerspace-statures`](../hoare-powerspace-statures/) concerns
  topological statures of Noetherian spaces; 09 inspected it and found it a
  different subject (Problem 37.8 asks whether a topological version exists).
- The report sits in the research-report collection of the `SetTheory/Cardinals`
  Lean project. That placement confers no formal status: no Lean declaration
  anywhere in ProveIt formalizes any statement of Parts I–III. Sections 25 and
  36 record the formalization routes the sources propose; none has been started.
