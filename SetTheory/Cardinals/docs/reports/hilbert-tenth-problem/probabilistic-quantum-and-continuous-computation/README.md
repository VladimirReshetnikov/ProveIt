# Diophantine Laws of Probabilistic, Quantum and Continuous Computation

**Normalization budgets and unique quartic certificates, four-dimensional quantum mortality, and a continuous three-outcome trichotomy**

This is a research report dated 30 September 2026, built from three
manuscripts of batch 60. All three were prepared for Vladimir Reshetnikov;
manuscripts 08 and 09 name ChatGPT as the author of the mathematical
development and code, and manuscript 07 describes itself as a research
manuscript with reproducible exact-arithmetic artifacts.

| Source | Batch 60 | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 08 (base) | manuscript 08 | `ProveIt_Diophantine_Quantum_Normalization` (*Diophantine Laws of Probabilistic Computation: optimal normalization budgets, unique quartic certificates, and quantum computational substrates*, 29-page Letter PDF) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Section 1, Part I (Sections 3–9), Sections 11–12 of Part II, Section 33, its parts of Sections 34–37, Appendices A.1 and D |
| 07 | manuscript 07 | `quantum_diophantine_research` (*Rational Gram Packing, Four-Dimensional Quantum Mortality, and Diophantine Certificates*, 22-page A4 PDF) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Sections 13–22 of Part II, its parts of Sections 1 and 34–37, Appendix A.2 |
| 09 | manuscript 09 | `ProveIt_Diophantine_Barriers` (*Diophantine Barriers for Continuous Computation: a three-dimensional trichotomy, finite quartic certificates, and a computable critical-noise radius*, 26-page Letter PDF, main file `diophantine_barriers.tex`) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Part III (Sections 23–32), its parts of Sections 1 and 34–37, Appendices B, C and E |

Every result, proof, example, remark, research question and limitation of
the three manuscripts is printed. The three share no theorem, so nothing is
printed twice and there are no second routes. **The report is AI-assisted
and unrefereed, and none of its theorems is formalized in Lean or Rocq.**

```
article.tex                                           the report, standalone LaTeX with an internal bibliography
article.pdf                                           the compiled report, 87 pages (unnumbered title page,
                                                      contents pages 1-5, then pages 6-86)
README.md                                             this guide
07-quantum-mortality-STATUS.md                        source 07's verification and dependency status, as delivered
09-continuous-barriers-PROVENANCE.md                  source 09's repository inspection, sources and claim boundaries, as delivered
code/07-quantum-mortality-Makefile                    source 07's make targets (pdf, check, clean), delivered paths
code/07-quantum-mortality-quantum_diophantine.py      source 07's exact matrix arithmetic, Gram factors, instrument and certificate compiler
code/07-quantum-mortality-run_checks.py               source 07's checks (32,418 assertions); writes examples/ and verification/
code/08-probabilistic-laws-Makefile                   source 08's make targets (test, pdf, clean), delivered paths
code/08-probabilistic-laws-normalization.py           source 08's exact budget evaluator and quartic compiler
code/08-probabilistic-laws-prefix_allocator.py        source 08's labelled prefix (Kraft) allocation
code/08-probabilistic-laws-quantum_exact.py           source 08's exact Clifford+T amplitudes and state vectors (at most 16 qubits)
code/08-probabilistic-laws-verify.py                  source 08's checks (SymPy); writes artifacts/
code/09-continuous-barriers-barriers.py               source 09's exact grid, bottleneck, cut and TM-to-PWA compiler
code/09-continuous-barriers-run_checks.py             source 09's checks (5,660 assertions); writes to the directory named, default results/
data/07-quantum-mortality-build_summary.json          source 07's record of its 22-page PDF build
data/07-quantum-mortality-check_results.json          source 07's recorded run: 32,418 checks in 26 categories
data/07-quantum-mortality-four_dimensional_instrument.json  the seven integer numerator matrices of Section 19 (denominator 15)
data/07-quantum-mortality-quartic_D2_K2_n2.json       the expanded (D,K,n)=(2,2,2) quartic: 647 monomials, 44 witnesses, 50 residuals
data/07-quantum-mortality-zero_word_witness.json      the canonical assignment for the zero word (2,1,1), 245 witnesses
data/08-probabilistic-laws-HTH_prefix_allocation.json the 12-stage prefix allocation of the HTH output law
data/08-probabilistic-laws-normalization_quartic_N2_m2.json  the N=2, m=2 residual system, variable order and assignment
data/08-probabilistic-laws-normalization_quartic_N2_m2.txt   the same quartic expanded (165 monomials)
data/08-probabilistic-laws-pdf_preflight.json         source 08's check of its 29-page PDF
data/08-probabilistic-laws-requirements.txt           source 08's pin, sympy==1.14.0
data/08-probabilistic-laws-source_manifest.json       source 08's pin and bibliography record (no hashes)
data/08-probabilistic-laws-verification.json          source 08's recorded run (Python 3.13.5, SymPy 1.14.0)
data/09-continuous-barriers-contraction_table.json    the rational enclosures of Table 1
data/09-continuous-barriers-small_certificate.json    the five-vertex safety certificate of Section 32
data/09-continuous-barriers-small_quartic.txt         its factored quartic
data/09-continuous-barriers-verification.json         source 09's recorded run: 5,660 assertions in 20 categories
```

The delivered READMEs and PDFs of the three manuscripts are not shipped: this
README replaces them, and `article.pdf` is a build of the merged text.
07's and 09's manuscripts and READMEs survive in the arrival commit
`ccfb084ad` (inside the zips), as do all three PDFs; 08's delivered
`article.tex` and `README.md` are also the versions of these two files in
the placement commit `7498484af`. Every other delivered
file is shipped under the prefixed name above, **byte-identical to the
delivery**; the delivered paths and the files whose text still uses them are
listed under *Delivered names* below.

## Labels and numbering

Every label in `article.tex` carries the prefix `pqc:`. Source 08's 74
labels are `pqc:` + the delivered name, source 07's 64 are `pqc:qm:` + the
delivered name, and source 09's 87 are `pqc:cb:` + the delivered name (225
delivered labels, none dropped; the delivered clashes `thm:quartic`,
`eq:mrdp`, `eq:quartic` (07/09), `thm:universal`, `eq:terminal`,
`sec:questions` (08/09) and `eq:canonical`, `sec:quartic` (07/08) are
removed by the prefixes). Writing the report added 33 labels: `pqc:conv`,
`pqc:conv:*` (15), `pqc:part:*` (4), `pqc:app:provenance`,
`pqc:qm:rem:chainformal`, and eleven research-question labels `pqc:q:*`
(6), `pqc:qm:q:*` (3), `pqc:cb:q:*` (2) — 258 labels in all, counted with
`\label(\[[^]]*\])?\{`. Eight delivered section labels whose headings were
rewritten (`sec:audit`, `sec:questions` and `app:archive` of 08,
`sec:implementation`, `sec:future` and `app:contracts` of 07,
`sec:questions` and `sec:examples` of 09) sit on the corresponding merged
headings. The 46 labels
of lemmas, propositions, corollaries, definitions, examples and remarks
carry cleveref type hints (`\label[lemma]{…}`), because these environments
share the theorem counter and 09's `\cref` would otherwise print every one
of them as "theorem". No `pqc:` label has a Lean mapping.

Numbering: source 08's Section *n* is Section *n* + 1 here for *n* = 2–8
(Part I), and its Sections 9, 10, 11 are Sections 11, 12, 33; source 07's
Section *n* is Section *n* + 12 (*n* = 1–10); source 09's Section *n* is
Section *n* + 22 (*n* = 1–10, its §10.1 only). Numbered statements keep
their position inside a section: 08's Theorem 5.1 is Theorem 6.1 here,
07's Theorems 4.1, 6.2 and 9.1 are Theorems 16.1, 18.2 and 21.1, and 09's
Theorem 6.1 is Theorem 28.1. Equations are numbered by section in the
same way, except that 09's equation (1.1), in its repository baseline, is
printed in Section 1.2 and numbered there. Research questions 1–12 are 08's, 13–22 are
07's (posed as subsections there) and 23–32 are 09's. Text added in writing
the report is marked `[write]`.

## Setting and notation

Witnesses are natural numbers, polynomials have integer coefficients and
subtraction is signed; a residual system's single equation is the sum of
squares of its residuals (Section 2.1). Section 2.3 tabulates the letters the
three sources use differently that are most easily confused — `N` (horizon /
common denominator / mesh), `m`, `K`, `k`, `D`, `H`, `A`, `B`, `T`, `S`,
`μ`, `δ`, `α`, `β`, `L`, `Q`, `R`, `G`, `ρ` — states the tempting false
readings, and names the purely local ones. Each Part keeps its
source's letters. Renamed (Section 2.4; no normalization changed):

| Here | Source | Where | Reason |
|---|---|---|---|
| `R(σ,τ)`, `R_s` | 08: `K(σ,τ)`, `K_s` | Section 12 and research question 6 | 07's outcome count `K`; shows the specialization to Part I's `R_s` |
| `G_s` | 08: `H_s` | Section 12 | 07's numerator matrices `H_j` and 08's Hadamard gate `H`; specializes to Part I's `G_s` |
| `S_𝓜`, `t_𝓜` | 07: `S`, `T` | Section 16.1 | the `S` and `T` gates of Section 11 |
| `\cenum` | 09: `\ce` ("computably enumerable") | Part III | 08's `\ce` is "c.e."; printed words unchanged |
| `\code` | three definitions | everywhere | unified as a breakable typewriter path |

## What the report claims

All with ordinary proofs in the article, modulo the named external inputs.

**Part I (manuscript 08).** A discrete subprobability law is the output law of
a fair-coin program iff it is uniformly left-c.e. (Theorem 4.2); one fixed
quartic `U` represents every effective output law as a sum of dyadic masses
of prefix-free projected roots, with no finite-fold hypothesis (Theorem 4.3,
by MRDP), and strict thresholds `bμ_e(z) > a` are Diophantine (Corollary
4.5). A positive probability history is realizable from initial mass `δ` iff
`δ G_s ≤ 1` for every checkpoint, `G_s` the product of the largest
coordinate ratios, with a unique pointwise minimal realization (Theorem 5.2).
For fixed horizon `N` and `m` labels an explicit quartic `F_{N,m}` with
`5Nm + m + 4N + 3` natural witnesses and `5Nm + m + 6N + 4` squared residuals
has a witness iff a valid input is feasible, exactly one witness then, and
none on invalid inputs (Theorem 6.1; 33 witnesses and 38 residuals at
`N = m = 2`, 165 expanded monomials). Total variation of a feasible history
is at most `log(1/δ)`, and at most `½ log(1/δ)` from a balanced binary start,
with `½` sharp (Proposition 7.1, Theorem 7.2). Conditional two-outcome
probabilities with any success floor below one are exactly the weakly
computable reals, with probability-one return exactly the computable reals
(Theorems 8.2, 8.4). Unconditional comparisons with an interior rational are
`Σ⁰₁`/`Π⁰₁`/`Σ⁰₂`/`Π⁰₂`-complete as tabulated in Theorem 9.1; strict conditional
comparisons are `Σ⁰₂`-complete at every success floor below one (Theorem
9.2), and `Σ⁰₁`/`Π⁰₁`-complete promise problems under almost-sure return
(Proposition 9.4).

**Part II (manuscripts 08 and 07).** Finite Clifford+T circuit probabilities
are decidable by exact integer arithmetic and have quartic representations
(Proposition 11.1); every effective measured quantum program's terminal
classical output law has the fixed-quartic projected-root form (the
corollary in Section 11.2). The operator accumulation cost is the product of
max-relative-entropy factors, with the same feasibility criterion, data
processing and trace-variation bound (Theorem 12.1, Corollary 12.2). For
rational `d×d` matrices `M_1, …, M_k`, packing the rows of a rational Gram
factor of `c²I − ΣM_iᵀM_i` across the active Kraus operators gives an exactly
normalized rational instrument with `k+1` outcomes in dimension
`d + ⌈s/k⌉` that is mortal iff the matrices are, with shortest witness
length raised by at most one (Theorem 16.1); `s = d+3` (Meyer) and `s = 4d`
(Lagrange) give Corollary 16.2, and `d+3` is the least uniform rational row
bound (Proposition 15.5). With Neary's six-generator `3×3` mortality theorem
(imported, Theorem 18.1): deciding whether a seven-outcome rational `4×4`
instrument has a nonempty zero-probability word is undecidable (Theorem
18.2), in dimension five without Meyer (Corollary 18.3), with no computable
bound on the shortest such word (Corollary 18.4). For fixed length `n` an
explicit quartic has natural solutions in bijection with the zero words,
`nK + (4n+2)D²` witnesses and `n(K+1) + (4n+3)D²` residuals, i.e. `71n + 32`
and `72n + 48` for `D = 4`, `K = 7` (Theorem 21.1, Corollary 21.2); a
companion quartic certifies nonzero words (Proposition 21.3); MRDP gives a
fixed polynomial for the unbounded set, whose complement is not Diophantine
(Theorem 22.1). Probability gaps `δ_n = 1/(DN^{2n})` and a `2nε`
perturbation bound (Propositions 20.1, 20.2); nonnegative mortality is
decidable (Proposition 22.3).

**Part III (manuscript 09).** The critical per-step noise radius of a
continuous rational piecewise-affine map with Lipschitz bound `L` is within
`(L+1)/(2N)` of a finite grid bottleneck, independently of time, so it is a
computable real (Theorem 25.1); bottleneck/cut duality (Theorem 26.1) gives
explicit quartics `Q_N` in Boolean cut variables that are complete for
positive radius (Theorem 26.2), and MRDP a fixed polynomial (Theorem 26.3).
One fixed continuous rational PWA map `F: [0,1]³ → [0,1]³` with a fixed
target box realizes every disjoint pair of c.e. sets as exact acceptance and
positive radius, the rest being noise-fragile divergence (Theorem 28.1),
with the time–radius sandwich of Corollary 28.4; the three outcome sets are
`Σ⁰₁`-, `Σ⁰₁`- and `Π⁰₁`-complete (Theorem 29.1), the two positive ones
recursively inseparable (Theorem 29.3), the third not existential
Diophantine (Corollary 29.2); there is no computable positive gap, mesh,
certificate-length or witness-height bound (Theorem 30.1, Proposition 30.2,
Corollary 30.3). A noise-faithful retract transfer (Theorem 31.1) and a
rational recurrent ReLU block realizing `F` (Corollary 31.2, using the
max–min representation theorem); an explicit unattained critical radius
`(1−a)b` (Proposition 32.1).

## What the report does not claim

- **No formalization.** No new Lean or Rocq proof was compiled and no
  proof-assistant axiom audit was run for any result here; the three
  formalization sections (35.1–35.3) are plans, and 09's proposed
  `RobustReachability` module names are not repository declarations.
- **No explicit universal polynomial.** None of the fixed MRDP polynomials
  (Theorems 4.3, 22.1, 26.3, Corollary 29.2) is expanded, and none has a
  stated degree, witness count or multiplicity. The explicit polynomials are
  the size-indexed families `F_{N,m}`, `𝒬_{D,K,n}` and `Q_N`; their sizes may
  not be transferred to the fixed-arity polynomials (Remark 2.1).
- **No single-fold or finite-fold MRDP result.** `N` and `m` in Theorem 6.1,
  and `n` in Theorem 21.1, index families of polynomials; no general
  finite-fold or single-fold question is assumed or settled. The
  output-law formula counts projected events, not witnesses.
- **External inputs are imported, not proved:** MRDP; Neary's
  six-generator `3×3` mortality theorem (STACS 2015, Corollary 12); Meyer's
  theorem (via Hasse–Minkowski); Lagrange's four-square theorem; the
  existence of a binary universal Turing machine; the max–min representation
  theorem (ReLU corollary only). Established ingredients (Kraft allocation,
  weak computability and its variation characterization, max-relative
  entropy and its data processing, exact Clifford+T arithmetic, bottleneck
  duality, Moore's generalized shifts, the robustness-implies-decidability
  phenomenon of Bournez–Graça–Hainry) are credited and not advertised as
  new.
- **No priority, optimality or minimality.** Literature searches were
  targeted, not exhaustive. 07 does not claim to have discovered quantum
  undecidability (Eisert–Müller–Gogolin 2012 did, in dimension fifteen) or
  that dimension four with seven outcomes is optimal; Proposition 15.5 is
  about arbitrary positive forms, not the special residual forms. 09 claims
  no minimal dimension, optimal Lipschitz constant, optimal degree or network
  size, and does not claim continuous universality or
  robustness-implies-decidability as its own.
- **Nonuniformity and promises.** The high-success realization of Theorem 8.2
  chooses a late small-variation tail nonuniformly (Remark 8.3); the
  conditional-comparison bounds use syntactically floor-guaranteeing wrapper
  families or are promise statements; endpoint thresholds are not read off
  the interior tables.
- **Semantics.** The operator theorem concerns accumulation of returned
  subnormalized ensembles, not unitary state trajectories, and does not
  compile matrix sequences into circuits. The quantum output-law corollary is
  not an efficient classical simulation. Theorem 18.2's input is the
  instrument's description, not one fixed programmable device, and the
  perturbation estimate is not a uniform experimental procedure. Part III's
  noise is adversarial, per step, in the sup norm after each full update
  (for the ReLU block: at the three recurrent outputs only); hidden-neuron
  noise, parameter errors, stochastic noise, floating-point hardware and
  continuous-time flows are different models. A certified lower radius
  guarantees avoidance only for errors strictly below it.
- **Finite checks are not proofs.** 07's 32,418 and 09's 5,660 assertions and
  08's exhaustive, sampled and symbolic checks test the implementations; 08's
  binary-sharpness diagnostics use floating point and are illustrative; 08's
  quadratic-field sign cross-check uses high-precision `Decimal` as an
  oracle. 07's `gram_search` with a height cap raising `TimeoutError` is not
  evidence that a factor does not exist, and the search is not a practical
  number-theory algorithm. 09 ships no universal interpreter table, ReLU
  weight list or MRDP polynomial, and its grid routine cannot verify a
  Lipschitz bound for an arbitrary Python callable.

## Relation to the formal project and to neighbouring reports

The report continues the Lean project `Computability/HilbertTenthProblem`
only through MRDP: its fixed-arity statements use `Diophantine.mrdp`,
`Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
(`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`) as a
mathematical interface, and source 07 names `Diophantine.boundedForall_dioph`,
`Diophantine.exactIter_dioph` and `Diophantine.existsExactIter_dioph`
(`.../Lean/Diophantine/Common/DiophantineTrace.lean`) as an alternative
route. These assert that representations exist and say nothing about how
many witnesses they have. **None of the report's own theorems is
formalized**, and placement beside a Lean project confers no formal status.
Part II's undecidability in dimension four rests on Neary's published
theorem that mortality of six integer 3×3 matrices is undecidable (STACS
2015, Corollary 12) and on Meyer's theorem. ProveIt keeps Neary's paper
(`Computability/HilbertTenthProblem/Lean/LIPIcs.STACS.2015.649.pdf`) and
formalizes only the binary-tag layer of his construction — the
track-and-shift simulation after his Lemma 9 (`TagBinary91.lean`), the
universality `Jones1980.tag91_re` (`TagUniversal91.lean`) and the
undecidability of the encoded tag family `Jones1980.tag91_undecidable`
(`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/TagDecide91.lean`);
see the Neary rows of `Computability/HilbertTenthProblem/Lean/STATUS.md`
(lines 416–418) — not the Post-correspondence or matrix-mortality steps
(Section 1.3 and Remark 22.2 of the article). Lagrange's theorem is in
Mathlib as `Nat.sum_four_squares`. Nothing under `Computability/` changed
between the pin `f608f1cb3` and the placement commit, so the sources'
descriptions of the repository are current. None of the report concerns
the project's operation counts of straight-line universal certificates.

The sibling report
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates/README.md),
merged from batch 60's manuscripts 01–06, treats witness-faithful
(single-fold, bijective) certificates of **discrete** executions; it shares
no theorem with this one. Its equivalence between single-fold (finite-fold)
universal halting polynomials and the open single-fold (finite-fold)
representability problem is the frontier that research questions 10 and 19
here ask about (Section 36.4). Research question 11's continuous-time
robustness part is answered for discrete-time rational PWA maps by Part III
and re-scoped there.

## Build

TeX Live or MiKTeX with lmodern, amsmath/amssymb/amsthm, mathtools,
mathrsfs, microtype, booktabs, longtable, array, enumitem, tabularx, xcolor,
fancyhdr, listings, TikZ, xurl, hyperref and cleveref. No external figures,
bibliography database or downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 87 Letter pages, with no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull boxes; there are eight
underfull boxes, all in narrow table cells. All fonts are embedded Type 1.
Source 07's `data/07-quantum-mortality-build_summary.json` and source 08's
`data/08-probabilistic-laws-pdf_preflight.json` describe the delivered 22-
and 29-page PDFs, which are not shipped; 07's `STATUS.md` and 09's
`PROVENANCE.md` likewise report builds and page inspections of their own
PDFs. These production checks do not verify the mathematics.

## Rerunning the checks

The programs import each other by their delivered module names and write
into delivered directories, so **run them on a copy with the delivered
layout, never in this directory** (a run here would fail to import, and the
07 and 08 scripts would create `examples/`, `verification/` or `artifacts/`
beside the shipped data). From this directory:

```sh
# 07: Python 3.10+, standard library only; do not use python -O (checks use assert)
mkdir -p /tmp/r07/code
for f in quantum_diophantine run_checks; do cp code/07-quantum-mortality-$f.py /tmp/r07/code/$f.py; done
(cd /tmp/r07 && python code/run_checks.py)      # writes examples/*.json, verification/check_results.json

# 08: Python 3.10+ and SymPy 1.14.0
mkdir -p /tmp/r08/code
for f in normalization prefix_allocator quantum_exact verify; do cp code/08-probabilistic-laws-$f.py /tmp/r08/code/$f.py; done
(cd /tmp/r08 && uv run --no-project --with sympy==1.14.0 python code/verify.py)   # writes artifacts/

# 09: Python 3.10+, standard library only
mkdir -p /tmp/r09/code
for f in barriers run_checks; do cp code/09-continuous-barriers-$f.py /tmp/r09/code/$f.py; done
(cd /tmp/r09 && python code/run_checks.py results)   # writes results/
```

Compare `/tmp/r07/examples/<f>.json` and `/tmp/r07/verification/check_results.json`
with `data/07-quantum-mortality-<f>.json`, `/tmp/r08/artifacts/<f>` with
`data/08-probabilistic-laws-<f>`, and `/tmp/r09/results/<f>` with
`data/09-continuous-barriers-<f>`. Rerun on 30 September 2026 (07 and 09
with Python 3.14.4, 08 with Python 3.13.5 and SymPy 1.14.0): all three
passed (32,418, all of 08's checks, 5,660), and every rewritten file equals
the shipped one apart from line endings — the scripts use `write_text`, which
writes CRLF on Windows — and 07's `runtime_seconds`. 08's report records the
running interpreter's version (`sys.version`), so another Python changes that
field. The seeds are fixed at 20260930.

The delivered Makefiles (`code/07-quantum-mortality-Makefile`,
`code/08-probabilistic-laws-Makefile`) name delivered paths (`article.tex`,
`code/run_checks.py`, `code/verify.py`); they work only in a copy of the
delivered layout, and their `pdf` targets would build the delivered
manuscript, which is not shipped (in this directory they would build the
merged report instead). 08's `clean` target deletes `article.aux`,
`article.log`, `article.out`, `article.toc` and `code/__pycache__`.

Small API examples from the delivered READMEs, run from the copies above:

```python
# in /tmp/r07 — words are chronological: (i, j) is A[j] @ A[i]; label 0 is the idle outcome
import sys; from fractions import Fraction; sys.path.insert(0, "code")
from quantum_diophantine import signed_example, build_certificate, canonical_assignment
inst = signed_example()
assert inst.probability((2, 1)) == Fraction(64, 50625) and inst.probability((2, 1, 1)) == 0
N, H = inst.integer_numerators(); assert N == 15
cert = build_certificate(d=4, k=7, n=3)
assert (len(cert.witnesses), len(cert.residuals)) == (245, 264)
assert cert.value(canonical_assignment(H, (2, 1, 1))) == 0
```

```python
# in /tmp/r08 — the code indexes coordinates from 0, the article from 1
import sys; sys.path.insert(0, "code")
from normalization import optimal_budget, make_assignment, numeric_residuals, compile_system
m0, pivots, factors = optimal_budget([[1, 1], [2, 1], [1, 1]])
assert str(m0) == "1/2" and pivots == [1, 0]
assert all(r == 0 for r in numeric_residuals(make_assignment([[1, 1], [2, 1], [1, 1]], 1, 2), 2, 2))
s = compile_system(2, 2); assert (len(s.witnesses), len(s.residuals)) == (33, 38)
```

```python
# in /tmp/r09/code — the contraction example of Section 32 (true radius 3/8)
from fractions import Fraction as F
from barriers import Box, make_grid_graph, bottleneck, safety_certificate
g = make_grid_graph(lambda p: (p[0] / 2,), (F(0),), [Box((F(3, 4),), (F(1),))], mesh=4, lipschitz=F(1, 2))
r = bottleneck(g.weights, g.source, g.targets)
assert r == F(1, 2) and safety_certificate(g) == (1, 1, 0, 0, 0)   # interval [5/16, 1/2]; the cut alone certifies 3/16
```

For large `N` and `m`, work with 08's residual circuit rather than
expanding the polynomial; 07's full four-dimensional certificate is likewise
checked in residual form. 09's reference graph code refuses more than 2,000
vertices by default.

## Delivered names

Delivered path → shipped path (all byte-identical):

| Source | Delivered | Shipped |
|---|---|---|
| 07 | `Makefile`, `code/quantum_diophantine.py`, `code/run_checks.py` | `code/07-quantum-mortality-<name>` |
| 07 | `examples/<f>.json` (3), `verification/build_summary.json`, `verification/check_results.json` | `data/07-quantum-mortality-<f>.json` |
| 07 | `verification/STATUS.md` | `07-quantum-mortality-STATUS.md` |
| 08 | `Makefile`, `code/<f>.py` (4) | `code/08-probabilistic-laws-<name>` |
| 08 | `artifacts/<f>` (5), `requirements.txt`, `source_manifest.json` | `data/08-probabilistic-laws-<f>` |
| 08 | `article.tex`, `README.md` | merged into `article.tex`; README replaced |
| 09 | `code/barriers.py`, `code/run_checks.py` | `code/09-continuous-barriers-<name>` |
| 09 | `results/<f>` (4) | `data/09-continuous-barriers-<f>` |
| 09 | `PROVENANCE.md` | `09-continuous-barriers-PROVENANCE.md` |

Shipped files whose text still uses delivered names or names unshipped
files: `07-quantum-mortality-STATUS.md` (`code/run_checks.py`,
`check_results.json`, its 22-page PDF and contact sheets);
`09-continuous-barriers-PROVENANCE.md` (`results/verification.json`, "the
TeX/PDF"); both Makefiles (above); `data/08-probabilistic-laws-source_manifest.json`
(`article.tex` of source 08 and `artifacts/verification.json`);
`data/08-probabilistic-laws-normalization_quartic_N2_m2.txt` ("the JSON
file", its sibling `.json`); `data/07-quantum-mortality-build_summary.json`
and `data/08-probabilistic-laws-pdf_preflight.json` (the unshipped PDFs); and
every Python program (delivered module names and output directories).
`data/08-probabilistic-laws-requirements.txt` is the generic one-line
`sympy==1.14.0` file that occurs elsewhere in the repository.

In the article the file names were changed to the shipped names; 08's
archive table (Appendix A.1) and 07's and 09's reproduction paragraphs
(Appendix A.2, Section 34.4) were rewritten for them.

## Provenance and merge choices (Appendix F)

- **Base 08**: its framework (effective output laws of classical and quantum
  programs) contains 07's quantum setting as one kind of program; 09 is a
  separate spine. 08's order is kept, except that its quantum front end and
  operator budget (its Sections 9–10) open Part II beside 07 rather than
  closing Part I.
- 07's and 09's repository paragraphs are printed in Section 1.2; the rest of
  their introductions opens their Parts. 09's reading guide is adapted to the
  merged numbering. Implementation, formalization, questions and conclusions
  of all three are printed side by side (Sections 34–37). The three abstracts
  and status statements are printed in Sections 1.5–1.6.
- New text: Sections 1.3, 1.5, 1.6, 2, 10, 36.4 and Appendix F, the
  title-page abstract and status, Remarks 2.1 and 22.2, the remark at the end
  of Section 33, Section 34.6, the lead paragraphs of Sections 35 and 36 and of
  Appendix A.1, and the rewritten reproduction paragraphs.
- Research questions: all 32 are printed by source; Section 36.4 records the
  overlaps (08's Q10 and 07's Q19 are one frontier; 08's Q9, 07's Q18, 09's
  Q23 ask for three different fixed polynomials; 08's Q2 and 07's Q17 for
  smaller explicit quartics) and re-scopes 08's Q11, partly answered by Part
  III for discrete time.
- Bibliography: merged (21 entries). 07's and 08's `matiyasevich` are
  different works (1993 book, 1971 paper) and both are kept (07's as
  `matiyasevich-book`); 07's entry for ProveIt's `MRDP.md` is kept apart from
  08's for `MRDP.lean`; 09's two repository citations at the moving `main`
  branch now point to these pinned entries, with 09's note that the guide was
  modified on 24 September 2026.
- Placement commit `7498484af` staged the delivered files; this report was
  written from them and from the pristine manuscripts in `ccfb084ad`.
