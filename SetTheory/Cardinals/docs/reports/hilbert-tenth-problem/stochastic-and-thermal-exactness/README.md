# Stochastic and Thermal Exactness

**Diophantine certificates for exact events in uniformly convergent systems: positive stochastic erasure, exact value iteration of stochastic games, thermal Hamiltonians with undecidable confinement boundaries, positive mixing realizations of polynomials, and coercive Green operators**

This is a research report dated 2 October 2026, built from six manuscripts:
three of batch 78 (cluster H2) and three of batch 79 (cluster J3) of
ProveIt's incoming reports. All six are AI-assisted research manuscripts
prepared for Vladimir Reshetnikov. The batch-78 ones are called *source 02*,
*source 10* and *source 03* after their batch-78 manuscript numbers. The
batch-79 ones are called *source 11*, *source 12* and *source 13* after the
next free file prefixes of this report, in the order of their Parts.

**Watch the numbering.** Source 10 (Part II) is batch-78 manuscript 10.
Batch-79 manuscript 10 is *source 12* (Part V); batch-79 manuscript 12 is
*source 11* (Part IV); batch-79 manuscript 14 is *source 13* (Part V).

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 02 (base) | batch 78, manuscript 02 | `ProveIt_Exact_Erasure_Research.zip` (`1977e6ea6`); *Exact Erasure without a Common Invariant Line: Positive stochastic computation, tensor guards, and Diophantine certificates*, main file `exact_erasure_research/article.tex`, 29-page PDF | `928ea9701` | `798b0c5d4` | Part I (Sections 2–16) and Appendices A–B |
| 10 | batch 78, manuscript 10 | `ProveIt_Exact_Convergence_Research.zip` (`808b53ed8`); *Exact Convergence as Computation: Diophantine Certificates for Uniformly Mixing Stochastic Games*, main file `Exact_Convergence_Research/article.tex`, 24-page PDF | `297eb58e4` (see below for its unpinned README read) | `798b0c5d4` | Part II (Sections 17–30) and Appendices C–D |
| 03 | batch 78, manuscript 03 | `Thermal_Arithmetic_Diophantine_Hamiltonians.zip` (`1977e6ea6`); *Thermal Arithmetic: Diophantine Witnesses, Effective Excited Spectra, and Undecidable Confinement Boundaries*, main file `thermal_arithmetic/article.tex`, 25-page PDF | `6914ccca6`; blob `8bd07142` of `imported_substrate_review_20261002.md` | `798b0c5d4` | Part III (Sections 31–41) and Appendix E |
| 11 | batch 79, manuscript 12 | `Mixing_Does_Not_Remove_Arithmetic.zip` (`ef2fc7990`); *Mixing Does Not Remove Arithmetic: Optimal Positive Markov Realizations of Diophantine Predicates*, main file `Mixing_Does_Not_Remove_Arithmetic/article.tex`, 24-page PDF | `44983ed7e` | `bbaf322e5` | Part IV (Sections 42–54) and Appendices G–H |
| 12 (base of Part V) | batch 79, manuscript 10 | `Coercive_Green_Diophantine.zip` (`ef2fc7990`); *Coercive Linear Algebra as a Universal Computational Substrate: Canonical Quasi-Diophantine Certificates, Rational Green Functions, and Uniformly Shunted Resistor Networks*, main file `Coercive_Green_Diophantine/article.tex`, 22-page PDF | `44983ed7e` | `bbaf322e5` | Part V.A (Sections 55–69) and Appendices I–J |
| 13 | batch 79, manuscript 14 | `Well_Conditioned_Diophantine_Computation.zip` (`ef2fc7990`); *Well-Conditioned Diophantine Computation: Connected Resistor Networks, Compact Support, and a Prime-Localization Barrier*, main file `well_conditioned_diophantine/article.tex`, 26-page PDF | `44983ed7e` | `bbaf322e5` | Part V.B (Sections 70–81) and Appendices K–L |

Author lines, kept in the Part openings: source 02 "Research report prepared
for Vladimir Reshetnikov / Mathematical development and implementation:
ChatGPT"; source 10 "Prepared for Vladimir Reshetnikov / Mathematical
development and exact-arithmetic implementation: ChatGPT"; source 03
"Research report prepared for Vladimir Reshetnikov" (no assistant named; its
provenance note says the files were "authored for this request"); source 11
"Research note prepared with ChatGPT / For the ProveIt computational-substrate
research program"; source 12 "Research report prepared for Vladimir
Reshetnikov" (no assistant named); source 13 "Research manuscript prepared for
Vladimir Reshetnikov / Mathematical development and reference implementation:
ChatGPT" (PDF metadata "ChatGPT; prepared for Vladimir Reshetnikov").

Every result, proof, example, remark, limitation, research question and
appendix of the six manuscripts is printed. Sources 02, 10 and 03 share no
theorem, and none cites another. Sources 12 and 13 prove **one theorem by two
routes**, written independently from the same snapshot: source 12 is printed
first as the base, and source 13 follows in full, its shared statements marked
by bracketed pointers to source 12 with its own proofs kept as second routes.
Source 13's connected network answers source 12's own research question "A
connected network with the same exact classification" (dated note in Part V.A).
Source 11 re-uses Part I's doubly stochastic lift (printed as a pointer, no
novelty claimed) and contrasts with Part I's commuting theorem.

All six Parts share one pattern, set out in Section 1.2 (Table 1): an
approximation converges uniformly at a rate known in advance, while an *exact*
event of the same system is undecidable — exact erasure under a uniform
total-variation contraction (Part I), exact arrival of value iteration at a
known fixed point (Part II), the boundary value of a uniformly computable
critical fugacity (Part III), exact arrival of one coordinate at its
equilibrium value under positive commuting mixing (Part IV), and finite support
or rationality of the Green data of a uniformly coercive operator (Part V).

**Status: AI-assisted, unrefereed, not formalized.** Nothing in the report
is formalized in Lean or Rocq, and priority is not certified for any Part.

## Already reviewed in the research programme

The Hilbert's-tenth-problem research programme reviewed five of the six
manuscripts before they were placed here and the sixth (source 11) shortly
after. This report links those reviews and does not present its placement as
a first review.

- Sources 02 and 03:
  [`incoming_substrate_review_1977e6ea6.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_1977e6ea6.md)
  (commit `44b28c395`), sections *Exact erasure* and *Thermal arithmetic and
  its repair*, with its receipt
  [`incoming_substrate_review_1977e6ea6.json`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_1977e6ea6.json)
  (keys `erasure`, `thermal`, `thermal_repair`). It accepts source 02 within
  its stated domains, replays its suite and all eight certificates, adds
  independent checks and finds no defect.
- Source 10:
  [`incoming_substrate_review_808b53ed8.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_808b53ed8.md)
  and its detailed
  [`incoming_convergence_review_808b.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_convergence_review_808b.md)
  (commit `126028588`), with the receipt `incoming_substrate_review_808b53ed8.json`
  (keys `independent.convergence`, `independent.convergence_repairs`,
  `independent.convergence_scale`). It accepts the mathematics and reconstructs
  every coefficient of the three delivered polynomials.
- Sources 12 and 13:
  [`review_coercive_connected_aebfa386e.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_coercive_connected_aebfa386e.md)
  (commit `899391bde`, made shortly before the placement commit `bbaf322e5`),
  with its checker `review_coercive_connected_aebfa386e.py` and receipt
  `review_coercive_connected_aebfa386e.json`. It read every proof of both,
  accepts them within their presentation and domain assumptions, reran both
  suites (110,522 and 38,524 checks) and all five example exports, adds
  independent checks, and finds no defect in source 12. It stresses that the
  exact finite-support witnesses are unbounded arrays, not fixed tuples of
  integer unknowns, and that neither report lowers the 87-operation bound.
- Source 11: inventoried in the byte-pinned intake
  [`incoming_substrate_intake_aebfa386e.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_intake_aebfa386e.md)
  (commit `b927b2290`) and reviewed after placement in
  [`review_mixing_aebfa386e.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_mixing_aebfa386e.md)
  (commit `5b633fcf9`), with checker `review_mixing_aebfa386e.py` and receipt
  `review_mixing_aebfa386e.json`. **PASS, no repair requested.** It read the
  whole manuscript and code, reproduced all fourteen exports byte for byte,
  and reconstructed every coefficient of the fourteen exported polynomials
  from the transition entries in exact `Fraction` arithmetic. It stresses
  limits that the text already states or implies, now summarized in the
  opening of Part IV: the `r(P)+1` bound is not a zero-set lower bound (`x`
  and `x²` need three and four states); the line loader's root correspondence
  needs natural values and an integral `S` (spurious real and signed zeros
  otherwise); the line loader is not an arithmetic saving; Bell–Semukhin's
  binary commuting results are NP-hardness results. The continuing review
  table
  [`incoming_substrate_review_aebfa386e.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_aebfa386e.md)
  lists all three batch-79 reviews as complete (commit `653349f6a`).
- Placement and later work. The programme authenticated all 64 files placed
  by `bbaf322e5` against the six delivered archives, with a stager that
  restores the delivered layouts
  ([`review_placement_bbaf322e5.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_placement_bbaf322e5.md),
  commit `5b633fcf9`). It also emitted complete paid straight-line evaluators
  of source 13's horizon quadratic, factoring the routing cross sum
  (`C = Σ_r (B − b_r) A*_r`; the transfer example at horizon 3 falls from 245
  to 206 operations), with an independent review
  ([`connected_cross_routing_slp.md`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/connected_cross_routing_slp.md),
  `review_connected_cross_routing_slp.md`, commit `9bc875b6a`); these are
  comparisons of emitted evaluators, not a fixed-arity bound (note in Section
  77).

**Defects found by those reviews; the shipped programs are the unpatched originals.**

- *Thermal compiler (source 03).* The ProveIt review of 2 October 2026 found
  that the low-level `Compiler`/`Atom` interface of
  `code/03-thermal-arithmetic-compiler.py` accepts invalid gate descriptors: a
  self-referential gate (`u = x + u`, two zero-energy completions over one
  input, hence an infinite fibre), the non-natural constant
  `Atom('const', 0.5)`, and Boolean atoms. `compile_polynomial` validates its
  input. The theorems assume a natural DAG (gate inputs are natural constants,
  parameters, witnesses or outputs of earlier gates) and are unaffected, but the
  manuscript's sentence "Floats and Boolean values are rejected where exact
  integer inputs are required" is true only of `compile_polynomial`; an
  editorial note says so in Section 38.5. Both behaviours were reproduced on a
  copy of the shipped file at the write. The tested repair is
  [`thermal_exact_dag_guards.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/thermal_exact_dag_guards.patch)
  in the research programme. Whether a later commit installs a patched copy
  here is Vladimir's call; the review's status paragraph would then need an
  update.
- *Bellman checker (source 10).* `code/10-exact-convergence-check_certificate.py`
  replays the trajectory from a scaled initial vector that it does not bind to
  the declared input, so a certificate with altered declared input can still
  report value zero and a successful game check. Repair:
  [`exact_convergence_input_binding.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/exact_convergence_input_binding.patch).
  Editorial note in Section 26.
- *Bellman loader (source 10).* `Program.encode` in
  `code/10-exact-convergence-bellman_diophantine.py` divides an explicitly
  supplied *integer* scale in floating point (counter 1075 becomes `0.0`); the
  default rational scale, used by every shipped export, is exact. Repair:
  [`exact_convergence_integer_scale.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/exact_convergence_integer_scale.patch).
  Editorial note in Appendix D.
- *Connected substrate (source 13).* In
  `code/13-well-conditioned-substrate.py` the frozen `Certificate` keeps
  mutable row dictionaries and `export` returns the same objects (lines
  343–348 and 373–377), so mutating an export erases the live input-binding
  row: in the review's fixture a wrong-input energy changes from 9409 to 0.
  And `set(primes)` runs before the primality checks (lines 285 and 306), so
  `localization_bound(5, [2, 2.0])` accepts an inexact scalar. Neither touches
  the mathematics, the formulas or the shipped exports. Repair:
  [`well_conditioned_certificate_snapshots.patch`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/well_conditioned_certificate_snapshots.patch)
  (SHA-256 `cdd6307d5659ae0c72e7715b72e22e8692b07362d0a0f008f89a9ac85372f2a9`),
  which passes the unchanged 38,524-check suite and reproduces every export.
  Editorial note in Section 79.1.

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 177 pages (unnumbered title page, then pages 1–176)
README.md                                            this guide
02-exact-erasure-PROOF_STATUS.md                     source 02's claims, dependencies, checks and limits, as delivered
02-exact-erasure-SOURCE_AUDIT.md                     source 02's repository reads and primary sources, as delivered
03-thermal-arithmetic-PROVENANCE.md                  source 03's repository snapshot and primary literature, as delivered
10-exact-convergence-PROOF_STATUS.md                 source 10's proof, novelty and implementation status, as delivered
12-coercive-green-SOURCE_AUDIT.md                    source 12's repository snapshot, earlier report and primary literature, as delivered
13-well-conditioned-sources.md                       source 13's pinned repository reads, antecedents and trust boundary, as delivered
code/02-exact-erasure-Makefile                       source 02's make targets (delivered layout; see below)
code/02-exact-erasure-check_certificate.py           source 02's independent residual evaluator (imports no generator code)
code/02-exact-erasure-erasure.py                     source 02's affine and tensor compilers, PCP front end, certificates
code/02-exact-erasure-run_checks.py                  source 02's 50,582-assertion suite and example export (imports erasure, check_certificate)
code/03-thermal-arithmetic-build.sh                  source 03's three-pass pdflatex script (delivered layout; see below)
code/03-thermal-arithmetic-compiler.py               source 03's exact circuit compiler and thermal interval routines (unpatched)
code/03-thermal-arithmetic-verify.py                 source 03's 7,936-assertion suite (imports compiler; needs SymPy 1.14.0)
code/10-exact-convergence-bellman_diophantine.py     source 10's counter-to-game compiler, exact iteration, quadratic certificates (unpatched)
code/10-exact-convergence-build.py                   source 10's test and PDF build driver (delivered layout; see below)
code/10-exact-convergence-check_certificate.py       source 10's independent polynomial and trajectory checker (unpatched)
code/10-exact-convergence-run_checks.py              source 10's 26,077-assertion suite and export of all artifacts
code/11-mixing-arithmetic-build_examples.py          source 11's producer: the fourteen examples and the compiler report (imports mixing_compiler; SymPy)
code/11-mixing-arithmetic-mixing_compiler.py         source 11's SymPy compiler: translation module, embedding, positive lift, loaders
code/11-mixing-arithmetic-reproduce.sh               source 11's POSIX reproduction script (delivered layout; see below)
code/11-mixing-arithmetic-verify_exports.py          source 11's independent Fraction checker (imports neither the compiler nor SymPy)
code/12-coercive-green-green_machine.py              source 12's history lift, sparse operator, certificates, Pell descent, intervals, slices
code/12-coercive-green-verify.py                     source 12's 110,522-check suite in 43 categories (imports green_machine)
code/13-well-conditioned-build.sh                    source 13's verification and PDF script (delivered layout; see below)
code/13-well-conditioned-substrate.py                source 13's counter compiler, connected graph, localization and quadratic APIs (unpatched)
code/13-well-conditioned-verify.py                   source 13's 38,524-assertion suite in 26 groups (imports substrate from src/)
data/02-exact-erasure-check_results.json             source 02's recorded run: 50,582 assertions by category (Python 3.13.5)
data/02-exact-erasure-final_certificate_replay.json  source 02's recorded checker results for its eight certificates
data/02-exact-erasure-pcp_nine_state_certificate.json             full certificate of the PCP example (344 witnesses, 400 residuals)
data/02-exact-erasure-pcp_nine_state_information_certificate.json compressed certificate of the PCP example (276, 324)
data/02-exact-erasure-pcp_nine_state_instance.json   the nine-state, five-letter PCP instance
data/02-exact-erasure-pdf_preflight.json             source 02's record of its own 29-page PDF (not shipped)
data/02-exact-erasure-perturbed_non_erasing_instance.json         an invertible, non-erasing perturbation of the three-state example
data/02-exact-erasure-seven_state_erasure_certificate.json        full certificate of the word (N,N,N) (171 witnesses, 192 residuals)
data/02-exact-erasure-seven_state_information_certificate.json    compressed certificate of the same word (132, 147)
data/02-exact-erasure-seven_state_instance.json      the seven-state, eight-letter instance (392 integer entries)
data/02-exact-erasure-seven_state_uniform_certificate.json        uniform-target full certificate (171, 198)
data/02-exact-erasure-three_state_information_certificate.json    compressed certificate of the three-state example (14, 14)
data/02-exact-erasure-three_state_instance.json      the three-state example of Section 13.1
data/02-exact-erasure-three_state_nonuniform_erasure_certificate.json  full certificate of the word (0,L) (24, 26)
data/02-exact-erasure-three_state_wrong_uniform_target.json       a deliberately wrong uniform-target certificate; the checker must reject it
data/03-thermal-arithmetic-examples.json             six compiled source polynomials with their complete expressions
data/03-thermal-arithmetic-requirements.txt          source 03's pin, sympy==1.14.0
data/03-thermal-arithmetic-verification.json         source 03's recorded run: PASS, 7,936 assertions, rational enclosures
data/03-thermal-arithmetic-verification_console.txt  the console output of that run
data/10-exact-convergence-countdown_game.json        the 128-state absorbing-halt countdown game, reset and input
data/10-exact-convergence-countdown_timeline.json    exact timing and comparison gaps of the countdown run
data/10-exact-convergence-fixedpoint_game.json       the 128-state erasing-halt game with common reward 1/4
data/10-exact-convergence-pdf_preflight.json         source 10's record of its own 24-page PDF (not shipped)
data/10-exact-convergence-small_certificate.json     the 12-witness two-state quadratic and its natural zero
data/10-exact-convergence-small_expanded_quadratic.json  the same polynomial fully expanded (45 monomials)
data/10-exact-convergence-small_game.json            the two-state zero-reward example game
data/10-exact-convergence-verification.json          source 10's recorded run: 26,077 assertions by category (Python 3.13.5)
data/11-mixing-arithmetic-compiler_report.json       source 11's producer report: 14 reverse-polynomial checks, radial ranks, 19 rejections
data/11-mixing-arithmetic-difference_square.json     the four-state realization of (x-y)^2-1 at theta=1/2 (Section 51.1)
data/11-mixing-arithmetic-document_qa.json           source 11's record of its own 24-page PDF (not shipped)
data/11-mixing-arithmetic-factor_family_0.json       the fixed 11-state quadratic-curve family Q_t, input t=0
data/11-mixing-arithmetic-factor_family_1.json       the same family, t=1
data/11-mixing-arithmetic-factor_family_11.json      the same family, t=11
data/11-mixing-arithmetic-factor_family_2.json       the same family, t=2
data/11-mixing-arithmetic-factor_family_6.json       the same family, t=6 (four roots, Section 51.3)
data/11-mixing-arithmetic-factor_line_0.json         the fixed 19-state line-segment family P_t, input t=0
data/11-mixing-arithmetic-factor_line_1.json         the same family, t=1
data/11-mixing-arithmetic-factor_line_11.json        the same family, t=11
data/11-mixing-arithmetic-factor_line_2.json         the same family, t=2
data/11-mixing-arithmetic-factor_line_6.json         the same family, t=6
data/11-mixing-arithmetic-fast_mixing.json           (x-y)^2-1 recompiled at theta=1/100 (four states, q=1/900)
data/11-mixing-arithmetic-independent_report.json    source 11's independent check record (1,310 count vectors, 1,424 words, 269 products)
data/11-mixing-arithmetic-product_graph.json         the five-state realization of xy-z
data/11-mixing-arithmetic-provenance.json            source 11's snapshot, repository sources and primary references
data/11-mixing-arithmetic-radial_quartic.json        the ten-state realization of (x^2+y^2)^2 (rank 9)
data/11-mixing-arithmetic-requirements.txt           source 11's pin, sympy==1.14.0
data/12-coercive-green-countdown.json                source 12's countdown example: table, source, support, witness, slice residuals
data/12-coercive-green-modular_false_positive.json   the characteristic-two false certificate, rejected over the integers
data/12-coercive-green-results.json                  source 12's recorded run: 110,522 checks in 43 categories (Python 3.13.5)
data/13-well-conditioned-countdown_T3_polynomial.json  source 13's horizon-3 countdown quadratic: residuals and 105 expanded monomials
data/13-well-conditioned-countdown_T3_witness.json   its 32-coordinate witness and the eight nonzero network values
data/13-well-conditioned-localization_bounds.json    rank constants, length bounds and finite-prime examples
data/13-well-conditioned-verification.json           source 13's recorded run: 38,524 assertions in 26 groups
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery. Delivered name → shipped name:

- Source 02 (`exact_erasure_research/`): `code/*.py`, `Makefile` →
  `code/02-exact-erasure-*`; `examples/*.json`, `verification/check_results.json`,
  `verification/final_certificate_replay.json`, `verification/pdf_preflight.json`
  → `data/02-exact-erasure-*`; `PROOF_STATUS.md`, `SOURCE_AUDIT.md` →
  `02-exact-erasure-*.md`; `article.tex` → the base of `article.tex` (Part I).
- Source 10 (`Exact_Convergence_Research/`): `code/*.py`, `build.py` →
  `code/10-exact-convergence-*`; `artifacts/*.json` except the two large
  certificates → `data/10-exact-convergence-*`; `PROOF_STATUS.md` →
  `10-exact-convergence-PROOF_STATUS.md`.
- Source 03 (`thermal_arithmetic/`): `compiler.py`, `verify.py`, `build.sh` →
  `code/03-thermal-arithmetic-*`; `examples.json`, `verification.json`,
  `verification_console.txt`, `requirements.txt` → `data/03-thermal-arithmetic-*`;
  `PROVENANCE.md` → `03-thermal-arithmetic-PROVENANCE.md`.
- Source 11 (`Mixing_Does_Not_Remove_Arithmetic/`): `code/*.py`, `reproduce.sh` →
  `code/11-mixing-arithmetic-*`; `examples/*.json` (all fourteen),
  `verification/*.json`, `provenance.json`, `requirements.txt` →
  `data/11-mixing-arithmetic-*`.
- Source 12 (`Coercive_Green_Diophantine/`): `code/*.py` →
  `code/12-coercive-green-*`; `examples/*.json`, `validation/results.json` →
  `data/12-coercive-green-*`; `SOURCE_AUDIT.md` →
  `12-coercive-green-SOURCE_AUDIT.md`.
- Source 13 (`well_conditioned_diophantine/`): `verify.py`, `src/substrate.py`,
  `build.sh` → `code/13-well-conditioned-*`; `examples/*.json`,
  `verification.json` → `data/13-well-conditioned-*`; `sources.md` →
  `13-well-conditioned-sources.md`.

Not shipped: the six PDFs; the delivered READMEs of all six; the manuscripts
of sources 10, 03, 11, 12 and 13 (printed as Parts II–V); the verified
checksum ledgers of source 02 (`verification/SHA256SUMS`, 25 of 25), source 03
(`SHA256SUMS.txt`, 11 of 11), source 11 (`SHA256SUMS.txt`, 26 of 26) and source
13 (`SHA256SUMS`, 11 of 11; sources 10 and 12 shipped none); three in-archive
byte copies, `verification/run_output.txt` of source 02 (= `check_results.json`),
`artifacts/test_run.txt` of source 10 (= `verification.json`) and
`validation/test_output.txt` of source 12 (= `results.json`); and source 10's
two large certificates (next section). All survive in the archives of their
arrival commits: for example
`git show 1977e6ea6:docs/incoming/ProveIt_Exact_Erasure_Research.zip > ee.zip`,
`git show 1977e6ea6:docs/incoming/Thermal_Arithmetic_Diophantine_Hamiltonians.zip > ta.zip`,
`git show 808b53ed8:docs/incoming/ProveIt_Exact_Convergence_Research.zip > ec.zip`,
`git show ef2fc7990:docs/incoming/Mixing_Does_Not_Remove_Arithmetic.zip > mx.zip`,
`git show ef2fc7990:docs/incoming/Coercive_Green_Diophantine.zip > cg.zip` and
`git show ef2fc7990:docs/incoming/Well_Conditioned_Diophantine_Computation.zip > wc.zip`.
Nothing of batch 79 was excluded as heavy: all fourteen of source 11's
examples (the largest 49,283 bytes) are shipped.

## Reconstructing the excluded data

Two certificates of source 10 are not stored here, because the shipped
compiler regenerates them exactly:

| File | Bytes | SHA-256 (delivered, LF) |
|---|---|---|
| `countdown_certificate.json` | 11,921,969 | `7b7ca91f186faa62ace1efb05e767c8d7e39b6242398483c34c8f06fe7063f1e` |
| `fixedpoint_certificate.json` | 21,813,796 | `1dec3a32bf52cd4a5e85678cb7577bec43aedeca5839cb9f0419510a9eb720c0` |

They are the complete horizon-17 scalar-equality quadratic of the countdown
game (2,584 witnesses, 2,381 squared linear forms, 204 products) and the
complete horizon-30 fixed-point quadratic (4,440 witnesses, 4,268 squares,
300 products), in factored form with the dense reset rows expanded.

To rebuild them, recreate the delivered layout in an empty scratch directory
(`run_checks.py` imports `bellman_diophantine` and `check_certificate` by
those names and writes into `artifacts/` beside its own `code/` directory;
standard library only):

```sh
mkdir -p r10/code
cp code/10-exact-convergence-bellman_diophantine.py r10/code/bellman_diophantine.py
cp code/10-exact-convergence-check_certificate.py   r10/code/check_certificate.py
cp code/10-exact-convergence-run_checks.py          r10/code/run_checks.py
cd r10
py code/run_checks.py        # 26,077 assertions; writes r10/artifacts/*.json
py code/check_certificate.py artifacts/countdown_certificate.json  --game artifacts/countdown_game.json
py code/check_certificate.py artifacts/fixedpoint_certificate.json --game artifacts/fixedpoint_game.json
tr -d '\r' < artifacts/countdown_certificate.json  | sha256sum
tr -d '\r' < artifacts/fixedpoint_certificate.json | sha256sum
```

(`py` is the Python launcher on this machine; the delivered texts say
`python`.) `run_checks.py` rewrites every file of `artifacts/`, including
both certificates; there is no command for one certificate alone. The whole
suite took 17 s at placement and 45 s at the write (a loaded machine); each
checker run takes a few seconds and reports value 0 with
`independent_game_check: true`. On POSIX the certificates are byte-identical
to the hashes above; on Windows they are written with CRLF line endings and
match after the `tr -d '\r'` normalization. Both were so reproduced at the
write (Python 3.14.4, Windows), and the other six regenerated exports equal
the shipped `data/10-exact-convergence-*.json` files after the same
normalization; `verification.json` differs only in its `"python"` field.

The delivered files themselves are in the original archive:
`git show 808b53ed8:docs/incoming/ProveIt_Exact_Convergence_Research.zip > ProveIt_Exact_Convergence_Research.zip`
(872,036 bytes), members
`Exact_Convergence_Research/artifacts/countdown_certificate.json` and
`Exact_Convergence_Research/artifacts/fixedpoint_certificate.json`.

## Labels and numbering

Every label carries the prefix `ste:`. Source 02's 86 labels are `ste:ee:`
plus their delivered names, source 10's 65 are `ste:ec:` plus theirs, and
source 03's 55 are `ste:ta:` plus theirs; no source label was dropped or
renamed apart from the prefix. The batch-78 merge added 50 labels, 256 in all:
twelve for the front section, the three Parts and the provenance appendix
(`ste:sec:front`, `ste:sec:parts`, `ste:sec:spine`, `ste:tab:spine`,
`ste:sec:notation`, `ste:tab:notation`, `ste:sec:relation`,
`ste:sec:status`, `ste:part:ee`, `ste:part:ec`, `ste:part:ta`,
`ste:app:provenance`); `ste:ee:q:*` on source 02's nine research questions;
on source 10, `ste:ec:cor:stopping`, `ste:ec:prop:onesided`,
`ste:ec:prop:selectors` and `ste:ec:prop:threshold` for its four unlabelled
statements, `ste:ec:app:audit` and `ste:ec:app:contract` for its appendices
and `ste:ec:q:*` for its seven research directions; on source 03,
`ste:ta:sec:intro`, `ste:ta:sec:gap`, `ste:ta:sec:package`,
`ste:ta:sec:questions`, `ste:ta:app:reproduction`, `ste:ta:q:*` for its ten
research questions and `ste:ta:rem:universalcompact` for the editorial remark
after its finite-fold theorem.

Batch 79 renamed and renumbered nothing: all 256 earlier labels keep their
names and their printed numbers (checked against the `.aux` of the committed
build). Source 11's 62 labels are `ste:mx:` plus their delivered names,
source 12's 85 are `ste:cg:` plus theirs and source 13's 75 are `ste:wc:` plus
theirs. The batch-79 write added 45 labels, **523 in all**: `ste:part:mx`,
`ste:part:cg`, `ste:tab:notation79`, `ste:cg:tab:conventions`,
`ste:app:provenance79`; on source 11, ten section, table and appendix labels
(`ste:mx:sec:intro`, `ste:mx:sec:pointers` for the added subsection
"Second routes and pointers", `ste:mx:sec:lift`, `ste:mx:sec:robust`,
`ste:mx:sec:witnesses`, `ste:mx:sec:implementation`, `ste:mx:sec:questions`,
`ste:mx:tab:examples`, `ste:mx:app:ledger`, `ste:mx:app:provenance`) and
`ste:mx:q:*` on its seven research subsections; `ste:cg:q:*` on source 12's
twelve research subsections; `ste:wc:q:*` on source 13's ten research
questions and `ste:wc:app:archive`. Appendix F lists them all.

Each Part keeps its source's numbering by section: source 02's Section *n* is
Section *n* + 1 (Sections 2–16), source 10's is *n* + 16 (17–30), source 03's
is *n* + 30 (31–41), source 11's is *n* + 41 (42–54), source 12's is *n* + 54
(55–69) and source 13's is *n* + 69 (70–81); so source 10's Theorem 1.1 is
Theorem 17.1 and source 12's Theorem 5.1 is Theorem 59.1. Source 02's
appendices keep their letters A–B, source 10's become C–D and source 03's
becomes E; Appendix F is the provenance; the batch-79 appendices follow it as
G–H (source 11), I–J (source 12) and K–L (source 13), so that A–F kept their
letters. Equations, tables and figures are numbered through the report.
Text written in the merges is marked `[write]`; text without a marker is the
source's own.

## Setting and notation

No symbol was renamed and no normalization changed; each Part keeps its own
letters. Table 2 (Section 1.3) lists every letter used differently in Parts
I–III, among them `N`, `K`, `D`, `M`, `T`, `H`, `Q`, `L`, `R`, `P` and `η`
(for example, `K` is source 02's lift scale, source 10's layer normalizer, and
in source 03 both the halting set `𝖪` and a compact remainder operator).
Table 8 (opening of Part IV) does the same for Parts IV and V, and Table 10
(opening of Part V) compares sources 12 and 13 notion by notion. Watch for
these readings:

- **Erasure.** In Part I a word *erases* when its stochastic product has rank
  one (one common output distribution, not necessarily uniform). In Part II the
  *erasing map* and *erasing halt convention* send a halted computation to the
  zero vector; the event observed there is attainment of the fixed point
  `½·1`. Same word, unrelated notions. Part IV's "no word erases" is Part I's
  notion (for doubly stochastic products rank one means the product is `J_s`),
  and it never happens there.
- **Uniform** means different things: Part I's uniform erasing word (target
  `J_n`) and uniform switching; Part II's uniformly mixing rows and uniform
  reset; Part III's uniformly computable reals.
- **Contraction / confinement.** Part I contracts total variation; Part II the
  supremum norm; Part III has no dynamics, and its confinement is the spectral
  bound `H > 0 ⇒ H ≥ 1 + Σ n_i`; Part IV contracts total variation by `θ` per
  letter; Part V has a uniformly bounded inverse, not a dynamics.
- **Stochastic convention.** Part I uses column-stochastic matrices on column
  distributions; Part IV row distributions (`M_w = J_s + q^L F A_w E`, the roles
  of `E` and `F` transposed with respect to Part I's lift).
- **`A`, `J`, `m`, `q`.** In Part IV `A_i` are unipotent translation matrices
  and `J_s` the averaging matrix; in Part V.A `A` is the adjacency and `L_α`
  the operator; in Part V.B `A = A_m = mI − J` is the operator and `J` the
  adjacency. Source 12's `m` counts branches, source 13's `m` is the diagonal
  (source 12's `α`). Part IV's `q` is a transient eigenvalue, source 13's `q`
  an integral charge (source 12's `c`).
- **Test instructions.** Source 12's `TEST(i, p₊, p₀)` lists the positive
  branch first; source 13's `TEST(j, q₀, q₊)` lists the zero branch first.
  Source 12's histories start at 0, source 13's at 1.
- **Green value and resistance.** Source 12's `g_α(s)` is a one-terminal root
  value; source 13's `R_x` is a two-terminal resistance, `2·g_L` on halting
  inputs and `m − √(m² − 4)` otherwise.
- **Certificate.** Parts I and II are horizon-indexed (arity grows with `T`);
  Part III's Hamiltonian has a fixed number of modes; Part IV's witness is the
  count vector itself; Part V's linear certificate is an unbounded
  finite-support array, its ordinary quadratics having a supplied support
  (source 12) or a supplied horizon (source 13). None is a fixed-arity
  single-fold representation of a c.e.-complete set.
- **Fugacity, thermal** are mathematical parameters; no physical system is
  assumed. Likewise Part V's resistor networks are countable, finitely
  presented objects, not finite circuits.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 02).** A positive affine lift of integer affine data into
  strictly positive rational column-stochastic matrices in any band
  `((1−η)/n, (1+η)/n)`, with `TV(S_w p, S_w q) ≤ η^T TV(p,q)`; a two-guard
  tensor compiler with no common invariant complex line and
  `rank S_w = 1 + 2 rank A_π(w)`; hence undecidable rank-one existence for at
  most eight positive 7×7 matrices (from the imported (3,6) mortality bound)
  and, through a printed four-dimensional PCP front end with an idempotent
  connector, many-one completeness for a nine-state family with variable
  alphabet; r-fold guards excluding invariant subspaces of dimensions
  1,…,r−1; an exact dimension correspondence with mortality; a sharp `n−1`
  horizon for commuting induced matrices; a zero–one law (erasing word ⇔
  a.s. finite erasure ⇔ finite expected erasure time); full and
  mass-compressed horizon-T natural quartics with `T((n−1)²+k)` witnesses and
  `T((n−1)²+1)+(n−1)²` residuals, word-bijective (44T and 37T+36 at n=7,
  k=8); a uniform-input quartic schema; no computable horizon; non-erasing
  subspace-preserving perturbations.
- **Part II (source 10).** A compiler from counter programs to homogeneous
  dyadic min/max circuits and then to genuine two-player stochastic games
  with paired channels, an initialized cyclic pipeline, an erasing halt and a
  common uniform reset; a fixed game with discount 1/2, reward 1/4, at most two
  actions per state and all probabilities ≥ 1/(2N), whose exact fixed-point
  attainment from dyadic terminal payoffs is c.e.-complete; zero-reward
  scalar-equality, consensus and strict-inequality variants; decidable
  point-mass and chance-only boundaries; a dyadic full-support Skolem
  specialization (credited to Vahanwala); horizon-T orthant-nonnegative
  quadratics with exactly one complete natural witness, `(N+2b)T` witnesses,
  `(N+b)T+e` squares and `bT` products; no computable cutoff.
- **Part III (source 03).** A witness-faithful degree-five diagonal
  Hamiltonian `H = (1+Σn_i)Q` with `m = k+g+1` modes, `r = g+2` residuals,
  `H > 0 ⇒ H ≥ 1+Σn_i` and `r(m+1)` four-mode positive terms; its
  self-adjoint realization, effective positive-energy layers, compact and
  trace-class remainders with explicit tails; dim ker H = number of witnesses,
  and compact resolvent ⇔ trace-class heat operator ⇔ finite multiplicity; a
  spectral form of finite-fold representability; undecidable compactness on a
  padded universal family; computable regulated partition functions and an
  analytic-continuation promise problem; a uniformly computable critical
  fugacity `t_*` with `c ∈ K ⇔ t_* < 1`; height bounds; no computable cutoff.
- **Part IV (source 11).** For a nonzero rational polynomial `P` with
  translation rank `r(P)`, an effective realization by `s = r(P)+1` states,
  one accepting state, a strictly positive initial row and commuting,
  invertible, strictly positive doubly stochastic rational matrices in any
  band `((1−θ)/s, (1+θ)/s)`, with acceptance `1/s + ε q^{|n|} P(n)` and a
  total-variation contraction `θ^L`; optimality of `r(P)+1` for the exact
  centered series; the sharp quartic budget `s ≤ C(k+3,2)` (attained by
  `(Σx_i²)²`) and a quintic bound; a fixed alphabet with the input on a
  rational quadratic Bézier curve (joint nilpotence depth ≤ 4) or a rational
  line segment (depth ≤ 5) whose exact equilibrium hit is c.e.-complete;
  strict-cutpoint and fixed-initial-state variants; the converse class
  `C_d` ⇔ natural solvability of one polynomial of degree ≤ d; a
  nonnormality obstruction; decidable separated targets; no computable
  horizon; explicit examples (4, 5, 10, 11 and 19 states).
- **Part V (sources 12 and 13).** A branch-history lift of counter machines
  to a computable path forest; for every integer `α ≥ 3` the operator
  `L_α = αI − A` with `(α−2)I ≤ L_α ≤ (α+2)I` and a polynomial-time
  approximable inverse; a unique normalized integer certificate
  `L_α u = c e_s`, `H(u) = 1`, with `c = D_n` and continuant coefficients,
  exactly on halting sources (over every torsion-free ring); Green value
  `D_{n−1}/D_n` or `(α − √(α²−4))/2`; three c.e.-complete sets; the Pell
  classification `q² + p² − αpq = 1` of the rational values; polynomial-time
  decidability of each rational level; polynomial-time intervals; no
  computable cutoff; a linear polynomial-functional presentation; exact
  quadratic finite slices with complete boundary rows; resistor-network and
  killed-walk readings; a positive-characteristic obstruction. Source 13, by
  its own route: a connected computably presented graph of maximum degree
  three with operator `5I − J`, `2I ≤ A ≤ 8I`, and dipole sources, with the
  same equivalences, least charge `D_L` and support `2L`; resistance
  `2D_{L−1}/D_L` versus `5 − √21`; undecidable attainment of a strongly
  convex energy on finite-support arrays; decidable membership over
  `Z[S⁻¹]` for every finite prime set (odd `m`), with an explicit length
  bound; four nonzeros per row optimal for fixed connected scalar operators;
  the positivity obstruction; a horizon-T natural quadratic with one complete
  witness, `(d+3)(T+1)+1+T((d+1)R+Z)` witnesses.

Credit and pointers (printed as `[write]` notes naming the host labels, no
novelty claimed): the circuit core of Part III's compiler and the fixed-arity
quartic corollaries of Parts I and II are `cdc:wf:lem:quadratization` of
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)
(and `pqc:lem:quarticlower`), and so is Part IV's gate front end; the
no-cutoff clauses of all five Parts are `cdc:bd:prop:nobound`; Part III's
finite-fold theorem follows `cdc:cs:thm:finitefold`; Part II's
complementarity gadget specializes `pqc:pm:lem:clamp` / `pqc:pm:thm:trace`;
Part I's (3,6) bound is also credited to Neary (STACS 2015, Cor. 12), as Part
II of `probabilistic-quantum-and-continuous-computation` does; Part IV's lift
is Part I's doubly stochastic lift (`ste:ee:cor:double`) and its binomial step
`cdc:pt:prop:unipotent`; source 13's horizon quadratic is a variant of the
degree-two counter compilers `lbh:qd:thm:compiler` / `lbh:ql:thm:compiler` of
[`liveness-beyond-halting`](../liveness-beyond-halting) and of
`cdc:eq:bigM`; source 13's statements shared with source 12 are pointers to
Part V.A.

The report does **not** claim:

- priority for any Part (all six sources say their searches were targeted,
  and sources 11–13 credit commuting probabilistic-automaton undecidability,
  Hankel-rank minimality, stochastic embeddings, inverse systems, history
  recording, inverse decay and the network–walk correspondence to the
  literature), refereeing, or any Lean/Rocq verification; the finite checks
  (50,582, 26,077 and 7,936 assertions; 110,522 and 38,524 checks; source 11's
  1,310 count vectors, 1,424 words and 269 nilpotence products) illustrate
  and do not prove;
- an improvement of the repository's 75-operation complete-certificate or
  87-operation universal-polynomial records; no numerical universal polynomial,
  stochastic alphabet, game or network is instantiated;
- a finite-fold or single-fold Diophantine representation; bounded certificates
  have horizon-dependent or support-dependent arity, MRDP's fixed-arity
  quartics leave witness multiplicity uncontrolled, Part IV keeps the
  multiplicity of the MRDP representation it starts from, and Part V's
  witnesses are unbounded finite-support arrays;
- Part I: irreducibility (a common invariant hyperplane remains); one fixed
  alphabet with an ordinary input loader; many-one completeness of the
  eight-letter bound; anything about undecidable hidden-Markov output entropy;
  optimality of any count. Its headline claim to answer the restriction raised
  in MathOverflow question 511960 rests on an external discussion that this
  repository does not archive; it is reported as the manuscript's claim;
- Part II: a numerical universal game (the 128-state games are one-counter
  examples); hardness of value iteration from zero or of solving discounted
  games; a resolution of Skolem or of the one-player Bellman frontier;
  robustness to perturbed tables or floating point;
- Part III: a resolution of the finite-fold problem; physical
  hypercomputation or autonomous dynamics; a numerical mode count for the
  universal family; that `t_*` is noncomputable (it is computable; its exact
  endpoint is undecidable); geometric locality; robustness to coefficient
  errors;
- Part IV: a printed universal alphabet (the shipped examples are
  illustrative; the universal theorems import MRDP); a lower bound for the zero
  set alone or for noncommuting or differently encoded competitors;
  undecidability of a supplied word's acceptance; a decision for single
  cubics (only a reduction); autonomous Turing simulation by a finite chain;
  any procedure using physical noise, sampling or finite-precision
  measurement; an arbitrary preassigned `q` near 1 at no cost; the constants
  `q = 1/18`, `ε = 1/8` and the printed matrices are those of the shipped
  compiler's basis, not invariants (an independent lift at placement had
  `q = 3/56` with the same four states);
- Part V: a new ordinary universal integer-polynomial bound or a fixed-arity
  ordinary compiler for the sparse witness; a finite physical halting oracle;
  polynomial-time neighbour exploration in source 13's connected graph (only
  computability); a decision theorem for arbitrary equations over `Z[S⁻¹]`
  (the localization theorem is family-specific and concerns the unit-source
  solution; arbitrary charge is universal); a uniform algorithm deciding the
  graph type in the row-three theorem; validity in positive characteristic;
  universality of restricted reversible two-counter models; optimality of the
  quadratic counts; individual novelty of undecidable rationality of
  computable reals, reversible simulation or path continued fractions.

## Research questions answered across the report

- Part I's question "Fixed-alphabet universality with an ordinary input
  interface" (`ste:ee:q:fixedalphabet`): **answered for the exact-hit
  predicate**, at MRDP existence level, by Part IV (fixed alphabet, input on a
  quadratic curve or a line segment, or a unary prefix); still open for
  rank-one erasure and without a printed numerical alphabet (dated note there).
- Part I's question "Precision-sensitive versus robust observation
  predicates" (`ste:ee:q:robust`): one case settled by Part IV's separated-target
  cutoff; zero-separation targets can stay c.e.-complete (dated note).
- Part I's question on structural non-erasure certificates: Part IV's
  alphabets are an instance of the invertible class (dated note).
- Source 12's question "A connected network with the same exact
  classification" (`ste:cg:q:connected`): **answered by source 13**
  (`ste:wc:lem:antisym`, `ste:wc:thm:main`), with a signed dipole source; a
  nonnegative source is impossible (`ste:wc:prop:positive`).

## Relation to neighbouring reports and to the formal project

This report is a sibling of
[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)
(cited by label names; Section 1.4):

- Part II there (quantum mortality, `pqc:qm:thm:47`) runs the same pipeline as
  Part I's seven-state corollary for a different exact predicate; its
  nonnegative-mortality boundary `pqc:qm:prop:nonnegative` does not transfer to
  rank one, which bears on Question `pqc:q:signed`.
- Part V there: source 13's Boolean energy landscape `pqc:ql:thm:compiler`
  (which treats no Gibbs distribution) is the bounded counterpart of Part III;
  source 17 (*Arithmetic of Rapidly Mixing Reversible Computation*) has Part
  II's slogan for stationary laws, is cited by source 13 here as an
  antecedent, and bears on Part IV's nonnormality obstruction and on source
  12's question on uniform killing.
- Part VII there: Part II here is the real, order-preserving counterpart of
  source 12's exact extinction (`pqc:ad:cor:complete`) and explains source 14's
  decidable point reachability (`pqc:sc:thm:main` (iii)) by its non-erasable
  clock; it answers Part VII's unlabelled question "Structural subclasses"
  negatively in part (the one-player case stays open). Parts IV and V here have
  Part VII's slogan for other objects.
- Parts VIII and IX there: `pqc:tu:cor:fixedquartic` (cited by Part III) and
  `pqc:iq:thm:geometric` (related to Part I's zero–one law).
- Part IV here bears on `pqc:q:signed` and `pqc:q:promise`.

[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)
supplies the re-proved results listed above and the degree floor
`cdc:of:thm:classification`, which makes radial isolation below degree four
impossible for a universal family (note in Section 39.1).
[`liveness-beyond-halting`](../liveness-beyond-halting) has no overlap with
Parts I–III; source 13's horizon quadratic is a variant of its counter
compilers (pointer in Section 77). Batch-79 manuscript 01, which sources 12
and 13 cite as *Linear Quasi-Diophantine Universality*, was placed by
`224ca41df` in
[`polynomial-witness-histories`](../polynomial-witness-histories), to be
printed there with the prefix `pwh:bt:`; that report was not yet written at
this write, so Part V cites it by report name only. Its regime is the opposite
one (a dense nonclosed range instead of a bounded inverse).
[`group-theoretic-substrates`](../group-theoretic-substrates) and
[`signal-machine-collision-certificates`](../signal-machine-collision-certificates)
have no overlap. The research note
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/matrix_pcp_trace.md`
uses the same radix-three PCP tiles as Part I's front end, without its fourth
coordinate and idempotent connector.

**The formal project.** The report sits in the collection, not in
`Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
development confers no formal status**. The sources import MRDP only as a
classical theorem; sources 10 and 13 name the project's interface
`Diophantine.mrdp`, `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
(`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33, 42,
26; blob unchanged from both pins to the write), and source 13 also
`re_tm0` in `Lean/Diophantine/Paper1980/TuringPartrec100.lean` (unchanged).
The project has formalized none of this report's statements: it has no
stochastic-matrix, stochastic-game, Bellman-operator, occupation-number
Hamiltonian, Markov-realization, Hankel-rank, coercive-operator,
Green-function or resistor-network module.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
microtype, booktabs, longtable, enumitem, fancyhdr, needspace, listings,
xurl, hyperref, bookmark, bm, tabularx, TikZ). The committed build has 177
pages: no LaTeX warnings at all (no undefined references or citations, no
multiply defined labels, no duplicate destinations), no overfull boxes, and
six underfull lines (badness at most 2799), all in batch-78 text (three
`[write]` notes and the bibliography) and identical to the committed build
before batch 79.

## Rerunning the programs

Every suite imports its companion modules by their delivered names and
writes into delivered paths: source 02's `run_checks.py` rewrites
`examples/*.json` and `verification/check_results.json` under its parent
directory; source 10's `run_checks.py` rewrites every file of `artifacts/`;
source 03's `verify.py` rewrites `examples.json` and `verification.json` in
its own directory; source 11's `build_examples.py` rewrites `examples/` and
`verification/compiler_report.json` and its `verify_exports.py` rewrites
`verification/independent_report.json`, all under their parent directory;
source 12's `verify.py` rewrites `examples/` and `validation/results.json`
under its parent directory; source 13's `verify.py` rewrites `examples/` and
`verification.json` in its own directory. On Windows all of them write CRLF
line endings, while the shipped files are LF. **Never run them in place.**
Recreate the delivered layout in a scratch directory:

```sh
# source 02 (standard library only)
mkdir -p r02/code
cp code/02-exact-erasure-erasure.py           r02/code/erasure.py
cp code/02-exact-erasure-check_certificate.py r02/code/check_certificate.py
cp code/02-exact-erasure-run_checks.py        r02/code/run_checks.py
cd r02 && py code/run_checks.py && cd ..      # 50,582 assertions; writes r02/examples, r02/verification
py r02/code/check_certificate.py data/02-exact-erasure-seven_state_information_certificate.json
py r02/code/check_certificate.py data/02-exact-erasure-three_state_wrong_uniform_target.json   # must exit 1

# source 10: see "Reconstructing the excluded data" above

# source 03 (needs SymPy 1.14.0)
mkdir -p r03
cp code/03-thermal-arithmetic-compiler.py r03/compiler.py
cp code/03-thermal-arithmetic-verify.py   r03/verify.py
cd r03 && uv run --no-project --with sympy==1.14.0 python verify.py && cd ..

# source 11 (build step needs SymPy 1.14.0; the checker needs only the standard library)
mkdir -p r11/code r11/verification
cp code/11-mixing-arithmetic-mixing_compiler.py r11/code/mixing_compiler.py
cp code/11-mixing-arithmetic-build_examples.py  r11/code/build_examples.py
cp code/11-mixing-arithmetic-verify_exports.py  r11/code/verify_exports.py
cd r11
PYTHONUTF8=1 uv run --no-project --with sympy==1.14.0 python code/build_examples.py   # writes r11/examples (14), r11/verification/compiler_report.json
PYTHONUTF8=1 py code/verify_exports.py                                                # "all checks passed"; writes r11/verification/independent_report.json
cd ..

# source 12 (standard library only)
mkdir -p r12/code
cp code/12-coercive-green-green_machine.py r12/code/green_machine.py
cp code/12-coercive-green-verify.py        r12/code/verify.py
cd r12 && py code/verify.py && cd ..          # 110,522 checks; writes r12/examples, r12/validation/results.json

# source 13 (standard library only)
mkdir -p r13/src
cp code/13-well-conditioned-verify.py    r13/verify.py
cp code/13-well-conditioned-substrate.py r13/src/substrate.py
cd r13 && py verify.py && cd ..               # 38,524 assertions; writes r13/examples, r13/verification.json
```

To check source 11's *shipped* examples without SymPy, copy the fourteen
example files (not the three reports, `provenance.json` or
`requirements.txt`, since the checker reads every `examples/*.json`) under
their delivered names into `r11/examples/` and run only
`verify_exports.py`; the delivered names are the shipped ones without the
`11-mixing-arithmetic-` prefix (`difference_square`, `fast_mixing`,
`product_graph`, `radial_quartic`, `factor_family_{0,1,2,6,11}`,
`factor_line_{0,1,2,6,11}`).

The checkers of sources 02 and 10 only read the certificate they are given, so
they may be pointed at the shipped `data/` files. At the batch-78 write
(Python 3.14.4, Windows, `PYTHONUTF8=1`) the first three suites passed: source
02 with 50,582 assertions, its 12 regenerated examples equal to the shipped
files after CRLF→LF and its check results differing only in `"python"`, and the
wrong uniform target rejected (exit 1); source 10 as described above; source 03
with 7,936 assertions, both JSON files and the console output equal to the
shipped ones after CRLF→LF. At the batch-79 write the recipes for sources 11,
12 and 13 were run on copies (Python 3.14.4, SymPy 1.14.0, Windows): source
11's build took about 6 s and reproduced all fourteen examples and its
compiler report after CRLF→LF, and its checker reported status "all checks
passed" in about 26 s (about 2 min on the loaded machine at placement) and
reproduced `independent_report.json` after CRLF→LF; source 12 passed with 110,522 checks, both
examples equal after CRLF→LF and `results.json` differing only in
`"python"`; source 13 passed with 38,524 assertions, its three examples and
`verification.json` equal after CRLF→LF.

Do not use the delivered build drivers here: `code/02-exact-erasure-Makefile`,
`code/03-thermal-arithmetic-build.sh`, `code/10-exact-convergence-build.py`,
`code/11-mixing-arithmetic-reproduce.sh` and `code/13-well-conditioned-build.sh`
assume the delivered layout (they run their suites by delivered names, the
last two with `python`/`python3`, and run pdflatex or latexmk on an
`article.tex` beside them; source 10's driver also writes
`artifacts/test_run.txt` and `build_logs/`); none of them builds this report.
Use the build command above.

## Discrepancies and disclosures

- **Source 10's unpinned README read.** Its bibliography linked the project
  README through `/blob/main/`, and its Appendix A (Appendix C here) records
  blob `880d2a13`. That blob is the README introduced by `db3b377f0` and
  replaced by `b7a9404d4`, both after the pin `297eb58e4` used for its other
  two repository reads (whose README blob is `138f234b`). Both versions state
  the 75- and 87-operation figures it quotes. A `[write]` note in Appendix C
  says so; the merged bibliography entry records all the sources' reads of
  that README.
- **Delivered names in delivered text.** `02-exact-erasure-PROOF_STATUS.md`
  names `verification/check_results.json` and `verification/pdf_preflight.json`;
  `10-exact-convergence-PROOF_STATUS.md` names `artifacts/verification.json`
  and calls the main theorem "Theorem 1.1" (Theorem 17.1 here);
  `03-thermal-arithmetic-PROVENANCE.md` names `article.tex`, `compiler.py`,
  `verify.py`, "the two JSON files and the console receipt" and the PDF;
  `data/02-exact-erasure-final_certificate_replay.json` names
  `examples/*.json`; both `pdf_preflight.json` files and
  `data/11-mixing-arithmetic-document_qa.json` describe the sources' own PDFs,
  which are not shipped; `data/11-mixing-arithmetic-provenance.json` names the
  delivered files of source 11; `12-coercive-green-SOURCE_AUDIT.md` and
  `13-well-conditioned-sources.md` name their delivered layouts and earlier
  manuscripts by delivered title. The Parts' reproduction sections and code
  listings keep the delivered layout; `[write]` notes give the shipped names.
- **Excluded certificates named in text.** Part II (Section 26) and source
  10's delivered texts name `countdown_certificate.json` and
  `fixedpoint_certificate.json`, which are not stored here; see
  "Reconstructing the excluded data".
- **Source 03's build note.** Its reproduction appendix (Appendix E) shows two
  pdflatex passes; `build.sh` runs three (`[write]` note there). Its PDF
  metadata used the subtitle *Diophantine Witnesses and Undecidable Confinement
  Boundaries*; the printed subtitle is used here.
- **Source 12's code conventions.** Its delivered README notes that the code
  numbers the registers 0 and 1 (1 and 2 in the article) and calls the scalar
  `c` `q` (note in Section 67.2). Its delivered README speaks of "twelve
  further research directions"; Section 68 indeed has twelve.
- **Source 11's constants.** `q = 1/18`, `ε = 1/8` and the printed matrices of
  Section 51.1 depend on the compiler's choice of basis (note there).
- **Wording corrected by editorial brackets, not in the source text.** Part I's
  "the fixed seven-state undecidable family" (Section 11.2) means the
  seven-state, at-most-eight-letter promised class of input-dependent
  alphabets, not one fixed alphabet. Part III's statement that floats and
  Booleans are rejected holds for `compile_polynomial` only (above).
- **External claims not checkable here.** Source 02's MathOverflow question
  511960 and its June 3 comment; sources 12 and 13 cite earlier manuscripts
  from "the supplied research corpus" or "the user's Library", identified here
  as batch-79 manuscript 01 and as source 17 of the probabilistic report; the
  published literature cited by the six sources was not re-read at the writes.
- **Typography.** The six delivered title pages are replaced by one title
  page (its vertical spacing was tightened in batch 79 so that the longer
  abstract still fits on one page); each source's title, subtitle, author line and abstract (with source
  11's status box, source 12's keywords and reading guide and source 13's
  keywords) open its Part. Source 02's remarks used the definition style; all
  remarks now use the remark style. Source 12's New TX fonts are replaced by
  Latin Modern; source 13's `\cref` references are written out; the
  inner-product and norm macros of sources 11–13 print with this report's
  definitions. The bibliographies are merged (key mapping in Appendix F).
