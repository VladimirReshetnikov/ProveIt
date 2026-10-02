# Stochastic and Thermal Exactness

**Diophantine certificates for exact events in uniformly convergent systems: positive stochastic erasure, exact value iteration of stochastic games, and thermal Hamiltonians with undecidable confinement boundaries**

This is a research report dated 2 October 2026, built from three manuscripts
of batch 78 (cluster H2) of ProveIt's incoming reports. All three are
AI-assisted research manuscripts prepared for Vladimir Reshetnikov. They are
called *source 02*, *source 10* and *source 03* after their batch-78
manuscript numbers, which are also the file prefixes of their shipped
programs, data and notes.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 02 (base) | batch 78, manuscript 02 | `ProveIt_Exact_Erasure_Research.zip` (`1977e6ea6`); *Exact Erasure without a Common Invariant Line: Positive stochastic computation, tensor guards, and Diophantine certificates*, main file `exact_erasure_research/article.tex`, 29-page PDF | `928ea9701` | `798b0c5d4` | Part I (Sections 2–16) and Appendices A–B |
| 10 | batch 78, manuscript 10 | `ProveIt_Exact_Convergence_Research.zip` (`808b53ed8`); *Exact Convergence as Computation: Diophantine Certificates for Uniformly Mixing Stochastic Games*, main file `Exact_Convergence_Research/article.tex`, 24-page PDF | `297eb58e4` (see below for its unpinned README read) | `798b0c5d4` | Part II (Sections 17–30) and Appendices C–D |
| 03 | batch 78, manuscript 03 | `Thermal_Arithmetic_Diophantine_Hamiltonians.zip` (`1977e6ea6`); *Thermal Arithmetic: Diophantine Witnesses, Effective Excited Spectra, and Undecidable Confinement Boundaries*, main file `thermal_arithmetic/article.tex`, 25-page PDF | `6914ccca6`; blob `8bd07142` of `imported_substrate_review_20261002.md` | `798b0c5d4` | Part III (Sections 31–41) and Appendix E |

Author lines, kept in the Part openings: source 02 "Research report prepared
for Vladimir Reshetnikov / Mathematical development and implementation:
ChatGPT"; source 10 "Prepared for Vladimir Reshetnikov / Mathematical
development and exact-arithmetic implementation: ChatGPT"; source 03
"Research report prepared for Vladimir Reshetnikov" (no assistant named; its
provenance note says the files were "authored for this request").

Every result, proof, example, remark, limitation, research question and
appendix of the three manuscripts is printed. They share no theorem, and none
cites another. They share one pattern, set out in Section 1.2 (Table 1): an
approximation converges uniformly at a rate known in advance, while an *exact*
event of the same system is undecidable — exact erasure under a uniform
total-variation contraction (Part I), exact arrival of value iteration at a
known fixed point (Part II), and the boundary value of a uniformly computable
critical fugacity (Part III).

**Status: AI-assisted, unrefereed, not formalized.** Nothing in the report
is formalized in Lean or Rocq, and priority is not certified for any Part.

## Already reviewed in the research programme

All three manuscripts were reviewed by the Hilbert's-tenth-problem research
programme before they were placed here. This report links those reviews and
does not present its placement as a first review.

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

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 90 pages (unnumbered title page, then pages 1–89)
README.md                                            this guide
02-exact-erasure-PROOF_STATUS.md                     source 02's claims, dependencies, checks and limits, as delivered
02-exact-erasure-SOURCE_AUDIT.md                     source 02's repository reads and primary sources, as delivered
03-thermal-arithmetic-PROVENANCE.md                  source 03's repository snapshot and primary literature, as delivered
10-exact-convergence-PROOF_STATUS.md                 source 10's proof, novelty and implementation status, as delivered
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

Not shipped: the three PDFs; the delivered READMEs of all three; the
manuscripts of sources 10 and 03 (printed as Parts II and III); the verified
checksum ledgers of source 02 (`verification/SHA256SUMS`, 25 of 25) and
source 03 (`SHA256SUMS.txt`, 11 of 11; source 10 shipped none); two in-archive
byte copies, `verification/run_output.txt` of source 02 (= `check_results.json`)
and `artifacts/test_run.txt` of source 10 (= `verification.json`); and source
10's two large certificates (next section). All survive in the archives of
their arrival commits: for example
`git show 1977e6ea6:docs/incoming/ProveIt_Exact_Erasure_Research.zip > ee.zip`,
`git show 1977e6ea6:docs/incoming/Thermal_Arithmetic_Diophantine_Hamiltonians.zip > ta.zip`
and `git show 808b53ed8:docs/incoming/ProveIt_Exact_Convergence_Research.zip > ec.zip`.

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
renamed apart from the prefix. The merge added 50 labels, 256 in all:
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

Each Part keeps its source's numbering by section: source 02's Section *n* is
Section *n* + 1 (Sections 2–16), source 10's is *n* + 16 (17–30), source 03's
is *n* + 30 (31–41); so source 10's Theorem 1.1 is Theorem 17.1 and source
03's Theorem 2.1 is Theorem 32.1. Source 02's appendices keep their letters
A–B, source 10's become C–D and source 03's becomes E; Appendix F is the
provenance. Text written in the merge is marked `[write]`; text without a
marker is the source's own.

## Setting and notation

No symbol was renamed and no normalization changed; each Part keeps its own
letters, and Table 2 (Section 1.3) lists every letter used differently,
among them `N`, `K`, `D`, `M`, `T`, `H`, `Q`, `L`, `R`, `P` and `η` (for
example, `K` is source 02's lift scale, source 10's layer normalizer, and in
source 03 both the halting set `𝖪` and a compact remainder operator). Watch
for these readings:

- **Erasure.** In Part I a word *erases* when its stochastic product has rank
  one (one common output distribution, not necessarily uniform). In Part II the
  *erasing map* and *erasing halt convention* send a halted computation to the
  zero vector; the event observed there is attainment of the fixed point
  `½·1`. Same word, unrelated notions.
- **Uniform** means different things: Part I's uniform erasing word (target
  `J_n`) and uniform switching; Part II's uniformly mixing rows and uniform
  reset; Part III's uniformly computable reals.
- **Contraction / confinement.** Part I contracts total variation; Part II the
  supremum norm; Part III has no dynamics, and its confinement is the spectral
  bound `H > 0 ⇒ H ≥ 1 + Σ n_i`.
- **Certificate.** Parts I and II are horizon-indexed (arity grows with `T`);
  Part III's Hamiltonian has a fixed number of modes. None is a fixed-arity
  single-fold representation of a c.e.-complete set.
- **Fugacity, thermal** are mathematical parameters; no physical system is
  assumed.

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

Credit and pointers (printed as `[write]` notes naming the host labels, no
novelty claimed): the circuit core of Part III's compiler and the fixed-arity
quartic corollaries of Parts I and II are `cdc:wf:lem:quadratization` of
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)
(and `pqc:lem:quarticlower`); the no-cutoff clauses of all three Parts are
`cdc:bd:prop:nobound`; Part III's finite-fold theorem follows
`cdc:cs:thm:finitefold`; Part II's complementarity gadget specializes
`pqc:pm:lem:clamp` / `pqc:pm:thm:trace`; Part I's (3,6) bound is also
credited to Neary (STACS 2015, Cor. 12), as Part II of
`probabilistic-quantum-and-continuous-computation` does.

The report does **not** claim:

- priority for any Part (all three sources say their searches were
  targeted), refereeing, or any Lean/Rocq verification; the finite checks
  (50,582, 26,077 and 7,936 assertions) illustrate and do not prove;
- an improvement of the repository's 75-operation complete-certificate or
  87-operation universal-polynomial records; no numerical universal polynomial,
  stochastic alphabet or game is instantiated;
- a finite-fold or single-fold Diophantine representation; bounded certificates
  have horizon-dependent arity, and MRDP's fixed-arity quartics leave witness
  multiplicity uncontrolled;
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
  errors.

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
  source 17 has Part II's slogan for stationary laws.
- Part VII there: Part II here is the real, order-preserving counterpart of
  source 12's exact extinction (`pqc:ad:cor:complete`) and explains source 14's
  decidable point reachability (`pqc:sc:thm:main` (iii)) by its non-erasable
  clock; it answers Part VII's unlabelled question "Structural subclasses"
  negatively in part (the one-player case stays open).
- Parts VIII and IX there: `pqc:tu:cor:fixedquartic` (cited by Part III) and
  `pqc:iq:thm:geometric` (related to Part I's zero–one law).

[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)
supplies the re-proved results listed above and the degree floor
`cdc:of:thm:classification`, which makes radial isolation below degree four
impossible for a universal family (note in Section 39.1).
[`liveness-beyond-halting`](../liveness-beyond-halting),
[`group-theoretic-substrates`](../group-theoretic-substrates) and
[`signal-machine-collision-certificates`](../signal-machine-collision-certificates)
have no overlap. The research note
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/matrix_pcp_trace.md`
uses the same radix-three PCP tiles as Part I's front end, without its fourth
coordinate and idempotent connector.

**The formal project.** The report sits in the collection, not in
`Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
development confers no formal status**. The sources import MRDP only as a
classical theorem; source 10 names the project's interface
`Diophantine.mrdp`, `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
(`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33, 42,
26; blob unchanged from source 10's pin to the write). The project has
formalized none of this report's statements: it has no stochastic-matrix,
stochastic-game, Bellman-operator or occupation-number Hamiltonian module.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
microtype, booktabs, longtable, enumitem, fancyhdr, needspace, listings,
xurl, hyperref, bookmark). The committed build has 90 pages: no LaTeX
warnings at all (no undefined references or citations, no multiply defined
labels, no duplicate destinations), no overfull boxes, and six underfull
lines (badness at most 2799), in three `[write]` notes and the bibliography.

## Rerunning the programs

Every suite imports its companion modules by their delivered names and
writes into delivered paths: source 02's `run_checks.py` rewrites
`examples/*.json` and `verification/check_results.json` under its parent
directory; source 10's `run_checks.py` rewrites every file of `artifacts/`;
source 03's `verify.py` rewrites `examples.json` and `verification.json` in
its own directory. On Windows all of them write CRLF line endings, while the
shipped files are LF. **Never run them in place.** Recreate the delivered
layout in a scratch directory:

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
cd r03 && uv run --no-project --with sympy==1.14.0 python verify.py
```

The checkers only read the certificate they are given, so they may be pointed
at the shipped `data/` files. At the write (Python 3.14.4, Windows,
`PYTHONUTF8=1`) all three suites passed: source 02 with 50,582 assertions,
its 12 regenerated examples equal to the shipped files after CRLF→LF and its
check results differing only in `"python"`, and the wrong uniform target
rejected (exit 1); source 10 as described above; source 03 with 7,936
assertions, both JSON files and the console output equal to the shipped ones
after CRLF→LF.

Do not use the delivered build drivers here: `code/02-exact-erasure-Makefile`,
`code/03-thermal-arithmetic-build.sh` and `code/10-exact-convergence-build.py`
assume the delivered layout (the first two run pdflatex on an `article.tex`
beside them, the third runs `code/run_checks.py` below its own directory and
writes `artifacts/test_run.txt` and `build_logs/`); none of them builds this
report. Use the build command above.

## Discrepancies and disclosures

- **Source 10's unpinned README read.** Its bibliography linked the project
  README through `/blob/main/`, and its Appendix A (Appendix C here) records
  blob `880d2a13`. That blob is the README introduced by `db3b377f0` and
  replaced by `b7a9404d4`, both after the pin `297eb58e4` used for its other
  two repository reads (whose README blob is `138f234b`). Both versions state
  the 75- and 87-operation figures it quotes. A `[write]` note in Appendix C
  says so; the merged bibliography entry records all three sources' reads of
  that README.
- **Delivered names in delivered text.** `02-exact-erasure-PROOF_STATUS.md`
  names `verification/check_results.json` and `verification/pdf_preflight.json`;
  `10-exact-convergence-PROOF_STATUS.md` names `artifacts/verification.json`
  and calls the main theorem "Theorem 1.1" (Theorem 17.1 here);
  `03-thermal-arithmetic-PROVENANCE.md` names `article.tex`, `compiler.py`,
  `verify.py`, "the two JSON files and the console receipt" and the PDF;
  `data/02-exact-erasure-final_certificate_replay.json` names
  `examples/*.json`; both `pdf_preflight.json` files describe the sources' own
  PDFs, which are not shipped. The Parts' reproduction sections and code
  listings keep the delivered layout; `[write]` notes give the shipped names.
- **Excluded certificates named in text.** Part II (Section 26) and source
  10's delivered texts name `countdown_certificate.json` and
  `fixedpoint_certificate.json`, which are not stored here; see
  "Reconstructing the excluded data".
- **Source 03's build note.** Its reproduction appendix (Appendix E) shows two
  pdflatex passes; `build.sh` runs three (`[write]` note there). Its PDF
  metadata used the subtitle *Diophantine Witnesses and Undecidable Confinement
  Boundaries*; the printed subtitle is used here.
- **Wording corrected by editorial brackets, not in the source text.** Part I's
  "the fixed seven-state undecidable family" (Section 11.2) means the
  seven-state, at-most-eight-letter promised class of input-dependent
  alphabets, not one fixed alphabet. Part III's statement that floats and
  Booleans are rejected holds for `compile_polynomial` only (above).
- **External claims not checkable here.** Source 02's MathOverflow question
  511960 and its June 3 comment; the published literature cited by the three
  sources was not re-read at the write.
- The three delivered title pages are replaced by one title page; each
  source's title, subtitle, author line, abstract and status statement open
  its Part verbatim. Source 02's remarks used the definition style; all remarks
  now use the remark style. The three bibliographies are merged (key mapping in
  Appendix F).
