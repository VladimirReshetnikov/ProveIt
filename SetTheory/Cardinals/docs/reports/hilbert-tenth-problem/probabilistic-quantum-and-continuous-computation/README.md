# Diophantine Laws of Probabilistic, Quantum and Continuous Computation

**Normalization budgets and unique quartic certificates, four-dimensional quantum mortality, a continuous three-outcome trichotomy, exact probabilities, exact gates and contracting dynamics**

This is a research report dated 30 September 2026, built from eleven
manuscripts: three of batch 60 (Parts I–IV) and eight of batch 62 (Parts
V–VII). All were prepared for Vladimir Reshetnikov. Of batch 60,
manuscripts 08 and 09 name ChatGPT as the author of the mathematical
development and code, and manuscript 07 describes itself as a research
manuscript with reproducible exact-arithmetic artifacts. The eight batch-62
manuscripts are AI-assisted research manuscripts; their title-page wording is
recorded in Appendix F.1 of the article.

| Source | Batch | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 08 (base) | 60, manuscript 08 | `ProveIt_Diophantine_Quantum_Normalization` (*Diophantine Laws of Probabilistic Computation: optimal normalization budgets, unique quartic certificates, and quantum computational substrates*, 29-page Letter PDF) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Section 1, Part I (Sections 3–9), Sections 11–12 of Part II, Section 33, its parts of Sections 34–37, Appendices A.1 and D |
| 07 | 60, manuscript 07 | `quantum_diophantine_research` (*Rational Gram Packing, Four-Dimensional Quantum Mortality, and Diophantine Certificates*, 22-page A4 PDF) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Sections 13–22 of Part II, its parts of Sections 1 and 34–37, Appendix A.2 |
| 09 | 60, manuscript 09 | `ProveIt_Diophantine_Barriers` (*Diophantine Barriers for Continuous Computation: a three-dimensional trichotomy, finite quartic certificates, and a computable critical-noise radius*, 26-page Letter PDF, main file `diophantine_barriers.tex`) | `f608f1cb3` | `ccfb084ad` | `7498484af` | Part III (Sections 23–32), its parts of Sections 1 and 34–37, Appendices B, C and E |
| 13 | 62, manuscript 09 | `Quartic_Probability_Landscapes` (*Probabilities from Well-Conditioned Quartics*) | `b998f70c6` | `b57c0b5ff` | `adeddcecc` | Part V: Sections 39–51, appendices 63–64, Sections 68.1 and 69.1 |
| 17 | 62, manuscript 14 | `ProveIt_Reversible_Equilibria` (*Arithmetic of Rapidly Mixing Reversible Computation*) | `e18718e83` | `cb1646dc4` | `adeddcecc` | Part V: Sections 52–62, appendices 65–67, Sections 68.2 and 69.2 |
| 10 | 62, manuscript 06 | `Diophantine_Certificates_for_Coherent_Computation` (*Diophantine Certificates for Coherent Computation*) | `ccfb084ad` | `b57c0b5ff` | `adeddcecc` | Part VI: Sections 71–80, appendices 103–104, Sections 108.1 and 109.1 |
| 11 | 62, manuscript 07 | `proveit_rational_rotations_research` (*Decidable Gates, Undecidable State Transfer*) | `b6bf6406a` | `b57c0b5ff` | `adeddcecc` | Part VI: Sections 81, 84 (shared core, with 16), 86–90, 96–97, 100, appendices 105–106, Sections 108.2 and 109.2 |
| 16 | 62, manuscript 13 | `dense_rotations_research` (*Dense Rotations, Undecidable Exactness*; main file `dense_rotations.tex`) | `e18718e83` | `cb1646dc4` | `adeddcecc` | Part VI: Sections 82–83, 84 (shared core, with 11), 91–95, 98–99, 101–102, appendix 107, Sections 108.3 and 109.2 |
| 14 | 62, manuscript 11 | `strict_contractions_research` (*Strict Contractions with Diophantine-Complete Transients*; main file `strict_contractions.tex`) | `526c2557f` | `6d04e1e38` | `adeddcecc` | Part VII: Sections 111–122, appendices 144–145, Sections 151.1 and 152.1 |
| 12 | 62, manuscript 08 | `Diophantine_Contracting_2Adic` (*Exact Diophantine Computation in Contracting 2-adic Dynamics*) | `b6bf6406a` | `b57c0b5ff` | `adeddcecc` | Part VII: Sections 123–133, appendices 146–148, Sections 151.2 and 152.2 |
| 15 | 62, manuscript 12 | `Precision_Is_Memory_Diophantine_Neural_Computation` (*Precision Is Memory: Quadratic Diophantine Certificates for Neural Computation and the Rational-Synthesis Frontier*) | `526c2557f` | `cb1646dc4` | `adeddcecc` | Part VII: Sections 135–143, appendices 149–150, Sections 151.3 and 152.3 |

Sources 10–17 are called by their shipped file prefixes, which continue this
report's sequence after 07–09; their batch-62 manuscript numbers are in the
second column. Written sections: 38 (conventions of Part V), 70 and 84–85
(conventions of Part VI, the shared core of sources 11 and 16, and the
completion of 11's main proof), 110 and 134 (conventions of Part VII and the
comparison of sources 14 and 12), the conclusion and question sections of each
Part, and Appendix F.1.

Every result, proof, example, remark, research question and limitation of the
eleven manuscripts is printed. The three batch-60 sources share no theorem.
Of batch 62, sources 11 and 16 share one arithmetic core (denominator
rigidity, decoding, rank-*d* embeddings, the spin map, the Mihailova compiler,
density and approximation), printed once in Section 84 with genuinely
different proofs kept as marked second routes; sources 14 and 12 reach one
phenomenon by independent routes and are both printed in full; and sources 13,
17, 14 and 10 re-derive results of Parts I–III, which are cited, with their
arguments kept as second routes (only source 13's interior-threshold table is
not reprinted). **The report is AI-assisted and unrefereed, and none of its
theorems is formalized in Lean or Rocq.**

```
article.tex                                           the report, standalone LaTeX with an internal bibliography
article.pdf                                           the compiled report, 275 pages (unnumbered title page,
                                                      contents pages 1-16, then pages 17-274)
README.md                                             this guide
07-quantum-mortality-STATUS.md                        source 07's verification and dependency status, as delivered
09-continuous-barriers-PROVENANCE.md                  source 09's repository inspection, sources and claim boundaries, as delivered
10-coherent-circuits-SOURCE_AUDIT.md                  source 10's repository and literature audit, as delivered
12-twoadic-contraction-PROOF_STATUS.md                source 12's proof, test and PDF-check status, as delivered
12-twoadic-contraction-SOURCES.md                     source 12's source ledger, as delivered
13-quartic-landscapes-PROVENANCE.md                   source 13's provenance and build record, as delivered
14-strict-contractions-SOURCE_AUDIT.md                source 14's repository and literature audit, as delivered
17-reversible-equilibria-PROVENANCE.md                source 17's pin, inspected files and literature record, as delivered
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
code/10-coherent-circuits-build.py                    source 10's build of its own manuscript PDF, delivered paths
code/10-coherent-circuits-check_certificate.py        source 10's independent certificate checker (imports no generator code)
code/10-coherent-circuits-coherent.py                 source 10's Z[e^{i pi/4}] arithmetic, canonical wires, contractions, comparator
code/10-coherent-circuits-verify.py                   source 10's checks; writes data/
code/11-rational-rotations-build.sh                   source 11's build (runs code/verify.py, then its manuscript), delivered paths
code/11-rational-rotations-rotations.py               source 11's decoders, spin lifts, compiler, Miller normal forms, trace certificates
code/11-rational-rotations-verify.py                  source 11's checks; writes verification_results.json
code/12-twoadic-contraction-build.sh                  source 12's build of its manuscript, delivered paths
code/12-twoadic-contraction-padic_machine.py          source 12's tape machine, 2-adic encoding, residues and Mealy compiler
code/12-twoadic-contraction-quartic_certificate.py    source 12's bounded quartic residuals and canonical witness
code/12-twoadic-contraction-verify.py                 source 12's checks (121,822); writes examples/ and verification_report.json
code/13-quartic-landscapes-build.sh                   source 13's build of its manuscript, delivered paths
code/13-quartic-landscapes-degree_two.py              source 13's degree-two transfer-matrix counter
code/13-quartic-landscapes-quartic_compiler.py        source 13's Boolean-circuit-to-quartic compiler
code/13-quartic-landscapes-verify.py                  source 13's checks (6,050 exact, 60 NumPy smoke tests); writes results/
code/14-strict-contractions-Makefile                  source 14's make targets (pdf, verify, clean), delivered names
code/14-strict-contractions-check_export.py           source 14's independent checker; prints its report to standard output
code/14-strict-contractions-verify_contraction.py     source 14's CPWL compiler, integer ReLU circuit, first-hit quartic, self-test
code/15-neural-precision-neural_certificates.py       source 15's trace, projective and synthesis certificate compilers
code/15-neural-precision-test_certificates.py         source 15's checks (53,472 assertions); writes examples/ and verification_report.txt
code/16-dense-rotations-build.sh                      source 16's build (runs verify.py, then dense_rotations.tex), delivered names
code/16-dense-rotations-verify.py                     source 16's decoder, compiler and certificate checks; writes two JSON files
code/17-reversible-equilibria-Makefile                source 17's make targets (check, pdf, clean), delivered paths
code/17-reversible-equilibria-equilibria.py           source 17's exact masses, prefix enclosures and quartic certificates
code/17-reversible-equilibria-verify.py               source 17's checks (SymPy); writes results/ and verification/
code/18-rational-tubes-Makefile                       batch 64, source 18 (placed in 3025c15df; not yet written into the article)
code/18-rational-tubes-constant_example.py
code/18-rational-tubes-kinetic.py
code/18-rational-tubes-quartic.py
code/18-rational-tubes-run_checks.py
code/18-rational-tubes-tubes.py
code/18-rational-tubes-verify_json.py
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
data/10-coherent-circuits-BUILD_INFO.txt              source 10's build and test summary (its 26-page PDF, Python 3.13.5)
data/10-coherent-circuits-HH_expanded_quartic.json    the eight-variable, 33-monomial HH quartic of Section 103
data/10-coherent-circuits-HH_zero_certificate.json    the HH output-1 contraction certificate: 1,326 variables, 1,330 equations
data/10-coherent-circuits-HTH_zero_certificate.json   the HTH certificate: 1,806 variables, 1,810 equations
data/10-coherent-circuits-independent_checker.log     the checker's PASS lines for the three certificates
data/10-coherent-circuits-verification.json           source 10's recorded run (counts of Section 80.2; elapsed time)
data/10-coherent-circuits-verification.log            its console log
data/11-rational-rotations-source_manifest.json       source 11's pin, inspected files and literature record (no hashes)
data/11-rational-rotations-verification_results.json  source 11's recorded run (the 16 check families of its table)
data/12-twoadic-contraction-BUILD_RECEIPT.json        source 12's record of its 27-page PDF build and 121,822 checks
data/12-twoadic-contraction-demo_expanded_quartic.json  the demonstration quartic expanded (818 monomials)
data/12-twoadic-contraction-demo_mealy.json           the demonstration Mealy transducer (1,795 reachable states)
data/12-twoadic-contraction-demo_quartic.json         the demonstration residual system (91 witnesses, 117 residuals)
data/12-twoadic-contraction-demo_witness.json         its unique witness at n = 337
data/12-twoadic-contraction-verification_report.json  source 12's recorded run
data/13-quartic-landscapes-geometric_horizon_0.json   the geometric-waiting quartic at horizon 0 (and 1, 2, 3 below)
data/13-quartic-landscapes-geometric_horizon_1.json
data/13-quartic-landscapes-geometric_horizon_2.json
data/13-quartic-landscapes-geometric_horizon_3.json
data/13-quartic-landscapes-test_output.txt            byte-identical copy of the next file (delivered twice)
data/13-quartic-landscapes-verification_report.json   source 13's recorded run (6,050 exact checks, 60 NumPy smoke tests)
data/14-strict-contractions-certificate_assignment.json  the example's natural witness values
data/14-strict-contractions-certificate_system.json   the example's quadratic residuals
data/14-strict-contractions-example_program.json      the three-state counter-transfer program
data/14-strict-contractions-example_trace.json        its exact trajectory (first hit at t = 7)
data/14-strict-contractions-expanded_quartic.json     the expanded quartic: 2,105 terms, 400 witnesses
data/14-strict-contractions-independent_checker_report.json  the checker's report (its standard output)
data/14-strict-contractions-integer_circuit.json      the 26-gate integer ReLU circuit
data/14-strict-contractions-test_report.json          source 14's recorded self-test
data/15-neural-precision-fixed_trace.json             the fixed-input trace certificate example
data/15-neural-precision-projective_trace.json        the projective certificate example
data/15-neural-precision-rational_synthesis.json      the synthesis quartic example (25 neurons, 114 coordinates)
data/15-neural-precision-source_manifest.json         source 15's pin and read paths (no hashes)
data/15-neural-precision-verification_report.txt      source 15's recorded run (53,472 assertions; Python 3.13.5)
data/16-dense-rotations-example_gates.json            the nine gates of the decidable example (denominator 5^14)
data/16-dense-rotations-verification_results.json     source 16's recorded run
data/17-reversible-equilibria-checks.json             source 17's recorded run (113,686 checks; Python 3.13.5, SymPy 1.14.0)
data/17-reversible-equilibria-compact_quartic_N3.json the compact N = 3 prefix certificate
data/17-reversible-equilibria-compact_quartic_N3.txt  the same, expanded
data/17-reversible-equilibria-examples.json           the exact example masses and enclosures
data/17-reversible-equilibria-pdf_preflight.json      source 17's check of its own PDF
data/17-reversible-equilibria-quartic_N3.json         the full N = 3 prefix certificate
data/17-reversible-equilibria-quartic_N3.txt          the same, expanded
data/17-reversible-equilibria-requirements.txt        sympy==1.14.0
data/18-rational-tubes-VERIFICATION_RECEIPT.txt       batch 64, source 18 (placed in 3025c15df; not yet written into the article)
data/18-rational-tubes-chemical_end_to_end_certificate.json
data/18-rational-tubes-chemical_small_quartic.json
data/18-rational-tubes-constant_certificate.json
data/18-rational-tubes-constant_flow_reactions.json
data/18-rational-tubes-constant_quartic.json
data/18-rational-tubes-constant_robust_certificate.json
data/18-rational-tubes-logistic_reactions.json
data/18-rational-tubes-logistic_robust_certificate.json
data/18-rational-tubes-negative_decay_certificate.json
data/18-rational-tubes-negative_floor_certificate.json
data/18-rational-tubes-negative_floor_quartic.json
data/18-rational-tubes-negative_quartic.json
data/18-rational-tubes-offset_nonlinear_reactions.json
data/18-rational-tubes-pre_blowup_certificate.json
data/18-rational-tubes-rational_data_certificate.json
data/18-rational-tubes-rational_quartic.json
data/18-rational-tubes-requirements.txt
data/18-rational-tubes-specialized_constant_expanded.txt
data/18-rational-tubes-specialized_constant_quartic.json
data/18-rational-tubes-verification_summary.json
```

The delivered READMEs and PDFs of the eleven manuscripts, and the batch-62
checksum manifests (`SHA256SUMS`, `SHA256SUMS.txt`, `MANIFEST.json`,
`CHECKSUMS.sha256`), are not shipped: this README replaces the READMEs, and
`article.pdf` is a build of the merged text. The batch-60 manuscripts and
READMEs of 07 and 09 survive in `ccfb084ad` (inside the zips), as do their
PDFs; 08's delivered `article.tex` and `README.md` are also the versions of
these two files in `7498484af`. The batch-62 manuscripts, READMEs, PDFs and
manifests survive in their arrival commits `b57c0b5ff`, `6d04e1e38` and
`cb1646dc4` (inside the zips). Every other delivered file is shipped under the
prefixed name above, **byte-identical to the delivery**; the delivered paths
and the files whose text still uses them are listed under *Delivered names*
below.

The 28 files beginning `18-rational-tubes-` (7 in `code/`, 21 in `data/`)
belong to batch 64's manuscript 05, *Rational Tubes, Integer Zeros*, placed
here as addition 18 in `3025c15df` for a later Part VIII. They are listed so
that the listing matches the directory; the article does not yet contain that
manuscript, and nothing in this README describes it.

## Labels and numbering

Every label in `article.tex` carries the prefix `pqc:`. Source 08's 74
labels are `pqc:` + the delivered name, source 07's 64 are `pqc:qm:` + the
delivered name, and source 09's 87 are `pqc:cb:` + the delivered name (225
delivered labels, none dropped; the delivered clashes `thm:quartic`,
`eq:mrdp`, `eq:quartic` (07/09), `thm:universal`, `eq:terminal`,
`sec:questions` (08/09) and `eq:canonical`, `sec:quartic` (07/08) are
removed by the prefixes). Writing Parts I–IV added 33 labels: `pqc:conv`,
`pqc:conv:*` (15), `pqc:part:*` (4), `pqc:app:provenance`,
`pqc:qm:rem:chainformal`, and eleven research-question labels `pqc:q:*`
(6), `pqc:qm:q:*` (3), `pqc:cb:q:*` (2) — 258 labels then. Eight delivered
section labels whose headings were rewritten (`sec:audit`, `sec:questions`
and `app:archive` of 08, `sec:implementation`, `sec:future` and
`app:contracts` of 07, `sec:questions` and `sec:examples` of 09) sit on the
corresponding merged headings. The 46 labels of lemmas, propositions,
corollaries, definitions, examples and remarks of Parts I–IV carry cleveref
type hints (`\label[lemma]{…}`), because these environments share the
theorem counter and `\cref` would otherwise print every one of them as
"theorem". No `pqc:` label has a Lean mapping.

Batch 62 (Parts V–VII) kept all 565 delivered labels of its eight
manuscripts, prefixed by source: `pqc:cc:` (10, 66 labels), `pqc:rr:` (11,
77), `pqc:ad:` (12, 80), `pqc:ql:` (13, 54), `pqc:sc:` (14, 68), `pqc:pm:`
(15, 69), `pqc:dr:` (16, 75) and `pqc:rv:` (17, 76). Where sources 11 and 16
state the same result, the one printed environment carries both sources'
labels. Writing Parts V–VII added 72 labels: `pqc:part:b62-V`, `-VI`, `-VII`;
`pqc:conv:b62-*` (14); `pqc:gates:*` (10) and `pqc:contr:sec:overlap`;
`pqc:app:provenance62`; research-question labels `pqc:rr:q:*` (7),
`pqc:dr:q:*` (10), `pqc:ad:q:*` (5), `pqc:sc:q:*` (4), `pqc:rv:q:physical`;
the section labels `pqc:ql:sec:intro` and `pqc:sc:sec:intro`; and labels on
thirteen existing unlabelled research questions of Parts II–IV (`pqc:q:histories`,
`pqc:q:frontend`, `pqc:q:algebra`, `pqc:q:instruments`, `pqc:q:promise`,
`pqc:q:signed`, `pqc:q:fields`, `pqc:cb:q:dimension`, `pqc:cb:q:realizers`,
`pqc:cb:q:neural`, `pqc:cb:q:transfer`, `pqc:cb:q:critical`,
`pqc:cb:q:boundary`) and on the example `pqc:ex:hhhth`. The report now has
**895 labels** (258 + 565 + 72), counted with `\label(\[[^]]*\])?\{`; no
existing label was renamed or removed, and no existing label's number or
bibliography number changed (checked against the `.aux` of the previous
build). In Parts V–VII, 85 labels of shared-counter environments carry
cleveref type hints, for the same reason as above.

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

Parts V–VII continue the numbering: Sections 38–69 (Part V), 70–109 (Part
VI) and 110–152 (Part VII); the appendices keep their letters A–F. Section
*n* of source 13 is Section 38 + *n* (*n* = 1–13); of source 17, Section
51 + *n* (*n* = 1–11); of source 10, Section 70 + *n* (*n* = 1–10); of
source 14, Section 110 + *n* (*n* = 1–12); of source 12, Section 122 + *n*
(*n* = 1–11); of source 15, Section 134 + *n* (*n* = 1–9). Sources 11 and 16
are interleaved around the shared core (see the source table). Each source's
question and conclusion sections are the subsections of Sections 68, 69,
108, 109, 151 and 152, and its appendices are ordinary sections of its Part,
titled "Source NN appendix". Research questions 33–44 are source 17's,
45–58 sources 11's and 16's (numbered here; three pairs merged into one
question each), 59–68 source 14's, 69–80 source 12's and 81–92 source 15's;
source 13's ten numbered paragraphs and source 10's twelve numbered projects
keep their forms. In Parts V–VII an italic *[source NN]* under a section
heading names the source of that section.

## Setting and notation

Witnesses are natural numbers, polynomials have integer coefficients and
subtraction is signed; a residual system's single equation is the sum of
squares of its residuals (Section 2.1). Section 2.3 tabulates the letters the
three batch-60 sources use differently that are most easily confused — `N`
(horizon / common denominator / mesh), `m`, `K`, `k`, `D`, `H`, `A`, `B`,
`T`, `S`, `μ`, `δ`, `α`, `β`, `L`, `Q`, `R`, `G`, `ρ` — states the tempting
false readings, and names the purely local ones. Each Part keeps its
source's letters. Parts V, VI and VII open with their own letter tables and
false readings (Sections 38.2, 70.3 and 110.1): for example source 17's `b`
is a binary environment, not Part I's rejection mass; the `D` of sources 11
and 16 is a common denominator, not a quantum dimension; Part III's `Hit`
is noisy, source 14's exact. Renamed (Sections 2.4, 38.3, 70.4, 110.2; no
normalization changed):

| Here | Source | Where | Reason |
|---|---|---|---|
| `R(σ,τ)`, `R_s` | 08: `K(σ,τ)`, `K_s` | Section 12 and research question 6 | 07's outcome count `K`; shows the specialization to Part I's `R_s` |
| `G_s` | 08: `H_s` | Section 12 | 07's numerator matrices `H_j` and 08's Hadamard gate `H`; specializes to Part I's `G_s` |
| `S_𝓜`, `t_𝓜` | 07: `S`, `T` | Section 16.1 | the `S` and `T` gates of Section 11 |
| `\cenum` | 09: `\ce` ("computably enumerable") | Part III | 08's `\ce` is "c.e."; printed words unchanged |
| `\code` | three definitions | everywhere | unified as a breakable typewriter path |
| `η_*` | 13: `δ_*` = 1/4096 | Part V | Part I's `δ` and source 17's gap `δ` |
| `Pr` | 13: blackboard `P` | Part V | this report's convention |
| `(L_leaf, T_mul, O)` | 10: `(L, T, O)` | Part VI | the `T` gate (also 10's own) and Part II's gate count `L` |
| quaternions `a, b` | 11: `α, β` | Part VI | as in source 16; Part II's scalars `α, β`; 11's Miller action `α_τ` keeps its letter |
| spin map `Φ`, evaluation `η` | 11: `Ψ`, `ρ` | Part VI | as in source 16 (`Φ(p,q)z = pzq⁻¹` equals 11's `pv q̄` on unit quaternions); Part III's `ρ` |
| `ReLU(a)` | 14: `ρ(a)` (its ReLU macro) | Part VII | Part III's critical radius `ρ` |
| `Hit^ex`, `Safe^ex` | 14: `Hit`, `Safe` | Part VII | Part III's noisy predicates |

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

**Part V (sources 13 and 17).** A Boolean circuit with `k` inputs and `s`
gates compiles to a coercive integer quartic in at most `k + 5s + 5`
variables, coefficient height at most 4, interaction degree at most 3, whose
real zeros are Boolean and in bijection with accepting inputs, with Hessian
spectrum in `[2,20]` at every zero, a rounding gap `1/64`, and convex
contractible low-energy components (Theorems 41.2, 42.1, 42.4 and 42.6); for a fair-coin
program the probability of halting by `t` is `2^{-t}` times the root count,
component count or Euler characteristic (Section 44), the limits are exactly
the left-c.e. reals, realized with these uniform constants (Section 45);
counting is polynomial-time at interaction degree two and #P-complete at
degree three (Section 43); fixed quartic normal forms for probability and
finite-mean predicates, with finite expected runtime `Σ⁰₂`-complete (Sections
46–47); coin-faithful substrate transfer (Section 48). Birth–death chains
with defect environments have a sharp common spectral gap `(3−2√2)/4`
(Section 54); the root mass is rational iff the environment is eventually
periodic (Section 55); one defect at the halting time makes equality to `1/2`
`Π⁰₁`-complete with all masses rational (Section 56); factorial defects give
a rational/Liouville dichotomy with `Σ⁰₂`/`Π⁰₂`-complete arithmetic type
(Section 58); the Thue–Morse equilibrium is transcendental, via the imported
Adamczewski–Bugeaud theorem (Section 59); prefix certificates with `3N+4`
and `N+1` witnesses, and strict cuts `Σ⁰₁`-complete (Section 60).

**Part VI (sources 10, 11 and 16).** A supplied contraction tree gives a
unique-witness quartic for the whole coherent contraction, with
`2(L_leaf + 2T_mul − O)` variables over the integers and at most
`8L_leaf + 64T_mul` over `Z[e^{iπ/4}]`, with proved heights (Sections 72–74);
a single-valued comparator for `p + q√2` (21 variables, 29 equations) and
exact circuit probabilities with at most 39 extra variables and 50 equations
(Section 75); graph-state branches (Section 76); a uniformly polynomial
zero-probability compiler would give NP = coNP (Section 77); under fast
Cauchy names exact zero is `Π⁰₁`-complete (Section 78); positive-probability
halting of quantum controllers is `Σ⁰₁`-complete and almost-sure halting
`Π⁰₂`-complete (Section 79). For the rotations `(3±4i)/5`, `(3±4j)/5`: a
reduced word of length `n` has denominator exactly `5^n`, decoded in
polynomial time; a finite presentation compiles to rational `SO(4)` gates
whose group is the image of the Mihailova fiber product, dense when the
presentation is nontrivial (Section 84). Source 11's instantiation has
polynomial-time rational-matrix membership and c.e.-complete state transfer
from a fixed rational vector, with hard targets satisfying an order-five
recurrence and no recursive precision bound (Sections 81, 85–90); source 16's
has c.e.-complete membership, even in every open ball, an exact threshold
`1/(qD^n)`, synthesis depth of degree `0′`, and a dimension-four obstruction
for its mechanism (Sections 82–83, 91–95); both give bounded quartic
certificates and MRDP polynomials (Sections 96–99).

**Part VII (sources 14, 12 and 15).** A fixed rational CPWL, positively
homogeneous, globally `1/2`-Lipschitz map of `R⁴`: exact half-space
reachability is `Σ⁰₁`-complete, point reachability decidable, and the peak
function computable and Lipschitz with a `Π⁰₁`-complete zero set (Sections
111–116); an integer ReLU circuit with `9m + 2d_M − 3` gates and a first-hit
quartic with `(2G+5)T+1` witnesses (Sections 117–118). A `1/2`-contraction of
`Z_2` with `Σ⁰₁`-complete exact extinction, realized by a finite Mealy
transducer, with a clock classification, flatness, and a uniform extinction
horizon for scalar analytic contractions (Sections 123–129); a bounded quartic
with `(3m+6)T + 3S + m + 4` witnesses (Section 131); Section 134 compares the
two routes. A unique-witness quadratic with `4nT` witnesses for exact runs of
rational clipped networks; synthesis for four-layer tied networks equivalent
to Hilbert's tenth problem over `Q`, decidable for strict targets; and no
computable precision ceiling for a universal network (Sections 135–142).

## What the report does not claim

- **No formalization.** No new Lean or Rocq proof was compiled and no
  proof-assistant axiom audit was run for any result here; the formalization
  sections (35.1–35.3, 51, 62, 102, 122, 133, 142.3) are plans, and 09's
  proposed `RobustReachability` module names are not repository declarations.
- **No explicit universal polynomial.** None of the fixed MRDP polynomials
  (Theorems 4.3, 22.1, 26.3, Corollary 29.2, and the MRDP statements of
  Parts V–VII) is expanded, and none has a stated degree, witness count or
  multiplicity. The explicit polynomials are size-indexed families; their
  sizes may not be transferred to the fixed-arity polynomials (Remark 2.1).
  No universal machine table, interpreter, Higman presentation, transducer or
  network weight list is printed (sources 11, 12, 13, 14, 16 say so).
- **No single-fold or finite-fold MRDP result.** Every bounded certificate
  indexes a family; no general finite-fold or single-fold question is assumed
  or settled. Source 16's certificate is parsimonious, not finite-fold.
- **External inputs are imported, not proved:** MRDP; Neary's six-generator
  `3×3` mortality theorem (STACS 2015, Corollary 12); Meyer's theorem (via
  Hasse–Minkowski); Lagrange's four-square theorem; the existence of a binary
  universal Turing machine; the max–min representation theorem (ReLU
  corollary only); Higman's embedding theorem and Mihailova's construction
  (sources 11, 16); Tarski's decision method (sources 15, 16); Minsky's
  two-counter universality (source 14); the Adamczewski–Bugeaud theorem
  (source 17). Established ingredients are credited and not advertised as
  new: Kraft allocation, weak computability, max-relative entropy, exact
  Clifford+T arithmetic, bottleneck duality, Moore's generalized shifts,
  Bournez–Graça–Hainry; tensor-contraction simulation (Markov–Shi),
  path-sum amplitudes (Dawson et al.); rotation undecidability (Bell–Potapov);
  undecidable stationary distributions (Gamarnik, who has priority); the
  Kaminski–Katoen almost-sure-termination hierarchy; neural universality
  (Siegelmann–Sontag) and complementarity formulations.
- **No priority, optimality or minimality.** Literature searches were
  targeted, not exhaustive. 07 does not claim to have discovered quantum
  undecidability (Eisert–Müller–Gogolin 2012 did, in dimension fifteen) or
  that dimension four with seven outcomes is optimal; Proposition 15.5 is
  about arbitrary positive forms, not the special residual forms. 09 claims
  no minimal dimension, optimal Lipschitz constant, optimal degree or network
  size, and does not claim continuous universality or
  robustness-implies-decidability as its own. Of batch 62: 10's NP = coNP
  statement is conditional; 11 claims no scalar-recurrence undecidability and
  no priority for its combination; 12's clock classification holds only
  within its radial family, it claims no one-pass automaton, no global
  smoothness, no multivariate result, and is not universal under clopen or
  robust observation; 13's degree-2/degree-3 frontier is a reduction, not
  FP ≠ #P, and its scheduler caveat for positive almost-sure termination is
  kept; 14 uses an exponential input encoding and claims no minimal dimension,
  noise robustness or smooth universal contraction; 15 does not decide
  Hilbert's tenth problem over `Q` (Koymans–Pagano record it as open) and does
  not implement its generic projective compiler, real quantifier elimination
  or universal network; 16's dimension obstruction is specific to its
  mechanism and its example is decidable.
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
  guarantees avoidance only for errors strictly below it. The rotation
  results of Part VI concern exact rational targets and exact words, not
  finite-precision experiments.
- **Research question 26 (extract and certify Part III's rational neural
  circuit) is not answered.** Source 14 counts gates for a different map and
  source 15 supplies certification infrastructure; neither extracts the
  network of Corollary 31.2.
- **Finite checks are not proofs.** 07's 32,418 and 09's 5,660 assertions and
  08's exhaustive, sampled and symbolic checks test the implementations; 08's
  binary-sharpness diagnostics use floating point and are illustrative; 08's
  quadratic-field sign cross-check uses high-precision `Decimal` as an
  oracle. 07's `gram_search` with a height cap raising `TimeoutError` is not
  evidence that a factor does not exist, and the search is not a practical
  number-theory algorithm. 09 ships no universal interpreter table, ReLU
  weight list or MRDP polynomial, and its grid routine cannot verify a
  Lipschitz bound for an arbitrary Python callable. The batch-62 suites
  (10, 11, 12's 121,822, 13's 6,050 exact and 60 NumPy smoke tests, 14, 15's
  53,472, 16, 17's 113,686) likewise test their implementations only; 13's
  NumPy Hessian checks are floating-point sanity checks.

## Relation to the formal project and to neighbouring reports

The report continues the Lean project `Computability/HilbertTenthProblem`
only through MRDP: its fixed-arity statements use `Diophantine.mrdp`,
`Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
(`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`) as a
mathematical interface, and source 07 names `Diophantine.boundedForall_dioph`,
`Diophantine.exactIter_dioph` and `Diophantine.existsExactIter_dioph`
(`.../Lean/Diophantine/Common/DiophantineTrace.lean`) as an alternative
route. The batch-62 sources use `Diophantine.mrdp` and its hypothesis
`REPred` in the same way. These assert that representations exist and say
nothing about how many witnesses they have. **None of the report's own
theorems is formalized**, and placement beside a Lean project confers no
formal status. ProveIt has no formal development of quaternion rotations,
Mihailova or Miller groups, 2-adic dynamics, tensor contractions, reversible
Markov chains or neural networks; source 12's "existing 2-adic digit API" is
Mathlib's `PadicInt`.
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
between the pins `f608f1cb3`, `ccfb084ad`, `b6bf6406a`, `b998f70c6`,
`526c2557f`, `e18718e83` and the placement commit `adeddcecc`, so the
sources' descriptions of the repository are current. None of the report
concerns the project's operation counts of straight-line universal
certificates.

The sibling report
[`canonical-diophantine-certificates`](../canonical-diophantine-certificates/README.md),
merged from batch 60's manuscripts 01–06 and extended in batch 62, treats
witness-faithful (single-fold, bijective) certificates of **discrete**
executions; it shares no theorem with this one. Its equivalence between
single-fold (finite-fold) universal halting polynomials and the open
single-fold (finite-fold) representability problem is the frontier that
research questions 10 and 19 here ask about (Section 36.4). Research
question 11's continuous-time robustness part is answered for discrete-time
rational PWA maps by Part III and, for stationary masses of reversible
chains, partly by source 17. Part V's Section 38.1 reconciles that report's
weighted canonical-stopping probability representation with Part I's fixed
quartic projection and source 13's randomly padded root counts. The third
report of the category,
[`liveness-beyond-halting`](../liveness-beyond-halting/README.md), treats
infinite-path (recurrence, liveness) predicates, which neither this report
nor the certificates report covers.

Of the research questions of Parts I–IV, batch 62 partly answers 7
(quantum front ends, source 10), 10 (counting, source 13), 11 (continuous
time, source 17), 12 (probability specifications, source 13), 20 (promise
problems, source 16), 22 (exact scalar fields, source 10) and 25 (smooth
realizers, source 12); it bears on 5, 21, 24, 27, 29 and 32; it does not
answer 26. Each has a dated note after it, and Section 36.4 lists them.

## Build

TeX Live or MiKTeX with lmodern, amsmath/amssymb/amsthm, mathtools,
mathrsfs, microtype, booktabs, longtable, array, enumitem, tabularx, xcolor,
fancyhdr, listings, TikZ, xurl, hyperref, cleveref, tcolorbox and etoolbox.
No external figures, bibliography database or downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX, pdfTeX) has 275 Letter pages, with no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull boxes; there are 17
underfull boxes, in narrow table cells and in a few source paragraphs. All
fonts are embedded Type 1. Parts V–VII
widened the contents' section-number and page-number columns (three-digit
numbers). Source 07's `data/07-quantum-mortality-build_summary.json`, source
08's `data/08-probabilistic-laws-pdf_preflight.json`, source 10's
`data/10-coherent-circuits-BUILD_INFO.txt`, source 12's
`data/12-twoadic-contraction-BUILD_RECEIPT.json` and source 17's
`data/17-reversible-equilibria-pdf_preflight.json` describe the delivered
PDFs, which are not shipped; 07's `STATUS.md`, 09's and 13's `PROVENANCE.md`,
12's `PROOF_STATUS.md` and 14's `SOURCE_AUDIT.md` likewise report builds and
page inspections of their own PDFs. These production checks do not verify the
mathematics.

## Rerunning the checks

The programs import each other by their delivered module names and write
into delivered directories, so **run them on a copy with the delivered
layout, never in this directory** (a run here would fail to import, and the
scripts would create `examples/`, `verification/`, `results/`, `artifacts/`
or `data/` files beside the shipped data). From this directory:

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

Batch 62 (use `py` or `python` for Python 3.10+; set `PYTHONUTF8=1` on
Windows; standard library only except 13's optional NumPy and 17's SymPy):

```sh
# 10: do not use python -O (checks use assert)
mkdir -p /tmp/r10/code
for f in coherent verify check_certificate; do cp code/10-coherent-circuits-$f.py /tmp/r10/code/$f.py; done
(cd /tmp/r10 && py code/verify.py && py code/check_certificate.py data/HH_expanded_quartic.json data/HH_zero_certificate.json data/HTH_zero_certificate.json)   # writes data/

# 11
mkdir -p /tmp/r11/code
for f in rotations verify; do cp code/11-rational-rotations-$f.py /tmp/r11/code/$f.py; done
(cd /tmp/r11 && py code/verify.py)               # writes verification_results.json

# 12
mkdir -p /tmp/r12/code
for f in padic_machine quartic_certificate verify; do cp code/12-twoadic-contraction-$f.py /tmp/r12/code/$f.py; done
(cd /tmp/r12 && py code/verify.py)               # writes examples/*.json, verification_report.json

# 13 (NumPy optional, for the floating-point smoke tests only)
mkdir -p /tmp/r13/code
for f in quartic_compiler degree_two verify; do cp code/13-quartic-landscapes-$f.py /tmp/r13/code/$f.py; done
(cd /tmp/r13 && py code/verify.py)               # writes results/

# 14
mkdir -p /tmp/r14
for f in verify_contraction check_export; do cp code/14-strict-contractions-$f.py /tmp/r14/$f.py; done
(cd /tmp/r14 && py verify_contraction.py --self-test --out verification && py check_export.py verification > independent_checker_report.json)

# 15: the output directory must exist
mkdir -p /tmp/r15/code /tmp/r15/examples
for f in neural_certificates test_certificates; do cp code/15-neural-precision-$f.py /tmp/r15/code/$f.py; done
(cd /tmp/r15 && py code/test_certificates.py)    # writes examples/*.json, verification_report.txt

# 16
mkdir -p /tmp/r16
cp code/16-dense-rotations-verify.py /tmp/r16/verify.py
(cd /tmp/r16 && py verify.py --output verification_results.json)   # also writes example_gates.json

# 17: SymPy 1.14.0 (needed by verify.py only); the output directories must exist
mkdir -p /tmp/r17/code /tmp/r17/results /tmp/r17/verification
for f in equilibria verify; do cp code/17-reversible-equilibria-$f.py /tmp/r17/code/$f.py; done
(cd /tmp/r17 && uv run --no-project --with sympy==1.14.0 python code/verify.py)   # writes results/, verification/checks.json
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

The batch-62 recipes were run on 30 September 2026 in copies (Python 3.14.4;
17 with Python 3.13 and SymPy 1.14.0 under `uv`). All eight passed, and every
regenerated file equals the shipped `data/NN-…` file apart from CRLF line
endings, with these exceptions: 10's `verification.json` records the elapsed
time; 13's `verification_report.json` (and its byte-identical copy
`test_output.txt`) records four NumPy Hessian eigenvalues that differ in the
last digits; 15's `verification_report.txt` records the Python version. 14's
checker prints its report, which the recipe saves; it equals
`data/14-strict-contractions-independent_checker_report.json`. 15 and 17 fail
unless their output directories exist, hence the `mkdir` lines.

The delivered Makefiles (`code/07-quantum-mortality-Makefile`,
`code/08-probabilistic-laws-Makefile`, `code/14-strict-contractions-Makefile`,
`code/17-reversible-equilibria-Makefile`) and build scripts
(`code/10-coherent-circuits-build.py`, `code/11-rational-rotations-build.sh`,
`code/12-twoadic-contraction-build.sh`, `code/13-quartic-landscapes-build.sh`,
`code/16-dense-rotations-build.sh`) name delivered paths (`article.tex`,
`strict_contractions.tex`, `dense_rotations.tex`, `code/verify.py`, …); they
work only in a copy of the delivered layout, their `pdf` targets would build
the delivered manuscripts, which are not shipped (in this directory some
would build the merged report instead), and 11's and 16's build scripts rerun
the checks first, rewriting their results in place. 08's `clean` target
deletes `article.aux`, `article.log`, `article.out`, `article.toc` and
`code/__pycache__`; 14's and 17's `clean` targets delete their manuscripts'
auxiliary files.

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
| 10 | `build.py`, `code/<f>.py` (3) | `code/10-coherent-circuits-<name>` |
| 10 | `data/<f>` (6), `BUILD_INFO.txt` | `data/10-coherent-circuits-<f>` |
| 10 | `SOURCE_AUDIT.md` | `10-coherent-circuits-SOURCE_AUDIT.md` |
| 11 | `build.sh`, `code/rotations.py`, `code/verify.py` | `code/11-rational-rotations-<name>` |
| 11 | `source_manifest.json`, `verification_results.json` | `data/11-rational-rotations-<f>` |
| 12 | `build.sh`, `code/<f>.py` (3) | `code/12-twoadic-contraction-<name>` |
| 12 | `examples/<f>.json` (4), `verification_report.json`, `BUILD_RECEIPT.json` | `data/12-twoadic-contraction-<f>` |
| 12 | `PROOF_STATUS.md`, `SOURCES.md` | `12-twoadic-contraction-<name>` |
| 13 | `build.sh`, `code/<f>.py` (3) | `code/13-quartic-landscapes-<name>` |
| 13 | `results/<f>` (6) | `data/13-quartic-landscapes-<f>` |
| 13 | `PROVENANCE.md` | `13-quartic-landscapes-PROVENANCE.md` |
| 14 | `Makefile`, `verify_contraction.py`, `check_export.py` | `code/14-strict-contractions-<name>` |
| 14 | `verification/<f>.json` (8) | `data/14-strict-contractions-<f>.json` |
| 14 | `SOURCE_AUDIT.md` | `14-strict-contractions-SOURCE_AUDIT.md` |
| 15 | `code/<f>.py` (2) | `code/15-neural-precision-<name>` |
| 15 | `examples/<f>.json` (3), `source_manifest.json`, `verification_report.txt` | `data/15-neural-precision-<f>` |
| 16 | `build.sh`, `verify.py` | `code/16-dense-rotations-<name>` |
| 16 | `example_gates.json`, `verification_results.json` | `data/16-dense-rotations-<f>` |
| 17 | `Makefile`, `code/<f>.py` (2) | `code/17-reversible-equilibria-<name>` |
| 17 | `results/<f>` (5), `verification/checks.json`, `verification/pdf_preflight.json`, `requirements.txt` | `data/17-reversible-equilibria-<f>` |
| 17 | `PROVENANCE.md` | `17-reversible-equilibria-PROVENANCE.md` |

Shipped files whose text still uses delivered names or names unshipped
files: `07-quantum-mortality-STATUS.md` (`code/run_checks.py`,
`check_results.json`, its 22-page PDF and contact sheets);
`09-continuous-barriers-PROVENANCE.md` (`results/verification.json`, "the
TeX/PDF"); every Makefile and build script (above);
`data/08-probabilistic-laws-source_manifest.json` (`article.tex` of source 08
and `artifacts/verification.json`);
`data/08-probabilistic-laws-normalization_quartic_N2_m2.txt` ("the JSON
file", its sibling `.json`); the PDF records `data/07-quantum-mortality-build_summary.json`,
`data/08-probabilistic-laws-pdf_preflight.json`, `data/10-coherent-circuits-BUILD_INFO.txt`,
`data/12-twoadic-contraction-BUILD_RECEIPT.json` and
`data/17-reversible-equilibria-pdf_preflight.json` (the unshipped PDFs);
`12-twoadic-contraction-PROOF_STATUS.md` (`verification_report.json`, "the
final PDF"); `13-quartic-landscapes-PROVENANCE.md`,
`14-strict-contractions-SOURCE_AUDIT.md` and `10-coherent-circuits-SOURCE_AUDIT.md`
("the article", its PDF and its build); `17-reversible-equilibria-PROVENANCE.md`
(this report's README at the pin `e18718e83`, which it inspected); the
manifests `data/11-rational-rotations-source_manifest.json` and
`data/15-neural-precision-source_manifest.json` (their manuscripts' inspected
paths); and every Python program (delivered module names and output
directories). `data/13-quartic-landscapes-test_output.txt` and
`data/13-quartic-landscapes-verification_report.json` are byte-identical: the
delivery shipped the same JSON under both names.
`data/08-probabilistic-laws-requirements.txt` and
`data/17-reversible-equilibria-requirements.txt` are generic `sympy==1.14.0`
files.

In Parts I–IV of the article the file names were changed to the shipped
names; 08's archive table (Appendix A.1) and 07's and 09's reproduction
paragraphs (Appendix A.2, Section 34.4) were rewritten for them. In Parts
V–VII the sources' text keeps the delivered names, and a `[write]` paragraph
in each source's implementation section gives the shipped names.

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
- New text in Parts I–IV: Sections 1.3, 1.5, 1.6, 2, 10, 36.4 and Appendix F,
  the title-page abstract and status, Remarks 2.1 and 22.2, the remark at the
  end of Section 33, Section 34.6, the lead paragraphs of Sections 35 and 36
  and of Appendix A.1, and the rewritten reproduction paragraphs.
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

**Batch 62 (Parts V–VII, Appendix F.1).**

- **Placement.** Eight manuscripts of exact probabilistic, quantum-gate and
  continuous-state computation, this report's remit, placed in `adeddcecc`
  and written as three new Parts after Part IV, so that nothing earlier
  renumbers: V (13, 17), VI (10, 11, 16), VII (14, 12, 15). Each Part opens
  with its conventions (sources, what is re-derived, letter table, renames,
  abstracts and status statements) and ends with its conclusions and research
  questions.
- **Sources 11 and 16** share one arithmetic core, printed once (Section 84):
  11's statements and proofs where both prove the same result (its decoder is
  polynomial-time, its approximation bound explicit), 16's finite-field
  tables, left-peeling decoder, block-expansion argument, differential proof
  of surjectivity and Tarski net kept as marked second routes. Their two
  free-group embeddings index generators differently (from 0 and from 1) and
  both are printed. Both instantiations and both certificate families are
  printed in full. Three pairs of their questions are merged, with both texts.
- **Sources 14 and 12** are both printed, with a written term-by-term
  comparison (Section 134).
- **Re-derivations** of Parts I–III are cited and kept as second routes:
  13's interior-threshold table (not reprinted; its rows `p = 1`, `p = 0` and
  finite mean are kept), 13's quartic normalization and lower-cut quartic,
  17's almost-sure cuts, 14's no-gap corollary, 10's positive and almost-sure
  halting; 10's two examples are Part II's Example 11.2, with a pointer.
- **In-place notes in Parts I–IV** (unnumbered, `[write]`): after
  Proposition 11.1's proof (source 10 supplies its witness counts), after
  Theorem 9.1, Proposition 9.4, Theorem 30.1 and Corollary 31.2's discussion,
  and dated notes (30 September 2026) after fourteen research questions.
- **Corrections in the batch-62 text**: 12's `R_{meq}` (a lost backslash in the
  delivered source) printed as `R_eq`; 12's Delvenne–Kůrka–Blondel pages
  (the author version's 1–28) given as the journal's 463–490; 11's "companion
  guide" named as ProveIt's `Lean/MRDP.md`; 12's "existing 2-adic digit API"
  identified as Mathlib's `PadicInt`; 17's citations of this report's README
  made internal cross-references; escaped underscores in file names removed;
  one inline formula of 10 given a line-break point. Title-page wording that
  names an AI assistant or a company is not reproduced.
- **Bibliography**: the eight lists are appended (85 entries in all now).
  Duplicates across batch-62 sources are printed once (Higman,
  Bogopolski–Ventura, Bell–Potapov, Moore 1990, Matiyasevich 1970); 10's and
  13's Kaminski–Katoen and 10's Giles–Selinger entries are this report's
  existing ones; 17's entry for this report's README is omitted.
- The write used the pristine manuscripts in the arrival commits and the
  files staged in `adeddcecc`.
