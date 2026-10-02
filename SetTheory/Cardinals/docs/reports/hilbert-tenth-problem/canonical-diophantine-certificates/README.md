# Canonical Diophantine certificates

**Witness-faithful polynomial representations of bounded discrete computation: resource algebra, trace classes, accelerators, polynomial trajectories, memory logs, queues, rewriting, heaps, self-assembly, priority pumping, reaction networks, routing networks and interaction combinators**

This is a research report dated 30 September 2026, with Part XV dated 2 October
2026, merged from fifteen manuscripts: six of batch 60 (its manuscripts 01–06), the only manuscript
of batch 61, which is numbered 07 here, four of batch 62 (its
manuscripts 01, 02, 04 and 05), numbered 08–11 here and added as Parts X–XIII
after the report had been written, and one of batch 63 (its manuscript 02),
numbered 12 here and added as Part XIV, and three of batch 78 (its
manuscripts 01, 04 and 05), numbered 13–15 here and merged into one Part,
XV. The base is manuscript 05, *Canonical
Trace Polytopes*; its `article.tex` was staged unprefixed and has been
replaced in place by the merged text. All fifteen manuscripts prove the same
kind of theorem: an explicit integer polynomial whose natural zeros are in
bijection with the bounded executions (or trace classes of executions) of a
discrete substrate, with exactly one witness each; in 12 the execution is a
terminating chip-routing run, represented by its outcome (firing counts and
sink outputs) rather than its history. In 13–15 the executions are
scheduled reductions of Lafont's interaction combinators, with exact port
wiring and exact counts of port-free cyclic wires. They continue the Lean
project `Computability/HilbertTenthProblem`, whose trace interfaces assert
only that such representations exist. Author lines: "Research report
prepared for the ProveIt project" (01), "Research manuscript for the ProveIt
project, Prepared with ChatGPT" (02), "Research note / article / memorandum
prepared for Vladimir Reshetnikov" (03, 04, 05), "Prepared for Vladimir
Reshetnikov" (06, 07), "A research article developed for the ProveIt
program" (08), "Research prepared for Vladimir Reshetnikov" (09; its PDF
metadata reads "Research prepared with ChatGPT for Vladimir Reshetnikov"),
"Research manuscript prepared with ChatGPT" (10) and "Research draft
prepared for Vladimir Reshetnikov / Developed with ChatGPT; proofs and
executable verification included" (11) and "Research article prepared for
the ProveIt program" (12), "Prepared for Vladimir Reshetnikov" (13 and 15;
13's title page adds "Prepared with ChatGPT" and its PDF metadata reads
"Research report prepared with ChatGPT for the ProveIt project"; 15's PDF
metadata reads "OpenAI, research draft prepared for Vladimir Reshetnikov")
and "Research prepared with ChatGPT for Vladimir Reshetnikov's ProveIt
program" (14). The article prints the batch-62 and batch-78
author lines in neutral form and records these assistant names only in its
provenance appendix; 12's author line names no assistant.

| Report no. | Batch, manuscript | Archive | Title | Pin | Arrived | Placed | Printed in |
|---|---|---|---|---|---|---|---|
| 01 | batch 60, manuscript 01 | `Diophantine_Causal_Computation` (29-page PDF) | *Canonical Diophantine Certificates for Causal Computation* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (its §1.2); Parts I (§§2–3), II (§§6–7), III (§§4–5, 8), VII (§§9.3–9.4), VIII (§§9.1–9.2), IX (§10) |
| 02 | batch 60, manuscript 02 | `canonical_diophantine_certificates` (27-page PDF) | *Canonical Diophantine Certificates for Polynomial Trajectories* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (§2); Parts IV (§§1.1–1.2, 3–9), VII (§10.2), VIII (§§10.1, 10.3), IX (§§10.4–10.6) |
| 03 | batch 60, manuscript 03 | `ProveIt_Linear_Size_Diophantine_Certificates`, inner directory `ProveIt_Diophantine_Certificates` (31-page PDF) | *Linear-Size Canonical Diophantine Certificates for Random-Access and Graph Computation* | `e8bb0931d` | `725d2ebb6` | `7498484af` | Conventions (§1.3); Parts V (§§2–9), IX (§10) |
| 04 | batch 60, manuscript 04 | `Witness_Faithful_Diophantine_Compilation`, inner directory `diophantine_substrates` (26-page PDF) | *Witness-Faithful Diophantine Compilation* | `e8bb0931d` | `c1f56f842` | `7498484af` | Conventions (§2); Parts II (§§3–5), VII (§§6–7), VIII (§8), IX (§9) |
| 05 (base) | batch 60, manuscript 05 | `canonical_trace_polytopes` (29-page PDF) | *Canonical Trace Polytopes: Witness-Preserving Diophantine Representations of Computational Substrates* | `e8bb0931d` | `c1f56f842` | `7498484af` | Introduction; Conventions (§2); Parts I (§3), II (§§4–8), VII (§9.4), VIII (§§9.1–9.3, 9.5), IX (§10) |
| 06 | batch 60, manuscript 06 | `diophantine_counter_programs` (30-page PDF) | *Saturation and Single-Fold Diophantine Compilation of Concurrent Counter Programs* | `e8bb0931d` | `c1f56f842` | `7498484af` | Conventions (§2); Parts I (§3), II (§§4, 7), III (§§5–6, 8), VIII (§10), IX (§9) |
| 07 | batch 61, its only manuscript | `Causal_Diophantine_Queue_Compilation` (27-page PDF) | *Causality Without Tableaux: Compact Diophantine Certificates for Queue Universality* | `725d2ebb6` | `b998f70c6` | `3bf66a8bc` | Conventions (§§2.1–2.2); Parts I (§3), VI (§§2.3, 4–10), IX (§11) |
| 08 | batch 62, manuscript 01 | `Names_to_Numbers_Diophantine_Heaps`, inner directory `Names_to_Numbers` (28-page PDF) | *Names to Numbers: Exact Quartic Certificates for Dynamic Heaps and Local Graph Computation* | `4e128356d` | `b57c0b5ff` | `adeddcecc` | Section 3.8 (abstract, status, §1); Part X (§§2–14, Appendices A–B) |
| 09 | batch 62, manuscript 02 | `order_free_diophantine` (30-page PDF) | *Order-Free Diophantine Self-Assembly and a Sharp Positivity-Restricted Degree Threshold* | `4e128356d` | `b57c0b5ff` | `adeddcecc` | Section 3.9 (title-page box, abstract, status, §1); Part XI (its Parts I–III) |
| 10 | batch 62, manuscript 04 | `ProveIt_Priority_Pumping_Diophantine`, inner directory `priority_fractran_research` (30-page PDF) | *Sharp Pumping Bounds and Canonical Diophantine Certificates for Priority Arithmetic Computation* | `4e128356d` | `b57c0b5ff` | `adeddcecc` | Section 3.10 (abstract, status, §1); Part XII (§§2–14, Appendices A–C) |
| 11 | batch 62, manuscript 05 | `one_shared_fallback_research`, inner directory `one_shared_fallback` (26-page PDF) | *One Shared Fallback: Conservative Reaction Computation, Unique Quartic Certificates, and a Canonical Fuel Form of the Finite-Fold Problem* | `4e128356d` (also names `ccfb084ad`) | `b57c0b5ff` | `adeddcecc` | Section 3.11 (abstract, §1); Part XIII (§§2–14, Appendices A–B) |
| 12 | batch 63, manuscript 02 | `Diophantine_Certificates_Without_Histories`, inner directory `diophantine_certificates` (26-page PDF) | *Diophantine Certificates Without Execution Histories: Single-fold quartics for succinct routing, and a universal one-router boundary* | `e18718e83` | `a4268e78e` | `62f1ad07c` | Section 3.12 (abstract, §1); Part XIV (§§2–11, Appendices A–B) |
| 13 | batch 78, manuscript 01 | `Exact_Wiring_Diophantine_Report`, inner directory `Exact_Wiring_Diophantine` (28-page PDF) | *Exact Wiring in Diophantine Computation: Sharp loop-parity separation and a cycle-preserving compiler for interaction combinators* | `439c0a2d9` | `1977e6ea6` | `aa11f3fef` | Section 3.13 (abstract, package statement, §1); Part XV (§§2–13, Appendix A); provenance appendix (Appendix B) |
| 14 | batch 78, manuscript 04 | `Topology_Is_Not_Free_Interaction_Nets`, inner directory `Interaction_Net_Diophantine` (23-page PDF) | *Topology Is Not Free: Loop-Sensitive Diophantine Certificates for Interaction Nets* | `6914ccca6` | `1977e6ea6` | `aa11f3fef` | Section 3.14 (title-page box, status, abstract, §1); Part XV (§§2–13, Appendices A–C); provenance appendix (Appendix D) |
| 15 | batch 78, manuscript 05 | `no_ghost_wires`, inner directory `no_ghost_wires` (25-page PDF) | *No Ghost Wires: Loop-Exact Quartic Certificates for Interaction Combinators* | `928ea9701` | `1977e6ea6` | `aa11f3fef` | Section 3.15 (abstract, status, §1); Part XV (§§2–13, Appendices A–C) |

Section numbers in the last column are those of each manuscript. Manuscripts
01–07 also contribute to the Introduction and to the back matter
(Implementation and validation, Formalization targets, Research questions,
Conclusions of the manuscripts, Provenance); manuscripts 08–12 keep their
validation, formalization plans, questions and conclusions inside their
Parts, and appear in the back matter only in the provenance appendix and
the bibliography. Manuscripts 13–15 are merged by subject into Part XV,
which closes with their validation, questions, conclusions and
appendices; the source audits of 13 and 14 are in the provenance appendix. The Parts are: I Exact commutation and resource algebra;
II Canonical trace classes; III Compressed repetition and accelerators; IV
Polynomial trajectories; V Memory logs, RAM and graph evaluation; VI Queues:
tag systems and FIFO networks; VII FRACTRAN, SKI and term rewriting; VIII
Other substrates; IX The boundary of fixed-arity compression; X Dynamic
heaps, fresh names and local graph computation; XI Order-free self-assembly
and a positivity-restricted degree threshold; XII Priority repetition:
pumping bounds, program-uniform certificates and periodic tails; XIII
Conservative priority reaction networks and a canonical-fuel form of the
finite-fold problem; XIV History-free routing certificates: last exits,
compressed periods and a rank-function bottleneck; XV Interaction
combinators: exact wiring, loop-exact gluing and bounded quartic frontends.

The full pins are `e8bb0931d67f80d9fce87a8cddb0f661ff19f956` (01–06),
`725d2ebb6909fe11a13a92354c0f47367a3cbbf5` (07),
`4e128356d0ef75308be8ed405d89aea2ffdb8a57` (08–11; 11 also names
`ccfb084adaa2f32e8d2738a25f82a00377fb3a8c`, a later commit it read on the
live branch) and `e18718e837d43e162252f9a314e8cb797fbd1a1f` (12), and `439c0a2d9c1052595f3de6a29c11511a24fb2e11` (13),
`6914ccca6685baf53b7a35f25efc89366c76ba74` (14) and
`928ea97017a25ebe56d240c84f27d2275d818c75` (15). The pin of 07 is the commit
in which 01–03 arrived; 07 was written after 04 and 06, names them by title
as its companion manuscripts, and arrived after this report was placed but
before it was written. The batch-60 placement commit `7498484af` also placed
the neighbouring report of this category (batch-60 manuscripts 07–09, not to
be confused with this report's 07). Manuscripts 08–11 were written at a pin
that predates this report (it was placed and written in batch 60) and do not
cite it; the write phase added the cross-references. Every file they cite,
under `Computability/`, `Logic/PresburgerArithmetic/` and the vendored
`lib/Coq-Library-Undecidability/theories/H10/Fractran/`, is identical at
`e8bb0931d`, `725d2ebb6`, `4e128356d`, `ccfb084ad` and the write.
Manuscript 12's pin `e18718e83` is the batch-60 commit that wrote the
neighbouring report *probabilistic-quantum-and-continuous-computation*; this
report had been placed but not written then (it was written in `5b87c88c5`),
so 12 does not cite it either. No file under
`Computability/HilbertTenthProblem` differs between `e8bb0931d`,
`e18718e83` and the batch-63 write.

Manuscripts 13–15 were written on the morning of 2 October 2026 at three
commits of that morning (`439c0a2d9` 10:29, `928ea9701` 10:41, `6914ccca6`
10:45), after Part XIV had been written (`781594d88`); 14 read this report's
README and cites it, 13 and 15 do not cite the report. 15 calls
`928ea9701` a "tree identifier" ("recursive-tree revision" in its
`PROVENANCE.md`); it is a commit. 13 records an "initially fetched" README
blob `79153a4ed`, which is the project README of `928ea9701`, not of its pin
(there the README is `076832c56`); both state the 75- and 87-operation
figures that 13 quotes. The other repository files they cite, the research
note `interaction_combinator_wiring_obstruction.md` (blob `764c98229`) and
`Lean/Diophantine/MRDP.lean` (blob `74aea8c5e`), are the same at the three
pins and at the batch-78 write.

What each manuscript contributes:

- **01** exact resource envelopes for every serialization of a repeated
  multiset of box-guarded integer translations; a single-fold quartic
  accelerator; a quartic whose natural roots are in bijection with the
  executable causal trace classes of Cartier–Foata height at most `H`;
  fixed phases and powers of fixed noncommuting words; rank and progress
  criteria; and the equivalence between a fixed-arity single-fold universal
  halting polynomial and the general single-fold problem.
- **02** a single-fold quartic of `O((d+1)^3)` natural coordinates,
  independent of `T`, for `p(i) ≥ 0` on `{0,…,T}` (degree `d` fixed), with
  applications to polynomially iterable, unitriangular and unipotent affine
  updates, first-exit times and specified-input nontermination.
- **03** a quartic with `24L` witnesses and `22L+1` quadratic residuals for
  every zero-initialized memory-access log of length `L`, a sorting-network
  alternative with a size–height trade-off, parsimonious RAM composition,
  graph evaluation, counting and first-halting probabilities.
- **04** one natural zero per independent-swap class of bounded Petri
  executions; a first-applicable-fraction FRACTRAN compiler; a
  unique-witness SKI compiler for a fixed schedule; a deterministic-memory
  lower-bound family.
- **05** (base) a convex quadratic in `(2T+1)d + (7T+1)m` natural unknowns
  whose natural zeros are in bijection with the length-`T` executions of a
  Petri net modulo any sound static commutation relation, with interval
  guards and zero tests; the real zero set is a rational polytope; quartic
  and raw-run variants; counting hardness, Boolean-memory lower bounds and
  the finite-fold equivalence for a canonical universal trace verifier.
- **06** an exact resource-summary algebra, a Boolean signature for
  lexicographic trace normality with `S^2 = S^3`, a quartic compiler for
  nested repetition schedules, a root/trace-class bijection at fixed length,
  and the depth hierarchy (Presburger at depth one, universality of
  existential schedule parameterization at depth two, finite-fold and
  single-fold equivalences at depth four).
- **07** certificates for cyclic-tag and deletion-tag systems and fixed-read
  FIFO networks with one coordinate per consumed symbol and one uniquely
  determined guard slack, no intermediate queue being quantified; the
  first-failure product; a local quartic with `3T-2` coordinates; and a
  proof that faithful word memory with polynomial insertion at both ends
  needs two natural coordinates.
- **08** a memory-log compiler with exactly `10C+4N-3` witnesses and
  `10C+7N-4` quadratic residuals (a variant of 03's; neither dominates),
  unique guarded quadratization of inactive branches, birth-order
  normalization of fresh object names, a quartic in bijection with the runs
  of a fixed bounded-local heap program modulo fresh-name permutations,
  Turing completeness of two immutable pointer-only linked stacks, transfer
  to bounded-local graph programs, polynomial witness heights, and a proof
  that perpetual memory safety has no existential representation.
- **09** for polynomials nonnegative on the whole real orthant, degree two
  and degree three represent exactly the semilinear sets and degree four
  every computably enumerable set; every semilinear set has a single-fold
  degree-two representation; the squares need degree four in this class; a
  convex quadratic with one natural zero per producible labelled assembly
  of a seeded irreversible tile system (`N(q+6)-3s+8K+10J` variables),
  with first-arrival ranks and a whole-grid terminality extension.
- **10** the exact repetition capacity of an instruction word of an
  ordered (first-enabled-rule) multiset or FRACTRAN program, the sharp
  pumping threshold `2H+1`, a single-fold quartic for the block relation
  uniform in all program entries (`29S+3dℓ+12d+3R+3ℓ` auxiliaries), an
  exact criterion for infinite periodic tails, computably enumerable
  completeness of eventual periodicity even for one fixed program, and
  affine macro certificates.
- **11** a compiler from register machines to conservative two-to-two
  priority reaction networks with one shared low-priority fallback (61
  species and 62 reactions for a universal machine), the exact reservoir
  threshold, a proof that one priority level does not suffice and that
  finite rates cannot implement priority, single-fold trace quartics
  (`308T+61` witnesses), single-fold bounded minimum-fuel quartics, and the
  theorem that the least-reservoir relation has a finite-fold (single-fold)
  representation exactly when every c.e. set has one.
- **12** for zero-retention chip-routing networks with absorbing sinks, the
  exact odometer criterion by balance and an acyclic last-exit graph (a
  classical mechanism, credited), made canonical by forest heights; for each
  run-length routing topology one quartic with exactly `4n+4m+s` natural
  witnesses and `6n+2m+s` residuals of degree at most two, uniform in the
  initial loads and run lengths, with a unique root exactly for terminating
  inputs; a grammar version (`4n+4g+4c+s` witnesses); canonical certificates
  for both outcomes (`UP ∩ coUP`, a second route to the ARRIVAL bound); a
  Presburger description of fixed periods and a transport identity; an
  `NP = coNP` barrier for circuit-defined periods; a universal one-router
  system with polynomial-time prefix ranks; and the theorem that the graph
  of its one monotone Boolean rank function has a single-fold (finite-fold)
  representation exactly when every c.e. set has one, with `2r+3` witnesses
  and degree `max{4,2d}`.
- **13** for distinct perfect matchings `M ≠ N` of `2n` labelled ports and a
  uniformly random closing matching, the parities of the numbers of cyclic
  wires after closing differ with probability between 2/5 and 2/3, both
  sharp (2/3 exactly when `M ∪ N` is one alternating four-cycle plus common
  edges, 2/5 exactly for one six-cycle), by a signed contraction recurrence;
  hence
  any summary that predicts loop parity in every closing context is
  injective on all `(2n−1)!!` matchings and needs `⌈log₂(2n−1)!!⌉` bits,
  `O(n log n)` random one-bit probes separate all matchings (existence; no
  efficient decoder), and a two-edge context separates any two matchings
  modulo every `r ≥ 2`; an exact splice and order-independent gluing; a
  linear-size memory certificate with initial and final arrays; and a
  bounded six-rule quartic compiler with `O(C₀+F+T)` coordinates, printed
  as a second presentation of 14's theorem (a paper construction).
- **14** locality of wire suppression; closed quadratic formulas for the new
  loops and surviving endpoints of a binary annihilation (ten boundary
  patterns) and a sharp ten-state result; a 23-residual quartic kernel with
  a unique 17-coordinate extension; a capped memory certificate with
  exactly `17L−4` auxiliaries and residuals (`16L−4` with a precomputed
  base); a fixed 36-access rewrite step; the bounded quartic family for
  exact scheduled reductions of all six rules, with `O(C₀+f+T)`
  coordinates, one witness per legal schedule and an explicit ledger (a
  paper construction); terminal predicates, a bounded ordinary-integer
  loader for fixed dimensions, and transfer to fixed interaction systems.
- **15** a division-free pair-suppression identity on natural matching
  matrices; a sixteen-port support bound; the path–cycle dictionary
  `cyc(α∘β) = |B|/2 + 2L`; completeness of the summary (boundary matching,
  loop count) for matching contexts; a canonical minimum-and-distance orbit
  certificate with exactly one natural witness for every permutation (`4n`
  witnesses and `5n` quadratic residuals; `5n` and `6n` with a selector
  matrix); a single-fold gluing certificate; an implemented fixed-schedule
  compiler for all six rules with an exact ledger (68 parameters, 126
  witnesses and 169 residuals for the repository's example); a finite
  schedule disjunction; and a lasso up to renaming.

**Status.** The report is AI-assisted and unrefereed. None of its theorems
is formalized in Lean or Rocq, and no manuscript ships Lean or Rocq files.
The Python programs are finite exact checks of the implementations and
examples, not proofs; the proofs are the mathematical arguments of the
article.

## Files

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 338 pages
README.md                                this guide

01-causal-traces-RESEARCH_STATUS.md      manuscript 01's research and verification status, as delivered
01-causal-traces-SOURCE_AUDIT.md         manuscript 01's pin, inspected repository files and literature
02-poly-trajectories-sources.md          manuscript 02's pin and bibliographic provenance
03-linear-memory-SOURCE_PROVENANCE.md    manuscript 03's pin, consulted sources and claim status
04-witness-faithful-SOURCE_AUDIT.md      manuscript 04's source and scope audit
06-counter-schedules-repository_context.md  manuscript 06's repository snapshot and trust boundaries
07-queue-causality-lean_integration.md   manuscript 07's proposed Lean integration (not an implemented formalization)
07-queue-causality-provenance.md         manuscript 07's pin, literature and verification boundaries
08-dynamic-heaps-PROVENANCE.md           manuscript 08's pin, inspected sources, dependencies and verification limits
10-priority-pumping-VALIDATION.md        manuscript 10's delivery validation (PDF build, 114,875 counted checks)
10-priority-pumping-provenance.md        manuscript 10's pin, inspected repository files and literature
12-rle-routing-SOURCES.md                manuscript 12's pinned repository and literature provenance
13-exact-wiring-SOURCES.md               manuscript 13's pinned repository and literature audit
15-no-ghost-wires-CLAIMS.md              manuscript 15's claims and scope ledger
15-no-ghost-wires-PROVENANCE.md          manuscript 15's repository revision, sources and verification limits
16-sandpile-SOURCES.md                   placed by 41e7f1189 (batch 78, cluster H3) for a later Part

code/01-causal-traces-causal_diophantine.py   exact semantics and the four compiler entry points
code/01-causal-traces-demo.py            the 11-witness large-count example (prints; writes no file)
code/01-causal-traces-verify.py          deterministic differential tests (seed 20260930); rewrites its examples and records
code/01-causal-traces-verify_exports.py  separate JSON coefficient checker (does not import the compiler)
code/02-poly-trajectories-certificates.py     sign-tower generator and endpoint checker (command line)
code/02-poly-trajectories-quartic_compiler.py positivity relation -> sum of squares of quadratic residuals
code/02-poly-trajectories-run_tests.py   regression tests (seed 20260930); writes four JSON files into the working directory
code/02-poly-trajectories-verify_export.py    separate assignment checker (prints JSON)
code/03-linear-memory-Makefile           manuscript 03's make targets (test, example, pdf, clean), delivery paths
code/03-linear-memory-canonical_memory.py     sparse polynomials and the low-height bitonic-network memory compiler
code/03-linear-memory-linear_memory.py   the linear-size large-base-product memory compiler
code/03-linear-memory-test_certificates.py    tests of the bitonic backend; rewrites its example and record
code/03-linear-memory-test_linear_memory.py   tests of the linear backend; rewrites its example and record
code/04-witness-faithful-diophantine_compiler.py  Petri, FRACTRAN and SKI compilers
code/04-witness-faithful-run_tests.py    finite checks; rewrites the four examples and its record
code/04-witness-faithful-verify_certificate.py    standalone JSON witness verifier (prints one JSON line per file)
code/05-trace-polytopes-build.py         manuscript 05's check-and-rebuild helper (do not run it here; see below)
code/05-trace-polytopes-demo.py          ordinary and zero-guarded examples; rewrites two result files
code/05-trace-polytopes-trace_polytope.py     exact compiler and witness checker
code/05-trace-polytopes-verify.py        finite checks against independent oracles; rewrites its results
code/06-counter-schedules-compiler.py    expression syntax, resource and normality summaries, quartic compiler
code/06-counter-schedules-substrates.py  polynomial/circuit-to-separated-schedule front end, 320 checks
code/06-counter-schedules-test_compiler.py    49,402 exact finite checks
code/06-counter-schedules-verify_export.py    independent evaluator of exported residuals (prints JSON)
code/07-queue-causality-Makefile         manuscript 07's make targets (pdf, test, examples, clean), delivery paths
code/07-queue-causality-compile_tag.py   general deletion-tag JSON front end
code/07-queue-causality-queue_certificates.py cyclic-tag and deletion-tag compilers (command line)
code/07-queue-causality-run_tests.py     exhaustive and seeded checks; rewrites five examples and its record
code/07-queue-causality-verify_certificate.py independent exact certificate evaluator (prints JSON)
code/08-dynamic-heaps-build.sh           manuscript 08's PDF build script (pdflatex article.tex; do not run it here)
code/08-dynamic-heaps-memory_quartic.py  sparse polynomials, bitonic network, memory residuals and canonical witness
code/08-dynamic-heaps-pointer_machine.py two-stack heaps, memory logs and birth-order normalization
code/08-dynamic-heaps-run_tests.py       exhaustive and seeded checks; rewrites its receipt and both examples
code/09-order-free-assembly_compiler.py  base and terminal assembly compilers, witness constructor, JSON exporter
code/09-order-free-build.sh              manuscript 09's PDF build script (its .tex is not shipped; do not run it here)
code/09-order-free-presburger_gadgets.py unbounded comparison and signed-divisibility penalties
code/09-order-free-verify.py             exact checks; rewrites the four certificates and the report
code/10-priority-pumping-generate_instances.py      writes the two polynomial/witness pairs
code/10-priority-pumping-priority_certificates.py   compiler, simulators, interval checker, capacity (command line)
code/10-priority-pumping-test_priority_certificates.py  finite tests (seed 20260930); rewrites verification.json
code/10-priority-pumping-verify_export.py           independent JSON polynomial evaluator (prints JSON)
code/11-reaction-fallback-reaction_compiler.py      reaction compiler, simulator, trace and minimum-fuel certificates
code/11-reaction-fallback-verify.py      deterministic tests (seed 20260930); writes where --output says
code/12-rle-routing-Makefile             manuscript 12's make targets (all, pdf, test, clean), delivery paths
code/12-rle-routing-compile_quartic.py   sparse compiler for the RLE quartic; writes --output and a .txt beside it
code/12-rle-routing-verify_certificates.py   exact semantics, witnesses, residuals and tests; writes --output
code/13-exact-wiring-Makefile            manuscript 13's make targets (all, paper, test, clean), delivery paths
code/13-exact-wiring-diophantine_memory.py   sparse quadratic memory compiler, canonical witness, quartic export
code/13-exact-wiring-parity.py           signed closure recurrence, partitions, representative matching pairs
code/13-exact-wiring-verify.py           finite checks; compares with its recorded receipt, rewrites it only with --write
code/13-exact-wiring-wiring.py           six-rule evaluator, splice and component gluing, separating contexts
code/14-net-topology-Makefile            manuscript 14's make targets (all, test, pdf, clean), delivery paths
code/14-net-topology-certificates.py     sparse quadratic systems, witness generators, quartic exporters
code/14-net-topology-nets.py             six-rule templates; component and local-formula reducers
code/14-net-topology-verify.py           finite checks (seed 20261002); rewrites three quartics and verification.json
code/14-net-topology-verify_exports.py   independent JSON quartic checker; rewrites export_audit.json
code/15-no-ghost-wires-build.sh          manuscript 15's three-pass PDF build (its .tex is not shipped; do not run it here)
code/15-no-ghost-wires-check_export.py   independent evaluator of the exported example (prints one line)
code/15-no-ghost-wires-loop_exact.py     net semantics, templates, orbit certificate, scheduled compiler, witness
code/15-no-ghost-wires-verify.py         finite checks; rewrites four data files and writes verification.txt
code/16-sandpile-build.sh                placed by 41e7f1189 (batch 78, cluster H3) for a later Part
code/16-sandpile-sandpile_compact.py     (the same)
code/16-sandpile-sandpile_cubic.py       (the same)
code/16-sandpile-sandpile_spatial.py     (the same)
code/16-sandpile-verify.py               (the same)
code/16-sandpile-verify_compact.py       (the same)
code/16-sandpile-verify_spatial.py       (the same)

data/01-causal-traces-build_validation.json   build and rendering record of the delivered 29-page PDF
data/01-causal-traces-canonical_history.json  32-witness, 48-residual causal-history polynomial and certificate
data/01-causal-traces-export_verification.json    recorded run of verify_exports.py
data/01-causal-traces-shared_resource_accelerator.json  11-witness, 18-residual, 76-monomial quartic and certificate
data/01-causal-traces-verification.json  recorded run of verify.py (Python 3.13.5)
data/01-causal-traces-verification.txt   the same run as text
data/02-poly-trajectories-huge_horizon_certificate.json  p(t) = (t - 10^50)^2, T = 10^100
data/02-poly-trajectories-independent_verification.json  recorded output of verify_export.py on quartic_example.json
data/02-poly-trajectories-interior_counterexample.json   p(t) = t^2 - 6t + 8, T = 6 (outer endpoints do not suffice)
data/02-poly-trajectories-quartic_example.json      template and assignment for p(t) = t^2 - 4t + 4, T = 6
data/02-poly-trajectories-test_report.json          recorded run of run_tests.py
data/03-linear-memory-build_validation.json         build record of the delivered 31-page PDF
data/03-linear-memory-example-certificate.json      four-event log, bitonic backend: certificate and assignment
data/03-linear-memory-example-events.json           the four-event log
data/03-linear-memory-example-polynomial.json       its expanded sum of squares
data/03-linear-memory-linear_example-certificate.json   the same log, linear backend (12 parameters, 96 witnesses, 89 residuals)
data/03-linear-memory-linear_example-events.json    the same log (identical to example-events.json)
data/03-linear-memory-linear_example-polynomial.json    its expanded sum of squares
data/03-linear-memory-linear_test_results.json      recorded run of test_linear_memory.py
data/03-linear-memory-linear_test_run.txt           its console output (identical bytes)
data/03-linear-memory-test_results.json             recorded run of test_certificates.py
data/03-linear-memory-test_run.txt                  its console output (identical bytes)
data/04-witness-faithful-certificate_verification.jsonl  recorded verifier output on the four examples
data/04-witness-faithful-fractran_first_halt.json   FRACTRAN first-halting certificate (103 variables, 120 residuals)
data/04-witness-faithful-petri_fork_join.json       Petri fork-join certificate (56 variables, 67 residuals)
data/04-witness-faithful-results.json               recorded run of run_tests.py
data/04-witness-faithful-ski_SKII.json              SKI certificate for SKII (13 variables, 11 residuals)
data/04-witness-faithful-ski_context.json           context-local SKI certificate (8 variables, 8 residuals)
data/05-trace-polytopes-demo_stdout.txt             recorded output of demo.py
data/05-trace-polytopes-example_guarded.json        exported zero-guarded certificate
data/05-trace-polytopes-example_quadratic.json      exported quadratic certificate
data/05-trace-polytopes-example_quartic.json        exported quartic certificate
data/05-trace-polytopes-example_raw.json            exported raw-run certificate
data/05-trace-polytopes-tiny_expanded_polynomial.txt    a small explicit expansion
data/05-trace-polytopes-verification.json           recorded run of verify.py
data/05-trace-polytopes-verification_stdout.txt     its console output (identical bytes)
data/05-trace-polytopes-witness_guarded.json        witness for example_guarded.json
data/05-trace-polytopes-witness_quadratic.json      witness for example_quadratic.json
data/05-trace-polytopes-witness_quartic.json        witness for example_quartic.json
data/05-trace-polytopes-witness_raw.json            witness for example_raw.json
data/06-counter-schedules-canonical_huge_witness.json    309-witness assignment; execution length has 221 digits
data/06-counter-schedules-canonical_multiplication_certificate.json  canonical polynomial (309 witnesses, 547 residuals)
data/06-counter-schedules-determinism_check.json    recorded comparison of two main-suite runs (hash seeds 1, 2)
data/06-counter-schedules-export_canonical_check.json   recorded verify_export.py output, canonical example
data/06-counter-schedules-export_resource_check.json    recorded verify_export.py output, resource-only example
data/06-counter-schedules-multiplication_certificate.json  resource-only polynomial (79 witnesses, 86 residuals)
data/06-counter-schedules-multiplication_witness.json      its 79-witness assignment
data/06-counter-schedules-pdf_quality.json          build and rendering record of the delivered 30-page PDF
data/06-counter-schedules-substrate_results.json    recorded run of substrates.py (320 checks)
data/06-counter-schedules-test_results.json         recorded run of test_compiler.py (49,402 checks)
data/07-queue-causality-quartic_example.json        T = 3 local quartic (7 variables, 9 residuals)
data/07-queue-causality-results.json                recorded run of run_tests.py
data/07-queue-causality-stream_example.json         T = 3 stream certificate (4 variables, 6 residuals)
data/07-queue-causality-ternary_tag_example.json    certificate for the ternary 2-tag program (5 variables)
data/07-queue-causality-ternary_tag_spec.json       that program's specification
data/07-queue-causality-uncausal_counterexample.json    word balance without a legal execution
data/07-queue-causality-zero_slack_example.json     T = 3 zero-slack certificate (3 variables)
data/08-dynamic-heaps-memory_certificate.json       worked five-event log: 15 source, 269 auxiliary coordinates, 292 residuals
data/08-dynamic-heaps-memory_events.json            the five-event log
data/08-dynamic-heaps-receipt.json                  recorded run of run_tests.py (seed, coverage, elapsed time)
data/09-order-free-alternative_star_certificate.json    star with two north labels (terminal certificate, 301 variables, 230 rows)
data/09-order-free-capped_star_certificate.json     capped four-arm star (terminal certificate, 256 variables, 196 rows)
data/09-order-free-cooperative_square_certificate.json  temperature-two cooperative square (terminal, 297 variables, 231 rows)
data/09-order-free-diamond_certificate.json         two-by-two diamond (base certificate, 133 variables, 103 rows)
data/09-order-free-verification_report.json         recorded run of verify.py
data/10-priority-pumping-example_certificate.json   uniform two-rule, two-coordinate schema (155 auxiliaries, 177 residuals)
data/10-priority-pumping-example_instance.json      witness for two applications of rule 2 in (1/72, 3/2)
data/10-priority-pumping-independent_example_check.json   recorded verify_export.py output on the example
data/10-priority-pumping-independent_large_check.json     recorded verify_export.py output on the large instance
data/10-priority-pumping-large_maximal_certificate.json   maximality schema for (3/2) (184 auxiliaries, 212 residuals)
data/10-priority-pumping-large_maximal_instance.json      witness for 10^1000 repetitions
data/10-priority-pumping-test_output.txt            console output of the tests (identical bytes to verification.json)
data/10-priority-pumping-verification.json          recorded test report (114,875 counted checks)
data/11-reaction-fallback-doubling_T8_quartic.json  expanded T = 8 quartic of the doubling machine (3,202 monomials)
data/11-reaction-fallback-doubling_T8_residuals.json    its 781 quadratic residuals
data/11-reaction-fallback-doubling_T8_witness.json  its 420-coordinate witness for n = f = 1
data/11-reaction-fallback-example_summary.json      generated counts and degree check
data/11-reaction-fallback-results.json              recorded run of verify.py
data/11-reaction-fallback-universal_61_species_62_reactions.json  the universal network, machine-readable
data/11-reaction-fallback-universal_reactions.txt   its 62 reactions with priority labels
data/12-rle-routing-example_quartic.json            period v^3 s, fixed lengths: 13 witnesses, 11 residuals, 50 monomials
data/12-rle-routing-example_quartic.txt             the same, human-readable
data/12-rle-routing-parametric_quartic.json         the same topology, both lengths free: 81 monomials
data/12-rle-routing-parametric_quartic.txt          the same, human-readable
data/12-rle-routing-test_results.json               recorded run of verify_certificates.py: PASS
data/13-exact-wiring-build_receipt.json            build and rendering record of the delivered 28-page PDF
data/13-exact-wiring-example_memory_certificate.json   A = 3, m = 5, V = 8: 21 parameters, 167 witnesses, 144 residuals, 2,496 monomials
data/13-exact-wiring-verification.json             recorded receipt of verify.py (Python 3.13.5), with source hashes
data/14-net-topology-delta_loop_quartic.json       delta kernel: 6 source fields, 17 auxiliaries, 23 residuals, 104 monomials
data/14-net-topology-export_audit.json             recorded run of verify_exports.py
data/14-net-topology-gamma_loop_quartic.json       gamma kernel, the same counts
data/14-net-topology-memory_example_quartic.json   four-access log, A = 4, V = 10: 12 source fields, 64 auxiliaries, 64 residuals, 402 monomials
data/14-net-topology-pdf_quality.json              build and rendering record of the delivered 23-page PDF
data/14-net-topology-source_audit.json             manuscript 14's pin, inspected repository files and literature
data/14-net-topology-verification.json             recorded run of verify.py (seed 20261002)
data/15-no-ghost-wires-endpoints.json              the repository's two distinguishing nets and the target
data/15-no-ghost-wires-quartic_A_schedule.json     the example: 169 residuals, 68 parameters, 126 witnesses
data/15-no-ghost-wires-verification.json           recorded run of verify.py (with a runtime field)
data/15-no-ghost-wires-witness_A.json              the unique witness for net A
data/16-sandpile-BUILD_REPORT.json                 placed by 41e7f1189 (batch 78, cluster H3) for a later Part
data/16-sandpile-compact_huge_input_certificate.json   (the same)
data/16-sandpile-compact_two_site_polynomial.json  (the same)
data/16-sandpile-compact_two_site_polynomial.txt   (the same)
data/16-sandpile-huge_input_certificate.json       (the same)
data/16-sandpile-requirements.txt                  (the same)
data/16-sandpile-two_site_polynomial.json          (the same)
data/16-sandpile-two_site_polynomial.txt           (the same)
data/16-sandpile-verification.json                 (the same)
data/16-sandpile-verification_compact.json         (the same)
data/16-sandpile-verification_spatial.json         (the same)
```

The directory holds 196 files: 19 at the root (the article, its PDF, this
README and sixteen provenance and audit files), 67 in `code/` and 110 in
`data/`. Per manuscript: 01 has 12 files, 02 10, 03 17, 04 10, 05 16
besides the replaced `article.tex` and `README.md`, 06 15, 07 14, 08 8, 09
9, 10 14, 11 9, 12 9, 13 9, 14 12 and 15 10. Every file of manuscripts 01–15 except `article.tex`, `article.pdf` and
`README.md` is byte-identical to the delivery. The nineteen files
`16-sandpile-*` (1 at the root, 7 in `code/`, 11 in `data/`) were placed by
`41e7f1189` (batch 78, cluster H3) for a Part that has not been written yet;
this README does not describe them.

## Labels

Every label in `article.tex` carries the prefix `cdc:`. Labels of manuscript
05 (the base) take the prefix alone (`cdc:thm:main`); those of the other
manuscripts take a sub-prefix:

| Manuscript | Sub-prefix | Example |
|---|---|---|
| 01 | `cdc:ct:` | `cdc:ct:thm:universal` |
| 02 | `cdc:pt:` | `cdc:pt:prop:height` |
| 03 | `cdc:mem:` | `cdc:mem:prop:lower` |
| 04 | `cdc:wf:` | `cdc:wf:thm:petri` |
| 05 | `cdc:` | `cdc:thm:quartic` |
| 06 | `cdc:cs:` | `cdc:cs:thm:tracebijection` |
| 07 | `cdc:qc:` | `cdc:qc:thm:stream` |
| 08 | `cdc:nh:` | `cdc:nh:thm:names` |
| 09 | `cdc:of:` | `cdc:of:thm:classification` |
| 10 | `cdc:pf:` | `cdc:pf:thm:pumping` |
| 11 | `cdc:rx:` | `cdc:rx:thm:FF` |
| 12 | `cdc:rt:` | `cdc:rt:thm:bottleneck` |
| 13 | `cdc:ew:` | `cdc:ew:thm:sharp` |
| 14 | `cdc:nt:` | `cdc:nt:thm:main` |
| 15 | `cdc:ng:` | `cdc:ng:thm:orbit` |

Labels written in the merge use `cdc:conv:` (the Conventions section),
`cdc:bd:` (merged statements of Part IX, such as the universal-halting
equivalence `cdc:bd:thm:universal` and the no-computable-witness-bound
proposition `cdc:bd:prop:nobound`), `cdc:part:` (the Parts),
`cdc:sec:` (the back-matter sections, for example `cdc:sec:validation`,
`cdc:sec:formal`, `cdc:sec:questions`, `cdc:sec:provenance`; base 05's own
thirteen section labels also begin `cdc:sec:`) and `cdc:q:` (merged
research questions). Labels written in the merge also include section labels in a manuscript's own namespace where that manuscript left a section unlabelled (`cdc:wf:sec:interfaces`, `cdc:wf:sec:monitor`, `cdc:wf:sec:ski`, `cdc:wf:sec:frontier`, `cdc:pt:sec:problem`, `cdc:pt:sec:firsthalt`, `cdc:pt:sec:limits`, `cdc:qc:sec:words`) and two remarks (`cdc:bd:rem:sfu`, `cdc:qc:rem:tagnotes`).

Label counts (pattern `\\label(\[[^]]*\])?\{`): the placed `article.tex` (manuscript 05 as delivered) had 70 labels, all bare. The written article has 523: all 475 labels of the seven manuscripts (01 74, 02 59, 03 76, 04 65, 05 70, 06 77, 07 54), each with its prefix and none dropped, and 48 labels written in the merge. None is duplicated. Where a duplicated statement is printed once, the labels of the statements it replaces sit on the merged statement (`cdc:thm:boundary`, `cdc:ct:thm:universal`, `cdc:mem:thm:compression` and `cdc:wf:thm:universal` on `cdc:bd:thm:universal`; `cdc:prop:noheight`, `cdc:ct:prop:no-bound`, `cdc:pt:prop:height`, `cdc:mem:prop:no-bound` and `cdc:wf:thm:height-obstruction` on `cdc:bd:prop:nobound`), and the section labels of the manuscripts' research-question sections sit on the merged Research questions section, so every reference resolves.

The batch-62 write (Parts X–XIII) raised the count from 523 to 840. It adds
all 292 labels of manuscripts 08–11 (08 55, 09 68, 10 87, 11 82), each with
its sub-prefix and none dropped, and 25 written labels: the four Parts
(`cdc:part:heaps`, `cdc:part:assembly`, `cdc:part:pumping`,
`cdc:part:reactions`), their conventions sections (`cdc:conv:b62-08` …
`cdc:conv:b62-11`), the paragraph on their questions (`cdc:conv:b62q`), the
four manuscript subsections (`cdc:sec:ms08` … `cdc:sec:ms11`), manuscript
09's three parts, which are sections here (`cdc:of:sec:degree`,
`cdc:of:sec:assembly`, `cdc:of:sec:reproduction`), and nine labels put on
existing, previously unlabelled questions so that the new Parts can cite
them (`cdc:q:interfaces`, `cdc:q:acceleration`, `cdc:q:sizeheight`,
`cdc:q:scalar`, `cdc:q:routing`, `cdc:q:locality`, `cdc:q:graphfront`,
`cdc:q:repsize`, `cdc:q:ffprimitives`). No existing label was renamed,
removed or renumbered: the 523 labels of the previous build have the same
numbers and types in the new `.aux`. The equations of Parts X–XIII, and of
manuscript 10's introduction in Section 3.10, are numbered within their
sections or subsections for that reason, so that the appendices keep their
equation numbers.

The batch-63 write (Part XIV) raised the count from 840 to 916. It adds all
69 labels of manuscript 12, each with the sub-prefix `cdc:rt:` and none
dropped (its bare `thm:universal`, `lem:bound` and `sec:intro` would
otherwise have repeated labels of other members), and 7 written labels: the
Part (`cdc:part:routing`), its conventions section (`cdc:conv:b63-XIV`), the
manuscript subsection (`cdc:sec:ms12`), manuscript 12's two appendices,
which are sections here (`cdc:rt:app:reproduction`,
`cdc:rt:app:dependencies`), and two labels put on existing, previously
unlabelled questions so that Part XIV and the notes can cite them
(`cdc:q:beyond`, "Beyond translations"; `cdc:q:varperiods`, "Variable
periods and variable degrees"). No existing label was renamed, removed or
renumbered: the 840 labels of the batch-62 build have the same numbers and
types in the new `.aux` (compared entry by entry). Part XIV's equations are
numbered within its sections, as in Parts X–XIII.

The batch-78 write (Part XV) raised the count from 916 to 1105. It adds all
128 labels of manuscripts 13–15 (13 63, 14 16, 15 49), each with its
sub-prefix and none dropped (13 and 14 share the bare names `lem:product`,
`prop:height`, `thm:glue` and `thm:memory`, and 13 and 15 share
`thm:compiler`, `sec:compiler` and `sec:future`), and 61 written labels: the
Part (`cdc:part:wiring`), its conventions section (`cdc:conv:b78-wiring`),
the three manuscript subsections (`cdc:sec:ms13` … `cdc:sec:ms15`), twelve
sections and subsections written in the merge under the sub-prefix
`cdc:ic:` (`cdc:ic:sec:nets`, `…:example`, `…:gluing`, `…:context`,
`…:kernel`, `…:memory`, `…:memcompare`, `…:compiler`, `…:orbits`,
`…:boundaries`, `…:validation`, `…:questions`), nine section and appendix
labels in manuscript 14's namespace (`cdc:nt:sec:intro`, `…:nets`, `…:glue`,
`…:kernel`, `…:memhist`, `…:machine`, `…:main`, `…:boundaries`,
`cdc:nt:app:sources`), because 14 left its sections unlabelled and cited
them by number, the 34 equation labels `cdc:nt:eq:2.1` … `cdc:nt:eq:11.1`,
which replace 14's hand-set `\tag` numbers and keep them in their names
(`cdc:nt:eq:3.3` is printed as (143.3)), and `cdc:nh:q:frontend`, put on
Part X's existing, previously unlabelled question "A complete
interaction-combinator frontend" so that Part XV and the notes can cite it.
No existing label was renamed, removed or renumbered: the 916 labels of the
batch-63 build have the same numbers in the new `.aux` (compared entry by
entry). Part XV's equations are numbered within its sections, and those of
Sections 3.13–3.15 within subsections; table numbers after Part XV did not
move, because no captioned table follows it.

Text written during the merge is marked `[write]` in the article.

## Delivered names and shipped names

Delivered paths are relative to each manuscript's package root (the inner
directory of its archive). Base 05's `README.md` and `article.tex` were
staged unprefixed and are replaced in place by this README and the merged
article; the delivered texts survive at the placement commit `7498484af`
and in the arrival commit `c1f56f842`.

**Manuscript 01** (package root `Diophantine_Causal_Computation/`)

| Delivered | Shipped |
|---|---|
| `RESEARCH_STATUS.md` | `01-causal-traces-RESEARCH_STATUS.md` |
| `SOURCE_AUDIT.md` | `01-causal-traces-SOURCE_AUDIT.md` |
| `code/causal_diophantine.py` | `code/01-causal-traces-causal_diophantine.py` |
| `code/demo.py` | `code/01-causal-traces-demo.py` |
| `code/verify.py` | `code/01-causal-traces-verify.py` |
| `code/verify_exports.py` | `code/01-causal-traces-verify_exports.py` |
| `data/build_validation.json` | `data/01-causal-traces-build_validation.json` |
| `data/export_verification.json` | `data/01-causal-traces-export_verification.json` |
| `data/verification.json` | `data/01-causal-traces-verification.json` |
| `data/verification.txt` | `data/01-causal-traces-verification.txt` |
| `examples/canonical_history.json` | `data/01-causal-traces-canonical_history.json` |
| `examples/shared_resource_accelerator.json` | `data/01-causal-traces-shared_resource_accelerator.json` |

**Manuscript 02** (package root `canonical_diophantine_certificates/`; flat)

| Delivered | Shipped |
|---|---|
| `certificates.py` | `code/02-poly-trajectories-certificates.py` |
| `huge_horizon_certificate.json` | `data/02-poly-trajectories-huge_horizon_certificate.json` |
| `independent_verification.json` | `data/02-poly-trajectories-independent_verification.json` |
| `interior_counterexample.json` | `data/02-poly-trajectories-interior_counterexample.json` |
| `quartic_compiler.py` | `code/02-poly-trajectories-quartic_compiler.py` |
| `quartic_example.json` | `data/02-poly-trajectories-quartic_example.json` |
| `run_tests.py` | `code/02-poly-trajectories-run_tests.py` |
| `sources.md` | `02-poly-trajectories-sources.md` |
| `test_report.json` | `data/02-poly-trajectories-test_report.json` |
| `verify_export.py` | `code/02-poly-trajectories-verify_export.py` |

**Manuscript 03** (package root `ProveIt_Diophantine_Certificates/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/03-linear-memory-Makefile` |
| `SOURCE_PROVENANCE.md` | `03-linear-memory-SOURCE_PROVENANCE.md` |
| `artifacts/build_validation.json` | `data/03-linear-memory-build_validation.json` |
| `artifacts/example/certificate.json` | `data/03-linear-memory-example-certificate.json` |
| `artifacts/example/events.json` | `data/03-linear-memory-example-events.json` |
| `artifacts/example/polynomial.json` | `data/03-linear-memory-example-polynomial.json` |
| `artifacts/linear_example/certificate.json` | `data/03-linear-memory-linear_example-certificate.json` |
| `artifacts/linear_example/events.json` | `data/03-linear-memory-linear_example-events.json` |
| `artifacts/linear_example/polynomial.json` | `data/03-linear-memory-linear_example-polynomial.json` |
| `artifacts/linear_test_results.json` | `data/03-linear-memory-linear_test_results.json` |
| `artifacts/linear_test_run.txt` | `data/03-linear-memory-linear_test_run.txt` |
| `artifacts/test_results.json` | `data/03-linear-memory-test_results.json` |
| `artifacts/test_run.txt` | `data/03-linear-memory-test_run.txt` |
| `code/canonical_memory.py` | `code/03-linear-memory-canonical_memory.py` |
| `code/linear_memory.py` | `code/03-linear-memory-linear_memory.py` |
| `code/test_certificates.py` | `code/03-linear-memory-test_certificates.py` |
| `code/test_linear_memory.py` | `code/03-linear-memory-test_linear_memory.py` |

**Manuscript 04** (package root `diophantine_substrates/`)

| Delivered | Shipped |
|---|---|
| `code/diophantine_compiler.py` | `code/04-witness-faithful-diophantine_compiler.py` |
| `code/verify_certificate.py` | `code/04-witness-faithful-verify_certificate.py` |
| `examples/fractran_first_halt.json` | `data/04-witness-faithful-fractran_first_halt.json` |
| `examples/petri_fork_join.json` | `data/04-witness-faithful-petri_fork_join.json` |
| `examples/ski_SKII.json` | `data/04-witness-faithful-ski_SKII.json` |
| `examples/ski_context.json` | `data/04-witness-faithful-ski_context.json` |
| `research/SOURCE_AUDIT.md` | `04-witness-faithful-SOURCE_AUDIT.md` |
| `tests/certificate_verification.jsonl` | `data/04-witness-faithful-certificate_verification.jsonl` |
| `tests/results.json` | `data/04-witness-faithful-results.json` |
| `tests/run_tests.py` | `code/04-witness-faithful-run_tests.py` |

**Manuscript 05** (package root `canonical_trace_polytopes/`; the base)

| Delivered | Shipped |
|---|---|
| `README.md` | `README.md` (replaced by this README) |
| `article.tex` | `article.tex` (replaced by the merged article) |
| `build.py` | `code/05-trace-polytopes-build.py` |
| `code/demo.py` | `code/05-trace-polytopes-demo.py` |
| `code/trace_polytope.py` | `code/05-trace-polytopes-trace_polytope.py` |
| `code/verify.py` | `code/05-trace-polytopes-verify.py` |
| `results/demo_stdout.txt` | `data/05-trace-polytopes-demo_stdout.txt` |
| `results/example_guarded.json` | `data/05-trace-polytopes-example_guarded.json` |
| `results/example_quadratic.json` | `data/05-trace-polytopes-example_quadratic.json` |
| `results/example_quartic.json` | `data/05-trace-polytopes-example_quartic.json` |
| `results/example_raw.json` | `data/05-trace-polytopes-example_raw.json` |
| `results/tiny_expanded_polynomial.txt` | `data/05-trace-polytopes-tiny_expanded_polynomial.txt` |
| `results/verification.json` | `data/05-trace-polytopes-verification.json` |
| `results/verification_stdout.txt` | `data/05-trace-polytopes-verification_stdout.txt` |
| `results/witness_guarded.json` | `data/05-trace-polytopes-witness_guarded.json` |
| `results/witness_quadratic.json` | `data/05-trace-polytopes-witness_quadratic.json` |
| `results/witness_quartic.json` | `data/05-trace-polytopes-witness_quartic.json` |
| `results/witness_raw.json` | `data/05-trace-polytopes-witness_raw.json` |

**Manuscript 06** (package root `diophantine_counter_programs/`)

| Delivered | Shipped |
|---|---|
| `code/compiler.py` | `code/06-counter-schedules-compiler.py` |
| `code/substrates.py` | `code/06-counter-schedules-substrates.py` |
| `code/test_compiler.py` | `code/06-counter-schedules-test_compiler.py` |
| `code/verify_export.py` | `code/06-counter-schedules-verify_export.py` |
| `examples/canonical_huge_witness.json` | `data/06-counter-schedules-canonical_huge_witness.json` |
| `examples/canonical_multiplication_certificate.json` | `data/06-counter-schedules-canonical_multiplication_certificate.json` |
| `examples/multiplication_certificate.json` | `data/06-counter-schedules-multiplication_certificate.json` |
| `examples/multiplication_witness.json` | `data/06-counter-schedules-multiplication_witness.json` |
| `repository_context.md` | `06-counter-schedules-repository_context.md` |
| `verification/determinism_check.json` | `data/06-counter-schedules-determinism_check.json` |
| `verification/export_canonical_check.json` | `data/06-counter-schedules-export_canonical_check.json` |
| `verification/export_resource_check.json` | `data/06-counter-schedules-export_resource_check.json` |
| `verification/pdf_quality.json` | `data/06-counter-schedules-pdf_quality.json` |
| `verification/substrate_results.json` | `data/06-counter-schedules-substrate_results.json` |
| `verification/test_results.json` | `data/06-counter-schedules-test_results.json` |

**Manuscript 07** (package root `Causal_Diophantine_Queue_Compilation/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/07-queue-causality-Makefile` |
| `code/compile_tag.py` | `code/07-queue-causality-compile_tag.py` |
| `code/queue_certificates.py` | `code/07-queue-causality-queue_certificates.py` |
| `code/verify_certificate.py` | `code/07-queue-causality-verify_certificate.py` |
| `examples/quartic_example.json` | `data/07-queue-causality-quartic_example.json` |
| `examples/stream_example.json` | `data/07-queue-causality-stream_example.json` |
| `examples/ternary_tag_example.json` | `data/07-queue-causality-ternary_tag_example.json` |
| `examples/ternary_tag_spec.json` | `data/07-queue-causality-ternary_tag_spec.json` |
| `examples/uncausal_counterexample.json` | `data/07-queue-causality-uncausal_counterexample.json` |
| `examples/zero_slack_example.json` | `data/07-queue-causality-zero_slack_example.json` |
| `notes/lean_integration.md` | `07-queue-causality-lean_integration.md` |
| `notes/provenance.md` | `07-queue-causality-provenance.md` |
| `tests/results.json` | `data/07-queue-causality-results.json` |
| `tests/run_tests.py` | `code/07-queue-causality-run_tests.py` |

**Manuscript 08** (package root `Names_to_Numbers/`)

| Delivered | Shipped |
|---|---|
| `PROVENANCE.md` | `08-dynamic-heaps-PROVENANCE.md` |
| `build.sh` | `code/08-dynamic-heaps-build.sh` |
| `code/memory_quartic.py` | `code/08-dynamic-heaps-memory_quartic.py` |
| `code/pointer_machine.py` | `code/08-dynamic-heaps-pointer_machine.py` |
| `examples/memory_certificate.json` | `data/08-dynamic-heaps-memory_certificate.json` |
| `examples/memory_events.json` | `data/08-dynamic-heaps-memory_events.json` |
| `tests/receipt.json` | `data/08-dynamic-heaps-receipt.json` |
| `tests/run_tests.py` | `code/08-dynamic-heaps-run_tests.py` |

**Manuscript 09** (package root `order_free_diophantine/`)

| Delivered | Shipped |
|---|---|
| `build.sh` | `code/09-order-free-build.sh` |
| `code/assembly_compiler.py` | `code/09-order-free-assembly_compiler.py` |
| `code/presburger_gadgets.py` | `code/09-order-free-presburger_gadgets.py` |
| `code/verify.py` | `code/09-order-free-verify.py` |
| `data/alternative_star_certificate.json` | `data/09-order-free-alternative_star_certificate.json` |
| `data/capped_star_certificate.json` | `data/09-order-free-capped_star_certificate.json` |
| `data/cooperative_square_certificate.json` | `data/09-order-free-cooperative_square_certificate.json` |
| `data/diamond_certificate.json` | `data/09-order-free-diamond_certificate.json` |
| `data/verification_report.json` | `data/09-order-free-verification_report.json` |

**Manuscript 10** (package root `priority_fractran_research/`)

| Delivered | Shipped |
|---|---|
| `VALIDATION.md` | `10-priority-pumping-VALIDATION.md` |
| `provenance.md` | `10-priority-pumping-provenance.md` |
| `code/generate_instances.py` | `code/10-priority-pumping-generate_instances.py` |
| `code/priority_certificates.py` | `code/10-priority-pumping-priority_certificates.py` |
| `code/test_priority_certificates.py` | `code/10-priority-pumping-test_priority_certificates.py` |
| `code/verify_export.py` | `code/10-priority-pumping-verify_export.py` |
| `results/example_certificate.json` | `data/10-priority-pumping-example_certificate.json` |
| `results/example_instance.json` | `data/10-priority-pumping-example_instance.json` |
| `results/independent_example_check.json` | `data/10-priority-pumping-independent_example_check.json` |
| `results/independent_large_check.json` | `data/10-priority-pumping-independent_large_check.json` |
| `results/large_maximal_certificate.json` | `data/10-priority-pumping-large_maximal_certificate.json` |
| `results/large_maximal_instance.json` | `data/10-priority-pumping-large_maximal_instance.json` |
| `results/test_output.txt` | `data/10-priority-pumping-test_output.txt` |
| `results/verification.json` | `data/10-priority-pumping-verification.json` |

**Manuscript 11** (package root `one_shared_fallback/`)

| Delivered | Shipped |
|---|---|
| `code/reaction_compiler.py` | `code/11-reaction-fallback-reaction_compiler.py` |
| `code/verify.py` | `code/11-reaction-fallback-verify.py` |
| `examples/doubling_T8_quartic.json` | `data/11-reaction-fallback-doubling_T8_quartic.json` |
| `examples/doubling_T8_residuals.json` | `data/11-reaction-fallback-doubling_T8_residuals.json` |
| `examples/doubling_T8_witness.json` | `data/11-reaction-fallback-doubling_T8_witness.json` |
| `examples/example_summary.json` | `data/11-reaction-fallback-example_summary.json` |
| `examples/universal_61_species_62_reactions.json` | `data/11-reaction-fallback-universal_61_species_62_reactions.json` |
| `examples/universal_reactions.txt` | `data/11-reaction-fallback-universal_reactions.txt` |
| `verification/results.json` | `data/11-reaction-fallback-results.json` |

**Manuscript 12** (package root `diophantine_certificates/`; flat)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/12-rle-routing-Makefile` |
| `SOURCES.md` | `12-rle-routing-SOURCES.md` |
| `compile_quartic.py` | `code/12-rle-routing-compile_quartic.py` |
| `example_quartic.json` | `data/12-rle-routing-example_quartic.json` |
| `example_quartic.txt` | `data/12-rle-routing-example_quartic.txt` |
| `parametric_quartic.json` | `data/12-rle-routing-parametric_quartic.json` |
| `parametric_quartic.txt` | `data/12-rle-routing-parametric_quartic.txt` |
| `test_results.json` | `data/12-rle-routing-test_results.json` |
| `verify_certificates.py` | `code/12-rle-routing-verify_certificates.py` |

Manuscript 12's section and theorem numbers, which its delivered README
cites, map as follows: Theorem 3.1 = `cdc:rt:thm:rle`, Theorem 4.1 =
`cdc:rt:thm:grammar`, Theorem 7.1 = `cdc:rt:thm:universal`, Theorem 8.1 =
`cdc:rt:thm:bottleneck` (Theorems 128.1, 129.1, 132.1 and 133.1 in the
article); its Sections 2–11 are Sections 127–136 of the article and its
Appendices A–B Sections 137–138.

**Manuscript 13** (package root `Exact_Wiring_Diophantine/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/13-exact-wiring-Makefile` |
| `SOURCES.md` | `13-exact-wiring-SOURCES.md` |
| `code/diophantine_memory.py` | `code/13-exact-wiring-diophantine_memory.py` |
| `code/parity.py` | `code/13-exact-wiring-parity.py` |
| `code/verify.py` | `code/13-exact-wiring-verify.py` |
| `code/wiring.py` | `code/13-exact-wiring-wiring.py` |
| `results/build_receipt.json` | `data/13-exact-wiring-build_receipt.json` |
| `results/example_memory_certificate.json` | `data/13-exact-wiring-example_memory_certificate.json` |
| `results/verification.json` | `data/13-exact-wiring-verification.json` |

**Manuscript 14** (package root `Interaction_Net_Diophantine/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/14-net-topology-Makefile` |
| `code/certificates.py` | `code/14-net-topology-certificates.py` |
| `code/nets.py` | `code/14-net-topology-nets.py` |
| `code/verify.py` | `code/14-net-topology-verify.py` |
| `code/verify_exports.py` | `code/14-net-topology-verify_exports.py` |
| `data/delta_loop_quartic.json` | `data/14-net-topology-delta_loop_quartic.json` |
| `data/export_audit.json` | `data/14-net-topology-export_audit.json` |
| `data/gamma_loop_quartic.json` | `data/14-net-topology-gamma_loop_quartic.json` |
| `data/memory_example_quartic.json` | `data/14-net-topology-memory_example_quartic.json` |
| `data/pdf_quality.json` | `data/14-net-topology-pdf_quality.json` |
| `data/source_audit.json` | `data/14-net-topology-source_audit.json` |
| `data/verification.json` | `data/14-net-topology-verification.json` |

**Manuscript 15** (package root `no_ghost_wires/`)

| Delivered | Shipped |
|---|---|
| `CLAIMS.md` | `15-no-ghost-wires-CLAIMS.md` |
| `PROVENANCE.md` | `15-no-ghost-wires-PROVENANCE.md` |
| `build.sh` | `code/15-no-ghost-wires-build.sh` |
| `code/check_export.py` | `code/15-no-ghost-wires-check_export.py` |
| `code/loop_exact.py` | `code/15-no-ghost-wires-loop_exact.py` |
| `code/verify.py` | `code/15-no-ghost-wires-verify.py` |
| `data/endpoints.json` | `data/15-no-ghost-wires-endpoints.json` |
| `data/quartic_A_schedule.json` | `data/15-no-ghost-wires-quartic_A_schedule.json` |
| `data/verification.json` | `data/15-no-ghost-wires-verification.json` |
| `data/witness_A.json` | `data/15-no-ghost-wires-witness_A.json` |

Delivered numbers cited by delivered text map as follows. 15's shipped
`CLAIMS.md` cites "article equations (22) and (23)": they are
`cdc:ng:eq:variables` and `cdc:ng:eq:residuals`, equations (146.17) and
(146.18) of the article. 13's delivered README (not shipped) cites its
Theorem 3.1, Section 4, Theorem 7.1 and Theorem 9.1: `cdc:ew:thm:sharp`
(Theorem 142.1), `cdc:ew:sec:tomography` (Section 142.2),
`cdc:ew:thm:memory` (Theorem 144.4) and `cdc:ew:thm:compiler` (Remark
145.5). 14's equation `(N.M)` is `cdc:nt:eq:N.M`. Part XV is Sections
139–156 of the article: 139 its conventions, 140–149 its ten subject
sections, 150 13's Appendix A, 151–153 14's Appendices A–C and 154–156
15's Appendices A–C; 13's Appendix B and 14's Appendix D are subsections
K.1 and K.2 of the provenance appendix.

**Not shipped.** The manuscripts (`article.tex`) and delivery READMEs of
members 01, 02, 03, 04, 06 and 07: they survive in their arrival commits
(`725d2ebb6` for 01–03, `c1f56f842` for 04 and 06, `b998f70c6` for 07), as
members of the committed archives. All seven delivered PDFs, likewise
recoverable from the arrival commits. The checksum ledgers, each verified
against the fresh extraction and then retired: 04 `MANIFEST.sha256` (13/13),
05 `SHA256SUMS.txt` (19/19), 06 `SHA256SUMS.txt` (18/18) and 07 `SHA256SUMS`
(17/17). Manuscripts 01, 02 and 03 delivered no ledger. For the batch-62
additions 08–11: their manuscripts (`article.tex` for 08, 10 and 11,
`order_free_diophantine.tex` for 09), delivery READMEs and PDFs survive in
the arrival commit `b57c0b5ff`; 08's and 09's checksum ledgers
(`SHA256SUMS`, 11/11 and 12/12) were verified and retired at placement;
10 and 11 delivered no ledger. For the batch-63 addition 12: its
`article.tex`, delivery `README.md` and 26-page `article.pdf` survive in the
arrival commit `a4268e78e`; its checksum ledger `SHA256SUMS` (12/12) was
verified and retired at placement (`62f1ad07c`) and verified again for this
write against a fresh extraction. For the batch-78 additions 13–15:
their manuscripts (`article.tex`), delivery READMEs and PDFs (28, 23 and 25
pages) survive in the arrival commit `1977e6ea6`, as members of the
committed archives `Exact_Wiring_Diophantine_Report.zip`,
`Topology_Is_Not_Free_Interaction_Nets.zip` and `no_ghost_wires.zip`
(`git show 1977e6ea6:docs/incoming/<archive>.zip`). 14's `SHA256SUMS.json`
(16/16) and 15's `SHA256SUMS.txt` (14/14) were verified and retired at
placement (`aa11f3fef`); 13 delivered no ledger (its
`results/verification.json` records the hashes of its programs). Three
console copies were not shipped: 14's `data/export_audit_console.txt` and
`data/verification_console.txt`, byte-identical to `export_audit.json` and
`verification.json`, and 15's `data/verification.txt`, which is its
`verification.json` with a two-line header. No file of 13–15 reaches 1 MB,
so nothing was excluded as a heavy regenerable artifact.

## What is claimed and what is not

The report claims the theorems of the fifteen manuscripts, with the proofs
printed in the article: bijections between the natural zeros of explicit
integer polynomials and bounded executions, trace classes or logs of the
substrates listed above, with one witness per execution or class, exact
variable, residual and degree counts, and the lower bounds and equivalences
stated there. For Parts X–XIII this means: 08's memory compiler, birth-order
normalization, heap and graph bijections, two-stack universality and safety
obstruction; 09's classification `D⁺₂ = D⁺₃ = SL`, `D⁺₄ = CE` for
polynomials nonnegative on the whole real orthant, single-fold quadratics
for semilinear sets and the order-free assembly compilers; 10's capacity
formula, sharp `2H+1` pumping bound, uniform single-fold quartic, periodic
tail criterion, c.e.-completeness of eventual periodicity and affine macro
certificates; 11's one-fallback compiler, exact reservoir threshold,
priority-erasure and finite-rate obstructions, trace and minimum-fuel
quartics and the canonical-fuel equivalence with the finite-fold problem.
For Part XIV: 12's exact odometer criterion with canonical heights, the
run-length and grammar quartics with their exact witness and residual
counts, the both-outcome certificates and the `UP ∩ coUP` membership, the
Presburger and transport statements, the circuit counting barrier, the
universal one-router theorem and the rank-function bottleneck equivalence.
For Part XV: 13's sharp loop-parity theorem and its consequences, its
splice and gluing theorems and its memory certificate with initial and
final arrays; 14's locality lemma, kernel formulas, ten-state minimality,
23-residual kernel, `17L−4` memory certificate, 36-access machine, the
bounded six-rule quartic family with one witness per legal schedule (with
13's second presentation), the bounded loader and the transfer theorem;
15's suppression identity, support bound, path–cycle dictionary, contextual
completeness, canonical orbit certificate, single-fold gluing certificate,
scheduled compiler with its exact ledger, disjunction and lasso. It
does not claim the following. Each item is stated by at least the
manuscripts named; the article keeps every one of them.

- **No priority.** No manuscript establishes historical or literature-wide
  priority for its constructions (01's status paragraph and
  `RESEARCH_STATUS.md`; 02's relation to prior work and `sources.md`; 03's
  status table and `SOURCE_PROVENANCE.md`; 04's status and
  `SOURCE_AUDIT.md`; 05's status box; 06's title page and
  `repository_context.md`; 07's abstract, relation to earlier work and
  `provenance.md`; 08's status box and `PROVENANCE.md`; 09's title page and
  relation to prior work; 10's status paragraph, claims ledger and
  `provenance.md`; 11's contribution and provenance subsections; 12's
  abstract, limitation ledger and `SOURCES.md`, which say that the
  last-exit mechanism, run-length switching orders and the ARRIVAL
  uniqueness results are prior work). Their literature searches were targeted, and a search
  that finds nothing is not evidence of novelty (03, 07). The classical
  ingredients (MRDP, machine arithmetization, sums of squares, circuit
  quadratization, Cartier–Foata and forbidden-factor normal forms, sorting
  networks and sorted-memory verification, radix encodings, finite-table
  interpolation, polynomial centralizers, pairing) are not claimed.
  Batch 78: 13 does not certify priority for its sharp 2/5–2/3 theorem
  (abstract, Section 1 and `SOURCES.md`); 14 does not assert independent
  priority for each elementary lemma (Section 1 and `source_audit.json`);
  15 has not established priority for its orbit certificate (status box,
  `CLAIMS.md`, `PROVENANCE.md`). Interaction combinators, their
  universality and the numbered rules are Lafont's; permutation gluing with
  closed components is de Falco's and the Brauer-category setting's; the
  four-δ witness pair is the repository note's. The carry-free product
  lemma of 13 and 14 is Part V's (`cdc:mem:lem:fingerprint`), and 14's
  ten-pattern loop formula was also derived independently in the research
  note `interaction_combinator_quadratic_topology.md`; priority is claimed
  for neither.
- **Not formal.** No new Lean, Rocq or Coq proof was written or compiled,
  the repository's Lean build and axiom audits were not rerun, and
  repository documentation is not treated as a kernel audit (all fifteen).
  The formalization sections of 08, 09, 10, 11 and 12 are likewise
  proposals; 12's five-layer Lean plan names no module as existing, and
  "none of these new layers has been kernel-checked".
  07's `lean_integration.md` and the formalization sections of 01, 03, 04
  and 05 are proposals; 03's module names are "proposals, not files claimed
  to exist". The Python programs are finite exact checks: they do not prove
  soundness for all inputs, completeness for arbitrary horizons, global
  uniqueness or optimality of the arity bounds (the validation sections of
  01, 02, 04 and 07, and 06's "Limitations").
- **The universal problem is reduced, not solved.** No manuscript resolves
  the general single-fold or finite-fold Diophantine representation
  problem, and none gives a fixed-arity single-fold or finite-fold
  representation of unbounded (universal) halting. Part IX proves that a
  fixed-arity single-fold (finite-fold) universal halting polynomial exists
  if and only if every c.e. set has a single-fold (finite-fold)
  representation: a reduction to the open problem, not a solution of it.
  01, 03, 04, 05 and 06 each prove a form of this equivalence (06 for its
  separated one-counter schedules of depth four), printed once; 07 states
  the distinction without proving the equivalence, and 02 separates its
  restricted theorem from a universal first-halting extension. 11 proves a
  one-parameter refinement (the least-reservoir relation of one fixed
  network), again a reduction to the open problem; none of 08–11 claims a
  single-fold or finite-fold MRDP theorem. 12 proves a rank-function form
  (the graph of one monotone Boolean function computable in polynomial
  time), "an equivalence, not a solution"; it supplies no coefficients of a
  global rank polynomial and no new constructive proof of MRDP.
  13, 14 and 15 each state that MRDP applied to the unbounded reachability
  relation is classical and does not preserve their unique witnesses,
  degree or size ledgers, and that they resolve neither the single-fold nor
  the finite-fold problem (13's "no illicit single-fold conclusion", 14's
  Section 10, 15's Section 8.2 and `CLAIMS.md`).
- **Families, not fixed arity.** Every construction is a family indexed by
  a horizon, height, log length or schedule, whose number of variables grows
  with that parameter: 01's causal height `H` is a compiler parameter
  ("a family of ordinary polynomials, not one fixed-arity polynomial"), and
  representing the union over all `H` by MRDP preserves none of the root
  bijections; 03's single-fold statement is for each fixed log length; 05 is
  "a bounded-horizon theorem package"; 04's counts do not compete with
  universal polynomial pairs or with the project's optimized straight-line
  certificates; 07's horizon `T` is a construction parameter, and its
  witness bound supplies no computable bound on an unknown halting time,
  nor is an `O(T)` circuit small in `log T`; 08's heap certificates grow
  with the number of macrosteps, 09's assembly compiler with the candidate
  domain, 10's quartic with the word length, and 11's certificates with the
  horizon or the resource cutoff (its `Q_L` has `O((L+1)^8)` variables).
  12's quartics have fixed arity for one routing topology, uniform in its
  loads and run lengths, but they are a family indexed by the topology and
  grow with its description ("dimensions depending on the network
  description"); its `Q_{a,b}` for the universal clock is indexed by
  external bit budgets. No
  construction improves the project's 75-operation universal certificate,
  which counts arithmetic operations, not witnesses (01's
  `RESEARCH_STATUS.md`; 04's integration section; 09 and 10 say so
  explicitly; 11's 61 species and 62 reactions count a network, not
  operations; 12 improves no universal variable–degree record).
  13–15's polynomials are families indexed by the horizon `T` and the input
  dimensions (15's by the whole lifetime schedule); a fixed horizon is not
  fixed arity, and none supplies an ordinary-integer universal loader. 13
  says that it lowers neither the 75- nor the 87-operation figure; 14's
  ledger and 15's counts decline that comparison.
- **13, scope.** The sharp theorem concerns bare labelled matchings and
  all closing matchings: summaries for a restricted family of contexts, or
  overapproximating reachability analyses, are not ruled out. The state-bit
  bound is an information bound, not a lower bound on Diophantine
  variables, and says nothing of the bit optimality of the large-height
  certificate. The tomography theorem is existence and sampling, with no
  efficient decoder. The compiler is a paper construction; only the memory
  component is exported. Uniqueness is over a fixed schedule, not of the
  schedule. The memory certificate pays `O(L² log U)`-bit witnesses; it is
  not a cryptographic improvement on fingerprinting. The two rule evaluators
  share one rule table, so their agreement tests gluing, not the table; the
  bounds to weight 30 are computed with the recurrence. Its formalization
  path is a proposal; the MRDP interface was read, not rebuilt.
- **14, scope.** The ten-state result is for one observation interface
  (external positions and both annihilation loop counts), not a global
  graph-memory bound. The memory caps `A, V` are external; the `17L−4` count
  "must not be advertised as an unconditional improvement" of earlier
  ledgers. The unknown-schedule assembler is specified and proved but not
  implemented, and its constants `G, H` are not measured. The bijection is
  with scheduled executions, not normal forms, interleaving classes or
  observational classes. The loader is for fixed dimensions, not a universal
  loader. The transfer theorem is uniform for a fixed rule table, not for
  rules given as data. Witnesses are bounded in bit length, not small; no
  least degree is claimed; natural witnesses are essential.
- **15, scope.** The schedule is structural; its exporter is dense
  (`O(T(C₀+T+F)²)` witnesses and residuals), and the support bound is not a
  constant-cost memory lookup. The finite disjunction may be exponential
  and, like the multiaffine variant and a general lasso wrapper, is proved
  but not implemented. The lasso is a sufficient condition for
  nontermination only. No fixed-arity universal equation, paid loader,
  sparse near-linear exporter, canonical quotient of concurrent schedules,
  minimal witness count or optimal circuit. Bounded uniqueness checks and
  single-coordinate mutations are not the uniqueness proof; algorithmic
  independence within one implementation is not external review.
- **Real relaxation is not integral.** 05's quadratic has a real zero set
  that is a bounded rational polytope, but that polytope need not be
  integral: its example of a nonempty polytope with no lattice point shows
  that linear programming can find a fractional point and decide nothing
  about a genuine execution. Convexity is not an algorithm for the natural
  zeros.
- **01, scope.** The causal-history polynomial has one root per genuine
  trace: it removes duplicate interleavings, not distinct histories. The
  eleven witnesses of the worked accelerator are not claimed optimal.
  Complete finite enumeration at bounded height is a size statement, not a
  practical solver. There is no full SKI/Iota evaluation compiler (only a
  local head-rule component), and no efficient algorithm for arbitrary
  Diophantine equations. Independence means equality of partial sequential
  maps, not simultaneous token reservation.
- **02, scope.** The certificates do not decide global termination: a
  uniform procedure for "every initial state terminates" would decide a
  Hilbert's-tenth solvability problem. The construction does not introduce
  polynomial loop acceleration, closed forms or input-dependent termination
  bounds (Hark–Frohn–Giesl, Lommen–Meyer–Giesl), and its canonical
  arithmetic gadgets are not claimed new (Cantone–Cuzziol–Omodeo). The
  implementation counts (849 witnesses, 1,218 residuals for the degree-two
  example) are deliberately unoptimized, not minimal or universal-record
  claims. The code implements the sign-certificate core only, not automatic
  source recognition, the Boolean program front end or the fixed-period
  affine front end. The JSON checker certifies an assignment, not compiler
  correctness or uniqueness. A universal first-halting extension or a
  single-fold polynomial graph of `2^n` would cross a different boundary.
- **03, scope.** The comparison-network lower bound is optimal only within
  the sorting-network architecture; it is not a lower bound for arbitrary
  Diophantine encodings, and it does not show that Batcher's extra
  logarithmic factor is necessary. Source determinism removes multiple
  bounded executions but says nothing about the fibres of a fixed-variable
  arithmetization of arbitrary run length. Complete RAM, combinator,
  cellular and probabilistic front ends are not implemented. Full
  abstraction of the repository's lambda-to-combinator translations is not
  established. The linear backend's scalar size is linear, not its bit cost.
- **04, scope.** A Petri candidate firing word may be valid but
  noncanonical; its constructed assignment then has nonzero energy, as
  intended. SKI schedules are external rule/path lists: there is no
  linear-size compiler for existentially chosen unbounded paths. No
  general Diophantine solver, no new universal-variable records, and no
  full abstraction of the repository compiler chains.
- **05, scope.** The cellular-automaton and bounded-rewriting front ends are
  described and justified mathematically, not supplied as standalone
  translators. The repository was inspected, not rebuilt, and no result
  relies on an unverified numerical optimization in it.
- **06, scope.** Its universality is universality of **existential schedule
  parameterization** (globally shared parameters at depth two), not
  undecidability of ordinary unrestricted one-counter or Petri-net
  reachability. Single-foldness holds with all repetition parameters fixed.
  The canonicality filter tests whether the given expansion is canonical;
  it is not a normalizer and does not preserve existential reachability for
  every restricted schedule language. The trace-class bijection at fixed
  length has no polynomial-export front end in the prototype. Resource counts
  do not encode FIFO order. The prototype uses syntax trees, not DAG
  sharing, expands separated-scheme coefficients in unary, and its witness
  counts are not minimal. No cubic Diophantine classification is claimed.
- **07, scope.** The verifier checks that a supplied witness is a zero of
  the exported polynomial; it does not certify semantic correctness or
  uniqueness of an untrusted compiler output. Its DAG degree bound is
  conservative: the stream example reports 6, while the simplified
  polynomial has degree 4. The fixed-read FIFO-network theorem is proved,
  but the network-table compiler is not implemented; the shipped compilers
  cover cyclic-tag and one-queue deletion-tag systems. No universal
  optimality is claimed (a compiler that simulates the run could output the
  constant 0 or 1), the guard variable is not logically unavoidable, and
  the witness-height bound is an upper bound. The word-memory lower bound
  concerns faithful natural-number word codes with fixed polynomial
  insertion maps: it excludes neither conditional, floor, division or
  prime-exponent operations, nor finite sets of lengths, hidden control
  state, or continuous and rational encodings; switched affine dynamics do
  not make one everywhere-polynomial scalar map universal. No lower bound on
  the number of variables of arbitrary Diophantine representations is
  asserted, and no direct `T+1`-variable polynomial for an arbitrary `T`-step
  Rule 110 space-time diagram. Its research questions are not claimed to be
  established open problems, except the finite-fold one.
- **08, scope.** Only the memory layer and a pointer-log demonstration are
  implemented; the complete source-language (local heap and graph) compiler
  is a mathematical construction, not a delivered implementation, and there
  is no interaction-combinator front end (Part XV, from manuscripts 13–15,
  now supplies one for bounded scheduled histories) or checked reduction
  from the repository's Iota or lambda semantics. The two-stack module is a logging
  demonstration, not a Turing-machine front end. The linearithmic bound is
  a corollary of published sorting theory (Goodrich; Part V uses AKS), not
  a benchmark, and the comparator lower bound holds only within the
  explicit-sorting architecture. The quotient removes fresh names only, not
  schedules, occurrences or unordered births; equations are over `ℕ`, and
  neither integer nor real domains preserve the bijection.
- **09, scope.** The cubic theorem holds only under nonnegativity on the
  whole real orthant, jointly in inputs and witnesses; it says nothing about
  natural solvability of arbitrary cubics, cubics that change sign on the
  orthant, positivity only on natural points or only after fixing the input.
  The single-fold semilinear quadratics and the assembly compiler do not
  give single-fold or finite-fold MRDP; the quartic normalization is
  unique only relative to an existing MRDP witness. The tile model has no
  negative glues and no detachment (a signed-glue counterexample shows why),
  the executable fixtures use singleton seeds, and witnesses are labelled
  assemblies, not shapes. The effective decomposition uses real-algebraic
  sampling with no complexity bound, which the prototype does not implement.
- **10, scope.** No universality, universal single-fold MRDP or improved
  operation record; FRACTRAN universality and Diophantineness are not new,
  and fixed-loop acceleration and arithmetic quarticization are not claimed
  new in general. The polynomial is uniform only for a fixed word schema;
  counts made existential may lose uniqueness. The infinite-tail criterion
  is proved but its polynomial exporter is not implemented. The interface is
  exponent vectors, not raw integers. The 114,875 checks are counted finite
  checks, not proofs.
- **11, scope.** Closed finite-reservoir instances are finite-state; the
  universality is only existential in the reservoir (or in the open,
  non-conserving variant). Priority is an ideal execution rule; the
  finite-rate obstruction concerns the stated stochastic model only. The
  finite-fold problem is not resolved, no record-small universality is
  claimed (61 and 62 are construction bounds), and the canonical-witness
  mechanism is a general normal-form principle, not a replacement for MRDP.
  The discrepancy it reports in the Alhazov–Verlan source table is the
  author's reading, not re-inspected here (the table's own structure
  corroborates it).
- **12, scope.** The least-action and last-exit mechanism is classical
  (Friedrich–Levine; Bond–Levine; ARRIVAL; reachability switching games),
  and run-length compression and last exits are "not new here". `SF` and
  `FF` are not proved: the bottleneck theorem is "an equivalence, not a
  solution", and its quantitative part is conditional on a local rank-graph
  representation. No polynomial-time algorithm finds the unique routing
  certificate; the height bound bounds certificate length, not execution
  time. The both-outcome theorem "is not asserted as a new upper bound for
  ordinary ARRIVAL". Natural witnesses are essential: replacing them by
  sums of four integer squares keeps existence and destroys uniqueness, and
  no single-fold claim is made over integer witnesses. The one-router
  system is algorithmic (an unbounded counter and bounded simulation), not a
  finite-state rotor; Cairns's sandpile universality is not transferred to
  finite periodic rotors; being eventually periodic is not having an
  effective periodic description. The unique clock certificate does not put
  universal halting in `UP` (its length has no computable input-only
  bound), and the bounded-budget quartics `Q_{a,b}` are not one
  fixed-arity equation. The grammar component of the code checks local
  prefix paths; there is no global symbolic grammar compiler. The
  universal-clock tests use toy countdown and looping systems; no universal
  Turing machine is encoded or verified. The monomial counts 50 and 81 are
  illustrative, not minimal. The bibliography is not a complete priority
  search, and nothing is Lean-checked.

## Relation to the formal project

The report continues the Lean project `Computability/HilbertTenthProblem`.
It uses the project's existence interfaces `Diophantine.boundedForall_dioph`,
`Diophantine.exactIter_dioph` and `Diophantine.existsExactIter_dioph`
(`Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`)
and MRDP (`Diophantine.mrdp`, `Diophantine.mrdp_iff` in
`Lean/Diophantine/MRDP.lean`; this and the Lean paths below are relative to
`Computability/HilbertTenthProblem`) only as context: they assert that
representations exist and say nothing about how many witnesses a
representation has. The project formalizes the single-fold exponential
representation of Jones and Matiyasevich: `JM1984.RM.re_sfu` and
`JM1984.RM.re_single_equation` (`Lean/Diophantine/Paper1984/DPR.lean`), with
the predicate `JM1984.Exp.SFU` (`Lean/Diophantine/Paper1984/ExpDioph.lean`)
and the uniqueness lemma `JM1984.RM.sysQ_unique`
(`Lean/Diophantine/Paper1984/ExpSys.lean`); this report cites that
representation as a classical input. None of the report's own theorems is
formalized in Lean or Rocq, and the Python programs are finite checks, not
proofs. Placing the report beside a Lean development confers no formal
status on it.

Part VI also borders the project's tag-system route: the Lean certificate
for Jones's 1980 Theorem 5 stores intermediate queues as content and length
marker (`Jones1980.length_step'`, `Jones1980.content_step'` in
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/TagHistory.lean`),
and the project's notes
`Papers/1980/EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md` and
`EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md` treat causal prefixes and global
stream identities for operation-counted certificates. Part VI's theorems are
not formalized.

The manuscripts inspected the project at their pins; no file under
`Computability/HilbertTenthProblem` has changed between `e8bb0931d` and the
write, so their descriptions of it are current. 01, 03 and 04 also read
`Computability/CombinatoryLogic/README.md`, and 04 read
`Computability/CombinatoryLogic/Coq/SKPolynomial.v`, whose "polynomials" are
applicative SK terms, not Diophantine polynomials.

Parts X–XIII (manuscripts 08–11) rely on no formal declaration either. They
cite, as context only, `Diophantine.mrdp`, `Diophantine.mrdp_iff` and
`Diophantine.mrdp_dioph_iff` (`Lean/Diophantine/MRDP.lean`; 09), the three
trace declarations above (08, 11), and the MRDP guide `Lean/MRDP.md` with
its primitive-recursive route (11). Manuscript 09 names
`PresburgerArithmetic.Formula.presburgerArithmetic_decidable`, a definition
in `Logic/PresburgerArithmetic/Lean/PresburgerArithmetic/Decision.lean`
(Cooper elimination over the integers, deciding sentences); the
formula-level elimination over `ℕ` that its single-fold semilinear
quadratics would compose with is a formalization obligation, not an
existing interface. Manuscript 10 names the vendored Rocq file
`lib/Coq-Library-Undecidability/theories/H10/Fractran/fractran_dio.v`
(`dio_rel_fractran_step`, line 33; `FRACTRAN_HALTING_dio_single`, line 168,
a single equation, not a single-fold one) as a bridge target. None of these
declarations proves any theorem of Parts X–XIII. Nearby project notes are
consistent with them: `Papers/1982/jones1982_corrected.tex` (line 87:
universal equations of degree four, none of degree two, without a positivity
hypothesis) with 09's threshold, which concerns orthant-nonnegative
polynomials only; `Papers/1980/FRACTRAN_VARIANTS.md` (lines 1 and 79, the
obstacle of FRACTRAN priority) with 10; and Korec's machines in
`Papers/1980/ALTERNATIVE_UNIVERSAL_MACHINERY.md` (lines 736–740) with 11's
universal source machine. None of 08–11 states or improves an operation
count.

Part XIV (manuscript 12) relies on no formal declaration either. It cites,
as context only, `Diophantine.mrdp` (`Lean/Diophantine/MRDP.lean`, line 33)
and the MRDP guide `Lean/MRDP.md` (natural-witness interface, input zero
allowed, no degree or witness bound and no practical generator), and, as
integration points of its Lean plan, `MRDP.boundedForall_dioph` and
`MRDP.primrec_diophFn` (`Lean/Diophantine/Common/MRDPCore.lean`, lines 215
and 336; the guide's lines 44–45) and the older trace interfaces of
`DiophantineTrace.lean`. Its statement that the project's MRDP interface
does not claim unique witnesses is true of `Diophantine.mrdp`; the article
adds that the project does formalize the single-fold *exponential*
representation (`JM1984.RM.re_sfu`, `Lean/Diophantine/Paper1984/DPR.lean`,
line 309, with `JM1984.Exp.SFU`), the formal neighbour of Part XIV's
bottleneck theorem. Nothing of Part XIV is formalized: the project has no
rotor-routing, chip-firing, ARRIVAL or `UP ∩ coUP` material, and 12 states
or improves no operation count.

The other reports of this category are
[probabilistic-quantum-and-continuous-computation](../probabilistic-quantum-and-continuous-computation/)
(`pqc:`), which treats the Diophantine representability of probabilistic,
quantum and continuous computation and shares no theorem with this one
(Parts X and XIII point to its question on continuous-time and robust
physical semantics), and
[liveness-beyond-halting](../liveness-beyond-halting/) (`lbh:`), opened in
batch 62 for recurrence and liveness beyond halting: Part X's perpetual
safety obstruction and Part XII's eventual-periodicity results are the
lowest levels of its hierarchy, and the article says so where they are
printed.

**Relations (batch 63).** *liveness-beyond-halting* has since been written
(`2a34b1740`) from batch-62 manuscripts 10 (base) and 03 and batch-63
manuscript 01 (its sources 10, 03 and 11). It quotes this report's
zero-guard remark in Part VIII ("the uniform-parameter presentation is then
quartic unless another representation is supplied") and supplies that
representation: the degree-two transition laws of its sources 03 and 11
(`lbh:qd:thm:compiler`, `lbh:ql:thm:compiler`, compared in its section
`lbh:sec:threecompilers`). Its hierarchy table (`lbh:sec:onetable`) cites
Parts X and XII as the Π⁰₁ and Σ⁰₁ levels for heap and priority programs.
Dated batch-63 notes in the article record this at the zero-guard remark
(Part VIII), after Part IV's specified-input nontermination certificates,
after Part X's safety theorem and before Part XII's section on
nonperiodic words. Part XIV shares only the word "clock" with that report
(the universal clock is not its Clock predicate), and termination of a
finite periodic routing network is decidable, below its hierarchy.
Manuscript 12 bears on no question of
*probabilistic-quantum-and-continuous-computation*.

Part XV (manuscripts 13–15) relies on no formal declaration either. 13 and
15 cite, as context only, `Diophantine.mrdp` and `Diophantine.mrdp_iff`
(`Lean/Diophantine/MRDP.lean`, lines 33 and 42), which assert existence of a
Diophantine representation and say nothing about its witnesses. No theorem
of Part XV is formalized in Lean or Rocq, none of the three ships Lean or
Rocq files, and their formalization sections are proposals. Placing these
manuscripts beside the formal project confers no formal status on them.
They answer the research note
`Papers/research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.md`
of the Hilbert's-tenth-problem tree, which is maintained separately and was
not edited. Two later notes of that tree bear on Part XV and are cited by
dated notes in the article: `interaction_combinator_quadratic_topology.md`
(`b7a9404d4`) derives 14's ten-pattern δδ loop formula independently, with
a 472-operation charge for one complete selected δδ step, and
`incoming_substrate_review_1977e6ea6.md` (`44b28c395`) reviews and replays
the three archives, finds no mathematical error, notes that 13's
`Circuit.failures` ignores unused trailing coordinates, and derives three
natural-domain reductions of the shipped systems: 15's orbit rows 169 → 147
in the example (same 126 witnesses), 14's loop kernel 23 → 15 residuals
and 17 → 15 helpers, and 13's memory example 144 → 134 residuals. They are
recorded, not applied: the shipped exports are unchanged.

**Relations (batch 78).** Part XV answers, for bounded scheduled histories,
Part X's question on a complete interaction-combinator frontend
(`cdc:nh:q:frontend`), answers Part V's question on the best scalar
constant (`cdc:q:scalar`) in part for capped relations, bears on the
question on faithful graph-rewriting front ends (`cdc:q:graphfront`), and
re-derives Part V's product lemma; dated notes at those places and after
Part V's linear-memory theorem, in Part X's subsection on interaction
systems and at its question on quotienting independent schedules say how
far. The commutation quotient of independent schedules stays open. In
*liveness-beyond-halting*, the question on clock-faithful translations to
interaction nets ("Other unconventional substrates with timing
certificates") is not answered: Part XV supplies a local polynomial compiler
for the target's own finite steps, not the clock-faithful simulation
theorem. That report was not edited in this write.

## Build

pdfLaTeX, with the packages loaded in `article.tex` (base 05's preamble
plus `float`, and since batch 62 `fancyvrb`, `tikz` and `etoolbox`:
fontenc, inputenc, amsmath, amsthm, mathtools, newtxtext, newtxmath,
geometry, microtype, booktabs, array, longtable, tabularx, float, xcolor,
enumitem, listings, fancyhdr, titlesec, tcolorbox, xurl, hyperref, aliascnt,
cleveref, fancyvrb, tikz and etoolbox; `etoolbox` only widens the section
numbers in the contents, which reach three digits). The two diagrams (Parts XI and XIII) are drawn in TikZ in the
source. The bibliography is internal; no BibTeX, external figures or
downloads are needed. Build in a scratch copy, so that no auxiliary file
lands in the collection:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build has 419 pages (196 before batch 62, 306 before batch 63,
338 before batch 78),
with no errors, warnings, undefined references or citations, multiply
defined labels, duplicate destinations or overfull boxes; the one underfull
line (in manuscript 01's introduction, Section 3.2) is the same as in the batch-62 build. Batch 63 adds
five macros for manuscript 12 (`\rankf`, `\UP`, `\coUP`, `\NP`, `\coNP`) and
no package. Batch 78 adds five macros for manuscripts 13–15 (`\M`, `\PP`,
`\multiset`, `\cyc`, `\id`) and no package; the batch-78 build has no
error, warning or overfull box, and its one underfull line is the one
above.

## Rerunning the checks

Every suite needs Python 3.10 or later and the standard library only. Every
suite rewrites its recorded outputs at fixed paths relative to its own
location, and most scripts import their siblings by delivered name, so run
them **on a copy with the delivered layout**, never in the report
directory. The recipes below build such copies, `r01` … `r15`, beside
`code/` and `data/`: run them in a scratch copy of the report directory
(copying `code/` and `data/` is enough), not in the collection. Where the
Windows `python` alias does not resolve, use `py`.

```sh
# 01: rewrites r01/examples/*.json and r01/data/{verification.json,verification.txt,export_verification.json}
mkdir -p r01/code
for f in causal_diophantine demo verify verify_exports; do cp code/01-causal-traces-$f.py r01/code/$f.py; done
(cd r01 && python code/demo.py && python code/verify.py && python code/verify_exports.py)

# 02: writes four JSON files into r02, then the independent check
mkdir -p r02
for f in certificates quartic_compiler run_tests verify_export; do cp code/02-poly-trajectories-$f.py r02/$f.py; done
(cd r02 && python run_tests.py && python verify_export.py quartic_example.json > independent_verification.json)

# 03: rewrites r03/artifacts/{example,linear_example}/ and the two test records
mkdir -p r03/code r03/artifacts
for f in canonical_memory linear_memory test_certificates test_linear_memory; do cp code/03-linear-memory-$f.py r03/code/$f.py; done
(cd r03 && python code/test_certificates.py > artifacts/test_run.txt && python code/test_linear_memory.py > artifacts/linear_test_run.txt)

# 04: rewrites r04/examples/*.json and r04/tests/results.json
mkdir -p r04/code r04/tests
for f in diophantine_compiler verify_certificate; do cp code/04-witness-faithful-$f.py r04/code/$f.py; done
cp code/04-witness-faithful-run_tests.py r04/tests/run_tests.py
(cd r04 && python tests/run_tests.py && python code/verify_certificate.py examples/fractran_first_halt.json examples/petri_fork_join.json examples/ski_SKII.json examples/ski_context.json > tests/certificate_verification.jsonl)

# 05: rewrites r05/results/ (run without -O: the assertions are the checks)
mkdir -p r05/code r05/results
for f in trace_polytope verify demo; do cp code/05-trace-polytopes-$f.py r05/code/$f.py; done
(cd r05 && python -B code/verify.py > results/verification_stdout.txt && python -B code/demo.py > results/demo_stdout.txt)

# 06: rewrites r06/verification/{test_results,substrate_results}.json
mkdir -p r06/code r06/verification r06/examples
for f in compiler substrates test_compiler verify_export; do cp code/06-counter-schedules-$f.py r06/code/$f.py; done
for f in multiplication_certificate multiplication_witness canonical_multiplication_certificate canonical_huge_witness; do cp data/06-counter-schedules-$f.json r06/examples/$f.json; done
(cd r06 && python code/test_compiler.py && python code/substrates.py \
  && python code/verify_export.py examples/multiplication_certificate.json examples/multiplication_witness.json > verification/export_resource_check.json \
  && python code/verify_export.py examples/canonical_multiplication_certificate.json examples/canonical_huge_witness.json > verification/export_canonical_check.json)

# 07: rewrites five r07/examples/*.json and r07/tests/results.json
mkdir -p r07/code r07/tests r07/examples
for f in queue_certificates compile_tag verify_certificate; do cp code/07-queue-causality-$f.py r07/code/$f.py; done
cp code/07-queue-causality-run_tests.py r07/tests/run_tests.py
cp data/07-queue-causality-ternary_tag_spec.json r07/examples/ternary_tag_spec.json
(cd r07 && python tests/run_tests.py && for e in stream quartic zero_slack ternary_tag; do python code/verify_certificate.py examples/${e}_example.json; done)

# 08: rewrites r08/tests/receipt.json and r08/examples/{memory_events,memory_certificate}.json
mkdir -p r08/code r08/tests r08/examples
cp code/08-dynamic-heaps-memory_quartic.py r08/code/memory_quartic.py
cp code/08-dynamic-heaps-pointer_machine.py r08/code/pointer_machine.py
cp code/08-dynamic-heaps-run_tests.py r08/tests/run_tests.py
cp data/08-dynamic-heaps-memory_events.json r08/examples/memory_events.json
(cd r08 && py tests/run_tests.py)

# 09: rewrites the four certificates and verification_report.json in r09/data
mkdir -p r09/code r09/data
for f in assembly_compiler presburger_gadgets verify; do cp code/09-order-free-$f.py r09/code/$f.py; done
(cd r09 && py code/verify.py)

# 10: rewrites r10/results/ (run without -O: the assertions are the checks)
mkdir -p r10/code r10/results
for f in priority_certificates test_priority_certificates generate_instances verify_export; do cp code/10-priority-pumping-$f.py r10/code/$f.py; done
(cd r10 && py code/test_priority_certificates.py > results/test_output.txt \
  && py code/priority_certificates.py --export results/example_certificate.json && py code/generate_instances.py \
  && py code/verify_export.py results/example_certificate.json results/example_instance.json > results/independent_example_check.json \
  && py code/verify_export.py results/large_maximal_certificate.json results/large_maximal_instance.json > results/independent_large_check.json)

# 11: writes r11/examples/ and r11/verification/results.json
mkdir -p r11/code
for f in reaction_compiler verify; do cp code/11-reaction-fallback-$f.py r11/code/$f.py; done
(cd r11 && py code/reaction_compiler.py --output examples && py code/verify.py --output verification/results.json)

# 12: writes test_results.json, example_quartic.{json,txt} and parametric_quartic.{json,txt} into r12
mkdir -p r12
for f in verify_certificates compile_quartic; do cp code/12-rle-routing-$f.py r12/$f.py; done
(cd r12 && py verify_certificates.py --output test_results.json \
  && py compile_quartic.py --output example_quartic.json \
  && py compile_quartic.py --variable-lengths --output parametric_quartic.json)

# 13: compares with the recorded receipt and the exported certificate; writes nothing
mkdir -p r13/code r13/results
for f in wiring parity diophantine_memory verify; do cp code/13-exact-wiring-$f.py r13/code/$f.py; done
cp data/13-exact-wiring-verification.json r13/results/verification.json
cp data/13-exact-wiring-example_memory_certificate.json r13/results/example_memory_certificate.json
(cd r13 && py code/verify.py)

# 14: writes r14/data/{delta,gamma}_loop_quartic.json, memory_example_quartic.json, verification.json, export_audit.json
mkdir -p r14/code r14/data
for f in certificates nets verify verify_exports; do cp code/14-net-topology-$f.py r14/code/$f.py; done
(cd r14 && py code/verify.py > /dev/null && py code/verify_exports.py)

# 15: writes r15/data/{endpoints,quartic_A_schedule,witness_A,verification}.json and verification.txt
mkdir -p r15/code r15/data
for f in loop_exact verify check_export; do cp code/15-no-ghost-wires-$f.py r15/code/$f.py; done
(cd r15 && py code/verify.py > /dev/null && py code/check_export.py)
```

The recipes for 08–12 use `py`, which resolves on this machine; the
delivered texts write `python` (12's Makefile `python3`).

The shell redirections reproduce the recorded console files
(`*_run.txt`, `verification_stdout.txt`, `demo_stdout.txt`,
`certificate_verification.jsonl`, `independent_verification.json`, the two
`export_*_check.json`), which the scripts print but do not write. 04's
verifier prints one line per file in argument order; the recorded file lists
the examples alphabetically, as the delivered README's `examples/*.json`
expands. 07's general-tag front end can also be run on the shipped
specification:
`(cd r07 && python code/compile_tag.py --spec examples/ternary_tag_spec.json --output custom_tag.json)`
reproduces `ternary_tag_example.json`. Four recorded files have no script
that writes them: 01's and 03's `build_validation.json` and 06's
`pdf_quality.json` describe the delivered PDFs, and 06's
`determinism_check.json` records two runs of `test_compiler.py` under
`PYTHONHASHSEED` 1 and 2 compared without their elapsed times.

**Expected results.** In the merge every recipe was run as printed on a
scratch copy of the shipped `code/` and `data/` (Python 3.14.4, Windows),
and every regenerated file was compared with the shipped one after removing
carriage returns. All seven suites passed. Identical: 01's two examples and
`export_verification.json`; 02's four JSON files other than
`test_report.json`, and `independent_verification.json`; 03's six example
files; 04's four examples and `certificate_verification.jsonl`; 05's twelve
result files other than `verification.json` and `verification_stdout.txt`;
06's `substrate_results.json` and both export checks; 07's five examples and
`results.json` (`"status": "all exact checks passed"`; the four
certificates accepted with energy 0 and variables/residuals/degree bound
4/6/6, 7/9/4, 3/8/8 and 5/7/8). The other records differ only in elapsed
times and, for 01, in the Python version (3.13.5 recorded). The
`compile_tag.py` command above also reproduced `ternary_tag_example.json`.
The recipes for 08–11 were run the same way in the batch-62 write (Python
3.14.4, Windows), and all four suites passed. Identical after removing
carriage returns: 08's `memory_certificate.json` and `memory_events.json`;
09's four certificates and `verification_report.json`; 10's two
certificates, two instances and two independent checks; 11's six example
files and `results.json`. 08's `receipt.json` and 10's `verification.json`
and `test_output.txt` differ only in their elapsed time. The recipe for 12
was run the same way in the batch-63 write (Python 3.14.4, Windows; about
five seconds): `"status": "PASS"`, 123,201 odometer candidates (2,037
balanced, 535 accepted), 13,375 RLE and 35,952 grammar mutations rejected,
the `2^8192 + 2^4096`-firing certificate evaluated to zero, 205 toy clock
checks; the compiler printed 11 residuals, degree 4, 50 and 81 monomials
and 500 cross-checks each. All five regenerated files equal the shipped
ones after removing carriage returns (no elapsed time is recorded).
The recipes for 13–15 were run the same way in the batch-78 write (Python
3.14.4, Windows) and all pass. 13 prints `"status": "PASS"` (about 22
seconds) after recomputing 121,537 closures, the bounds to weight 30,
23,930 splice comparisons and the exported memory certificate and comparing
them with the recorded receipt; it writes nothing. 14's two programs (about
8 seconds) regenerate five files that equal the shipped ones after removing
carriage returns. 15's `verify.py` (about 26 seconds) regenerates four
files that equal the shipped ones after removing carriage returns, except
the `runtime_seconds` field of `verification.json` (4.019 recorded), and
`check_export.py` prints `PASS: 68 parameters, 126 witnesses, 169
residuals, energy 0`.

**Hazards.**

- On Windows the regenerated files have CRLF line endings; the shipped
  files have LF. Compare with line endings normalized.
- Batch 78: 14's and 15's `verify.py` and 14's `verify_exports.py` write
  into `data/` beside their own `code/` directory, overwriting the recorded
  files there (15 also writes `verification.txt`); 13's `verify.py --write`
  rewrites its two files in `results/`. Run them only in the `r13`–`r15`
  copies. The shipped `code/13-*`, `code/14-*` and `code/15-*` scripts that
  import a sibling (13's and 14's `verify.py`, 15's `verify.py`) fail at
  that import, because the siblings carry prefixes. The three verifiers
  record SHA-256 hashes of every `.py` file in their code directory: keep
  only the copied programs there, or 13's comparison mode fails and 14's
  and 15's records change. 15's `check_export.py` takes `--data` for the
  directory but expects the delivered file names. Do not use
  `code/13-exact-wiring-Makefile` or `code/14-net-topology-Makefile` (their
  `paper`/`pdf` targets run `pdflatex` on `article.tex`, which is now the
  merged article, and `clean` deletes its auxiliary files) or
  `code/15-no-ghost-wires-build.sh` (it changes to its own directory and
  runs `pdflatex` three times on `article.tex`, which is not there).
- Every suite overwrites its recorded outputs at paths fixed relative to the
  script (the parent of the script's directory in 01, 03, 04, 05, 06, 07,
  08, 09 and 10; the working directory in 02; the `--output` paths in 11). The shipped `code/` scripts that import
  a sibling fail at that import, because the siblings carry prefixes; an
  unprefixed copy placed in the report directory would write into
  `examples/`, `data/`, `artifacts/`, `results/`, `tests/` or
  `verification/` there. 01's `verify_exports.py` finds no `examples/` in
  the report and stops with an error.
- Do not run `code/05-trace-polytopes-build.py` here. It runs `verify.py` and
  `demo.py` from `code/` below its own directory and then `pdflatex` three
  times on `article.tex` in its own directory. As shipped it stops at once
  (`code/code/verify.py` does not exist; tested on a copy). A copy at the
  report root run with `--skip-tests` would run `pdflatex` three times on
  `article.tex`, which is now the merged article, in the report directory,
  overwriting `article.pdf` and leaving auxiliary files there. Use the
  recipe above; inside `r05`,
  `cp ../code/05-trace-polytopes-build.py build.py && python build.py --verify-only`
  runs the same two checks.
- The two Makefiles (`code/03-linear-memory-Makefile`,
  `code/07-queue-causality-Makefile`) use delivery paths and a `pdf` target
  that runs `pdflatex` on `article.tex`; do not use them here. GNU make is
  not installed on this machine in any case.
- Do not run `code/08-dynamic-heaps-build.sh` or `code/09-order-free-build.sh`.
  Each changes to its own directory and runs `pdflatex` there, 08's three
  times on `article.tex` and 09's twice on `order_free_diophantine.tex` with
  output in `.build/`. As shipped in `code/` they find no such file; a copy
  of 08's at the report root would compile the merged `article.tex` in the
  report directory, overwriting `article.pdf` and leaving auxiliary files.
- 10's tests rewrite `results/verification.json` and print the same report;
  the recorded `test_output.txt` is that printed report (the two shipped
  files are byte-identical). 10's `priority_certificates.py --export` and
  `generate_instances.py` write into `results/`, 11's programs into the
  directories named by `--output`; give them paths outside the report.
- 12's programs write where `--output` says, relative to the working
  directory (defaults `test_results.json` and, for the compiler, a JSON file
  plus a `.txt` of the same stem beside it). Run in the report directory,
  they would write unprefixed files there; the shipped
  `code/12-rle-routing-compile_quartic.py` fails at its import of
  `verify_certificates` in any case. Do not use
  `code/12-rle-routing-Makefile` here: its `test` target runs the delivered
  names with `python3`, and its `pdf` and `clean` targets run `pdflatex` on
  and delete the auxiliary files of `article.tex`, which is now the merged
  article.
- The command-line compilers write where they are told: 03's
  `canonical_memory.py` and `linear_memory.py` (an output directory), 07's
  `queue_certificates.py` and `compile_tag.py` (`--output`) and 02's
  `certificates.py` (`--output`). 02's `quartic_compiler.py` and 06's
  `compiler.py` write `quartic.json` and `multiplication_certificate.json`
  into the working directory unless given `--output` or `--export`. Give
  them paths outside the report. 03's linear backend can exceed Python's
  decimal string limit for large logs (`PYTHONINTMAXSTRDIGITS=0` lifts it, for
  trusted input only).

## Disclosures

- **Shipped text that uses delivery names or names unshipped files.**
  - `01-causal-traces-RESEARCH_STATUS.md` and `01-causal-traces-SOURCE_AUDIT.md`
    speak of "the article", "the paper" and "the new report": manuscript 01's
    delivered text, now merged. They name no paths.
  - `02-poly-trajectories-sources.md` names `article.tex` (manuscript 02's,
    not shipped).
  - `03-linear-memory-SOURCE_PROVENANCE.md` names "this archive" and
    `artifacts/` (now `data/03-linear-memory-*`).
  - `04-witness-faithful-SOURCE_AUDIT.md` speaks of "this package" and "the
    compiled article", which is not shipped.
  - `06-counter-schedules-repository_context.md` speaks of "the article",
    manuscript 06's delivered text.
  - `07-queue-causality-provenance.md` names `article.tex`, `article.pdf`,
    "this ZIP", `tests/run_tests.py` and `tests/results.json` (now
    `code/07-queue-causality-run_tests.py` and
    `data/07-queue-causality-results.json`);
    `07-queue-causality-lean_integration.md` speaks of "the package".
    07's manuscript text calls it `notes/lean_integration.md`.
  - `code/03-linear-memory-Makefile` uses `code/…`, `artifacts/…` and
    `article.tex`; `code/07-queue-causality-Makefile` uses `code/…`,
    `examples/…`, `tests/run_tests.py` and `article.tex`;
    `code/05-trace-polytopes-build.py` uses `code/verify.py`,
    `code/demo.py` and `article.tex`.
  - Every script uses delivery names in its imports and paths: 01
    (`causal_diophantine`; `examples/`, `data/`), 02 (`certificates`,
    `quartic_compiler`; the four JSON names in the working directory), 03
    (`canonical_memory`, `linear_memory`; `artifacts/…`), 04
    (`code/` on `sys.path`, `diophantine_compiler`; `examples/`,
    `tests/results.json`), 05 (`trace_polytope`; `results/`), 06
    (`compiler`; `verification/…`), 07 (`code/` on `sys.path`,
    `queue_certificates`, `verify_certificate`; `examples/…`,
    `tests/results.json`).
  - `08-dynamic-heaps-PROVENANCE.md` speaks of "the article" and "this
    archive" and names `tests/receipt.json` (now
    `data/08-dynamic-heaps-receipt.json`).
    `10-priority-pumping-VALIDATION.md` names `article.pdf` and `article.tex`
    (manuscript 10's, not shipped; its text is Part XII), `results/verification.json`
    (now `data/10-priority-pumping-verification.json`) and
    `code/verify_export.py` (now `code/10-priority-pumping-verify_export.py`);
    `10-priority-pumping-provenance.md` speaks of "this article".
  - `code/08-dynamic-heaps-build.sh` runs `pdflatex` on `article.tex` and
    `code/09-order-free-build.sh` on `order_free_diophantine.tex`; neither
    manuscript source is shipped.
  - The batch-62 scripts use delivery names in their imports and paths: 08
    (`code/` on `sys.path`, `memory_quartic`, `pointer_machine`;
    `examples/`, `tests/receipt.json`), 09 (`assembly_compiler`,
    `presburger_gadgets`; `data/`), 10 (`priority_certificates`;
    `results/`), 11 (`reaction_compiler`; `--output` paths).
  - The article prints the shipped names wherever 08–11 name their own files
    in prose, and keeps their command listings in the delivered layout with
    a note; 11's manifest appendix is printed with shipped names and a note
    that its `article.tex`, `article.pdf` and `README.md` are not shipped.
  - Batch 63: `12-rle-routing-SOURCES.md` names `article.tex` (manuscript
    12's, not shipped; its text is Part XIV and Section 3.12) and speaks of
    "this package"; `code/12-rle-routing-Makefile` names
    `verify_certificates.py`, `compile_quartic.py`, the three output files
    by their delivered names, and `article.tex`;
    `code/12-rle-routing-compile_quartic.py` imports `verify_certificates`
    by its delivered name. 12's recorded data name no files. The article
    prints the shipped names where 12 names its files in prose, keeps its
    reproduction listings in the delivered layout with a note, and notes
    that its `article.tex`, `article.pdf`, `README.md` and `SHA256SUMS` are
    not shipped. 12's delivered README (not shipped) cites its theorems by
    delivered number; the mapping is under "Delivered names and shipped
    names".
  - Recorded data that names delivery files: 03's `build_validation.json`
    (`code/test_certificates.py`, `code/test_linear_memory.py`), 01's
    `export_verification.json` and 04's `certificate_verification.jsonl`
    (bare example names). 01's and 03's `build_validation.json` and 06's
    `pdf_quality.json` describe the delivered 29-, 31- and 30-page PDFs,
    which are not shipped.
- **Batch 78: shipped text that uses delivery names or names unshipped
  files.** `13-exact-wiring-SOURCES.md` speaks of "the report" and "the
  article" (manuscript 13's delivered text, now merged) and names only
  repository paths. `15-no-ghost-wires-CLAIMS.md` cites "article equations
  (22) and (23)" (see "Delivered names and shipped names") and
  `data/verification.json` (now `data/15-no-ghost-wires-verification.json`);
  `15-no-ghost-wires-PROVENANCE.md` names `verify.py`, `check_export.py`,
  "the article", "the PDF" and "the archive", and calls `928ea9701` a
  "recursive-tree revision" (it is a commit). `code/13-exact-wiring-Makefile`
  uses `code/verify.py` and `article.tex`; `code/14-net-topology-Makefile`
  uses `code/verify.py`, `code/verify_exports.py` and `article.tex`;
  `code/15-no-ghost-wires-build.sh` runs `pdflatex` on `article.tex`; none
  of these manuscript sources is shipped. The scripts use delivery names in
  their imports and paths: 13 (`wiring`, `parity`, `diophantine_memory`;
  `results/`), 14 (`certificates`, `nets`; `data/`), 15 (`loop_exact`;
  `data/`). Recorded data name delivery files: 13's `verification.json`,
  14's `verification.json` and 15's `verification.json` key their program
  hashes by delivered names, and 14's `export_audit.json` names the bare
  data files; 13's `build_receipt.json` and 14's `pdf_quality.json`
  describe the delivered 28- and 23-page PDFs, which are not shipped and
  survive in `1977e6ea6`; 14's `source_audit.json` names this report's
  README as "prior collection". The article prints the shipped names where
  13–15 name their files in prose and keeps their listings in the delivered
  layout with notes. The review in the research tree reports one limitation
  of 13's code: `Circuit.failures` in `diophantine_memory.py` ignores unused
  trailing coordinates instead of requiring the declared tuple length; the
  polynomial on its declared coordinates is unaffected.
- **Byte-identical duplicates within a manuscript** (checked with `cmp`):
  03's `test_results.json` and `test_run.txt`, `linear_test_results.json`
  and `linear_test_run.txt`, and `example-events.json` and
  `linear_example-events.json`; 05's `verification.json` and
  `verification_stdout.txt`; 10's `verification.json` and `test_output.txt`.
  Batch 78 shipped none: 14's two console copies and 15's
  `verification.txt` were left in the arrival commit. 15's `build.sh` is
  byte-identical to the build script of another batch-78 manuscript, placed
  in another report.
  The console files are the scripts' printed JSON. No two files of
  different manuscripts are identical.
- **Machine-dependent fields.** 08's `receipt.json` and 10's
  `verification.json` (and hence `test_output.txt`) record an elapsed time,
  which a rerun changes; nothing else in the batch-62 records depends on
  the machine. In batch 78, 15's `verification.json` records a
  `runtime_seconds` field and 13's `verification.json` the Python version
  of its run (13's comparison mode ignores elapsed time).
- **Missing final newlines.** Four of 06's JSON files end without a newline
  and are kept so: `canonical_huge_witness.json`,
  `canonical_multiplication_certificate.json`,
  `multiplication_certificate.json` and `multiplication_witness.json`.
- **Same delivered names, different files.** 04 and 07 both delivered
  `tests/results.json`, `tests/run_tests.py` and `code/verify_certificate.py`;
  they are different files, told apart only by their prefixes
  (`code/04-witness-faithful-verify_certificate.py` checks lists of
  sum-of-squares residuals, `code/07-queue-causality-verify_certificate.py`
  evaluates arithmetic DAGs). Likewise 02 and 06 each have a
  `verify_export.py`, 01 and 05 a `code/verify.py`, 02 a `run_tests.py`,
  03 and 06 a `test_results.json`, and 02 and 07 a `quartic_example.json`;
  all are different programs or data. In batch 62, 09 and 11 also deliver
  `code/verify.py`, 10 a `code/verify_export.py`, 08 a `tests/run_tests.py`
  and 11 a `results.json` (as `verification/results.json`); again all are
  different files, told apart by their prefixes. In batch 63, 12 delivers a
  `test_results.json` (as do 03 and 06, under `artifacts/` and
  `verification/`) and a `verify_certificates.py`, which is not 04's or
  07's `code/verify_certificate.py`. In batch 78, 13, 14 and 15 each
  deliver a `code/verify.py`, and 14 and 15 each a `data/verification.json`;
  all are different files, told apart by their prefixes.
- **Two Cantone–Cuzziol–Omodeo papers.** 02, 04, 05 and 06 cite
  Cantone, Cuzziol and Omodeo, *On Diophantine singlefold specifications*,
  Le Matematiche 79(2) (2024), 585–620 (merged key `cco2024`). 07 cites a
  different paper by the same authors, *Six equations in search of a
  finite-fold-ness proof*, arXiv:2303.02208 (version 3, 2024; key
  `cco-six`). 01 cites a third, Cantone, Casagrande, Fabris and Omodeo,
  *Does every recursively enumerable set admit a finite-fold Diophantine
  representation?* (CEUR Workshop Proceedings 2396, 2019; key `ccfo2019`).
  03 cites none of them. The bibliography keeps all three. Batch 62 adds two
  more: Cantone, Casagrande, Fabris and Omodeo, *The quest for Diophantine
  finite-fold-ness*, Le Matematiche 76(1) (2021) (08 and 11; key
  `ccfo2021`), and Cantone, Cuzziol and Omodeo, *A Brief History of
  Singlefold Diophantine Definitions*, CEUR Workshop Proceedings 3428 (2023)
  (10; key `cco-history`); 08 also cites `cco-six` and 11 `cco2024`.
- **Pins.** 01–06 inspected `e8bb0931d` and 07 inspected `725d2ebb6`; their
  statements about the repository are those of their pins. 06's
  `repository_context.md` says that its document reads were made on the
  main branch during the inspection that returned that tree, not from a
  checkout of the pinned tree; 01's `SOURCE_AUDIT.md` says a search index
  also returned an older revision, which it did not use. 08–11 inspected
  `4e128356d`; 11 adds that a later read of the live branch returned
  `ccfb084ad`, which the article recasts as a pin statement, and cites
  ProveIt's MRDP guide by an unpinned link to the `main` branch, which the
  bibliography pins at `4e128356d` (the guide is unchanged between these
  commits). 12 inspected `e18718e83` and cites its README and MRDP guide by
  pinned links; its bibliography key `repo` is not this report's `repo`
  (06's item), so its two repository items are merged into `repo-h10` and
  `repo-mrdp`, which now also record that pin.

## Merge decisions

The article's provenance appendix ("Provenance of this report") records the
same decisions.

- **Base: manuscript 05.** Of the four manuscripts that prove a
  trace-class root bijection, 05 needs the weakest hypothesis (any sound
  static commutation relation `I ⊆ I_max`, with interval guards and zero
  tests; 04 needs disjoint supports) and proves the strongest conclusion (a
  convex quadratic whose nonnegative real zero set is a rational polytope
  with exactly the natural zeros as lattice points). Its text supplies the
  preamble, the introduction (Section 1) and the first place of every shared
  result.
- **Layout.** Section 1 is 05's introduction plus an organization
  subsection; Section 2 is the conventions (the block prescribed for this
  report, a notation dictionary, reading rules, then every manuscript's own
  conventions); Section 3 prints each manuscript's title, author line,
  date, abstract, status statement and introduction; Parts I–IX follow by
  subject; then implementation and validation, formalization targets,
  research questions and conclusions, collected by manuscript; then the
  manuscripts' appendices, the provenance appendix and one bibliography.
  Every section title inside Parts I–IX carries the number of the
  manuscript it comes from, for example `[05]`.
- **Printed once.** The universal-halting equivalence, proved by 05, 01,
  03 and 04, is one theorem, `cdc:bd:thm:universal`, with items (a) every
  c.e. subset of ℕ, (a′) every c.e. relation of finite arity (01), (b) a
  fixed universal halting polynomial, (b′) of degree at most four (04), (c)
  a fixed polynomial for 05's decidable first-halting trace verifier, all
  in finite-fold and single-fold versions. The absence of a computable
  witness-height bound, proved by 02, 01, 03, 04 and 05, is one proposition,
  `cdc:bd:prop:nobound`, stated in 02's general form (any undecidable set)
  with the universal-halting form beside it. At the places where 01, 02,
  03 and 04 stated them, a `[write]` note gives each manuscript's letters
  and its own proof follows there. 06's finite-fold substrate equivalence and
  parameter-bound obstruction are different statements and are kept whole;
  07 proves neither and is credited in prose.
- **Second routes.** 04's `thm:petri` and 06's `thm:tracebijection`
  (different constructions and counts), 01's `prop:boxes` (the box
  formulas of 05's `thm:interval`) and 06's `thm:commutation` (the counter
  form of 05's `thm:commute`) keep their statements and proofs, with
  "second route" or "counter form" in their titles; 04's monitor,
  lower-bound family and counting theorem, and the Parikh refinements of
  01, 04 and 06, point in their titles to 05's versions. 01's height-bounded
  compiler `thm:history` is a different theorem and is kept whole.
- **Moved text.** 05's interval-guard theorem and guarded-program
  corollary (from its section on other substrates) open Part I and follow
  the quadratic certificate in Part II; its rewriting subsection is in
  Part VII. The substrate surveys of 01, 02 and 05 are split between Parts
  VII, VIII and IX. 02's first two introductory subsections open Part IV and
  its Section 2 is in the conventions; 07's word-code subsection opens Part
  VI and its first-failure section closes Part I. 07's word-memory section
  stays before its quartic section, as in the manuscript, because the
  quartic uses its two-coordinate memory. Every move is announced by a note
  at both ends.
- **Conclusions.** Those of 02, 03 and 07 close Parts IV, V and VI; those of
  05, 01, 04 and 06 are collected in one back-matter section.
- **Research questions.** The 74 questions (01 10, 02 10, 03 10, 04 10, 05
  12, 06 12, 07 10) are printed in 50 `question` environments: 43 single
  questions and 7 merged clusters (verified compiler interfaces, dynamic
  independence, counting, sharp degree and arity, SKI bridges, fixed-arity
  compression, restricted compression), each naming its sources and
  printing each source's text. Three notes: 05's degree-two certificate
  answers part of 01's question on sharp degree, arity and domain
  comparisons (for length-`T` classes; the height-bounded quartic and the
  integer domain stay open); Part VI answers 06's queue question for
  bounded runs of fixed-read FIFO networks (data-dependent read counts stay
  open); 05's question on ProveIt's operation-counted straight-line
  certificates stays a question.
- **Bibliography.** The 58 items of the seven bibliographies (without 07's
  two "companion" items, which were manuscripts 04 and 06) are 33 distinct
  works; each merged entry lists the manuscripts citing it and keeps every
  annotation. Two different Cantone–Cuzziol–Omodeo papers stay apart. The
  39 items of manuscripts 08–11 add 23 distinct works (56 in all): fifteen
  of their items were merged into existing entries (the repository items,
  now also pinned at `4e128356d`; Batcher; the SNARKs-for-C paper;
  Jones–Matiyasevich; Larchey-Wendling–Forster 2022; Conway; `cco2024` and
  `cco-six`), 08's and 11's citations of *The quest for Diophantine
  finite-fold-ness* became one new entry, and 09's citation of the Lean file
  `MRDP.lean` is kept apart from the MRDP guide `MRDP.md` (keys
  `repo-mrdp-lean` and `repo-mrdp`).
- **Corrections to the printed text** (delivered files untouched): 07's
  sentence citing its unpublished companions now names manuscripts 04 and
  06 of this report; 06 cited Jones–Matiyasevich for ProveIt's
  documentation and now cites the repository; 04's hard-coded "Section 2",
  "Section 3" and "Section 7" point to its sections here (three section
  labels added); where 01, 02, 03, 04, 05, 06 and 07 name their own files in
  prose, the shipped name is printed, and their command listings keep the
  delivered layout with a note; sentences in which 01, 03 and 05 describe
  their delivered packages (PDF, checksum ledger, README) carry notes on
  what is shipped.
- **Additions.** The conventions block, with one change to the prescribed
  wording: "Parts II, VI, VII and VIII" for the Parts in which `T` counts
  execution steps (the prescription listed II, VI and VIII; Part VII's
  FRACTRAN runs also have `T` steps). A notation dictionary; a reading
  paragraph (in printed manuscript text, "this article" is that
  manuscript); Part openings with source, scope, duplicates and hypotheses;
  the remark on the formalized exponential counterpart after 02's
  exponentiation boundary (`cdc:bd:rem:sfu`); the remark on the project's
  tag-system notes after 07's uncausal example (`cdc:qc:rem:tagnotes`);
  notes on 07's one-coordinate obstruction versus the pairings of 01 and 05,
  and on bounded cellular-automaton tableaux. All written text is marked
  `[write]`.
- **Batch 62 (Parts X–XIII).** The four additions were written after the
  report and each is printed as one Part in its own order, appended after
  Part IX and before the appendices, so that no existing Part, section,
  theorem, question or equation number changed. Their title pages,
  abstracts, status statements and introductions are Sections 3.8–3.11;
  their validation, formalization plans, research questions and conclusions
  close their Parts; 09's three parts are sections of Part XI, with its
  sections demoted one level. Each Part opens with its source, its relation
  to Parts I–IX, its hypotheses and a conventions section with a table of
  letters that clash with other Parts. Duplicates are printed in both places
  with a note, because the variants differ: 08's memory compiler beside 03's
  (with an exact comparison: `2L-N` fewer witnesses, `3N-3L-1` more
  residuals, one fewer when `L = N`); 09's spatial cutoff and 11's reservoir
  bound as cases of `cdc:bd:prop:nobound`; 11's canonical-fuel equivalence
  as the one-parameter refinement of `cdc:bd:thm:universal`(c). 08's
  question on certificates without explicit sorting is printed with a note
  that Part V's linear backend answers its size part (the bit-height part
  stays open, Part V's size–height question). The 39 new questions (08 12,
  09 10, 10 10, 11 7; 11's are subsection headings turned into `question`
  environments) are printed in their Parts and cross-referenced to, not
  merged with, the 50 questions of the back matter. Six of those 50 get
  dated notes on what Parts X–XIII answer (sharp degree; locality with
  polynomial bit-height; graph-rewriting front ends; substrate interfaces;
  restricted unbounded classes; finite-fold arithmetic primitives).
  Unnumbered forward pointers were added after `cdc:thm:main`'s section,
  the word-power proposition, the acceleration theorem, Part V's memory and
  RAM theorems, Part VII's FRACTRAN theorem, the universal-halting
  equivalence and the no-bound proposition, and at the end of Part IX.
  Renamed: 09's tile palette `T` is `\mathcal T`, and 08's normal form is
  `\NF_{\mathrm{birth}}`; macro clashes were resolved by new names
  (`\indset` for 09's `\ind`, 11's `\E` printed as `\cE`, the `\repo` macros
  of 09 and 10 replaced by the word ProveIt, 10's `\mathscr` kept since
  `newtxmath` provides it and `\mathcal P` is already 10's program), and
  escaped underscores inside `\code` removed. The equations of Parts X–XIII
  are numbered within sections and those of Section 3.10 within
  subsections. Corrections: 09's "Part I" and 11's "Appendix A" point to
  their sections; 11's live-branch sentence is recast as a pin statement
  and its unpinned `blob/main` link pinned in the bibliography; notes add
  the Part VII FRACTRAN certificate and the Part III/IV acceleration results
  to 10's account of prior work, and the Part V compiler to 08's. Title-page
  lines naming the AI assistant appear only in the provenance appendix.
- **Batch 63 (Part XIV).** Manuscript 12 was written after Parts I–XIII
  were placed and, like 08–11, without knowledge of the report. It is
  printed as one Part in its own order (its Sections 2–11 and both
  appendices), appended after Part XIII and before the appendices, so that
  no existing number changed; its title page, abstract and Section 1 are
  Section 3.12 (the Section 3 heading "The seven manuscripts" became "The
  twelve manuscripts"). The Part opens with its source, its relation to
  Parts I–XIII, its hypotheses and a conventions table. It duplicates no
  printed result, so nothing is merged: its bottleneck theorem is printed
  as a history-free form of `cdc:bd:thm:universal`(c), with a paragraph
  relating it to that theorem, to `cdc:rx:thm:FF` and to
  `cdc:pt:prop:exponential-boundary`, and its no-bound item (iv) as the
  routing form of `cdc:bd:prop:nobound`; its both-outcome theorem is a
  second route to the ARRIVAL bound the manuscript itself credits. Its
  eight questions (headings of unnumbered subsections) are `question`
  environments at the end of the Part, cross-referenced to
  `cdc:q:verified`, `cdc:q:degree`, `cdc:q:locality`, `cdc:q:compression`,
  `cdc:q:ffprimitives` and `cdc:q:beyond`, not merged. Four questions of
  the back matter get dated notes: `cdc:q:restricted` (answered in part,
  for routing topologies), `cdc:q:varperiods` (an analogue answered in
  part), `cdc:q:compression` and `cdc:q:ffprimitives` (re-scoped).
  Unnumbered forward pointers were added after the universal-halting
  equivalence, in the no-bound proposition's specializations and after the
  remark on the formalized exponential counterpart. Renamed: 12's Cantor
  pairing `π` is `π_C` (Part IX's `π` is `(a+b)^2+a`); its `\mathsf{SF}`
  and `\mathsf{FF}` use Part XIII's `\SF` and `\FF`. Bibliography keys
  mapped: `repo` → `repo-h10`, `mrdpguide` → `repo-mrdp` (both with 12's
  pin), and its six literature items became new entries with lower-case
  keys (62 distinct works in all). Bracketed `[write]` notes inside the
  Part: the formalized single-fold exponential representation beside 12's
  MRDP paragraph; the grammar-length bound `2^{g_v-1}` in place of the
  manuscript's looser `2^{g_v}`; that the transport identity needs
  `U_v > 0` only where `k_v > 0`; the location of the two MRDP
  declarations its Lean plan names. Where 12 names its files in prose the
  shipped names are printed. Reciprocal pointers to *liveness-beyond-halting*
  (written in the same batch) are dated notes in Parts IV, VIII, X and XII.
- **Batch 78 (Part XV).** Manuscripts 13–15 were written after Parts
  I–XIV, without knowledge of one another, as answers to the same research
  note, and answer Part X's frontend question. They share their target, the
  rule table, the gluing theorem and the bounded compiler, so they are
  merged into one Part arranged by subject, appended after Part XIV and
  before the appendices; no existing number changed. Their title pages,
  abstracts, status statements and introductions are Sections 3.13–3.15
  (the Section 3 heading became "The fifteen manuscripts"). Printed once,
  crediting every source: the rule table and witness pair (13's text, with
  14's and 15's definitions and readings beside it); the storage and loop
  bounds (13's corollary; 14's and 15's statements keep their additions);
  order-independent gluing (13's theorem, with 15's division-free matrix
  form and 14's locality lemma); the compiler theorem (14's statement and
  ledger, with 13's statement as a remark, because it is the same theorem,
  and its proof as a second presentation; likewise the transfer theorem);
  and the carry-free product lemma, which is Part V's (13's and 14's
  statements kept in their notation, their proofs replaced by a pointer).
  Kept with their own proofs: 15's contextual completeness (it adds
  sufficiency to the loop-count form of 13's injectivity); 13's and 14's
  memory theorems, variants for different relations, compared with Part
  V's in a table, where 14's `17L−4` is not presented as an improvement on
  `24L`; and 15's orbit route. The 25 questions (13 9, 14 8, 15 8) are
  `question` environments at the end of the Part, cross-referenced, not
  merged. Renamed: no symbol; 13's `\M`, `\PP`, `\multiset` and 15's
  `\cyc`, `\id` were added to the preamble with their meanings; 14's pin
  and URL macros are printed literally; 14's hand-set equation numbers and
  its hard-coded "Section 1/4/6/7/8" now point to its equations and
  sections here; a conventions table lists the letters that clash (`L`,
  `B`, `M`, `n`, `D_n`, `C`, `F`/`f`, `c`, `U`, `H`, `S`, `A`, `V`, `h`, `e`,
  `P`, `Q`, `K`, `R`). Where 13–15 name their files in prose, the shipped
  names are printed. The title-page lines naming the AI assistant are in
  the provenance appendix only. Dated `[write]` notes credit the research
  note `interaction_combinator_quadratic_topology.md` as an independent
  derivation of 14's loop formula and record the three reductions of the
  review `incoming_substrate_review_1977e6ea6.md`, unapplied. Bibliography:
  eleven new entries (the research note, the two later research-tree notes,
  this report's README as 14 cites it, Lafont 1990, de Falco,
  Lehrer–Zhang, Blum–Evans–Gemmell–Kannan–Naor, Naor–Parter–Yogev,
  Sutherland, Matiyasevich's Scholarpedia article), and the entries for
  Lafont 1997, Matiyasevich 1970 and 2010, Batcher, the project README and
  `MRDP.lean` extended (73 distinct works in all).
- **Macros.** One `\code` (01's `\texttt{\detokenize{#1}}`); 02's `\_`
  escapes inside `\code` removed; the pin macros `\repoSHA` (01 and 07,
  different commits), `\repoCommit` (02) and `\reposha` (04) printed as
  literal identifiers; 04's unused `\repo` URL macro dropped (03's `\repo`
  kept); 06's unused `\word` dropped in favour of 07's. No mathematical
  symbol was renamed; letters that change meaning between Parts are listed
  in the conventions.
