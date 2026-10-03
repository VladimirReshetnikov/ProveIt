# Canonical Diophantine certificates

**Witness-faithful polynomial representations of bounded discrete computation: resource algebra, trace classes, accelerators, polynomial trajectories, memory logs, queues, rewriting, heaps, self-assembly, priority pumping, reaction networks, routing networks, interaction combinators, abelian sandpiles, exponential trajectories and compressed queue traces**

This is a research report dated 30 September 2026, with Parts XV–XVIII dated 2 October
2026, merged from twenty manuscripts: six of batch 60 (its manuscripts 01–06), the only manuscript
of batch 61, which is numbered 07 here, four of batch 62 (its
manuscripts 01, 02, 04 and 05), numbered 08–11 here and added as Parts X–XIII
after the report had been written, and one of batch 63 (its manuscript 02),
numbered 12 here and added as Part XIV, and three of batch 78 (its
manuscripts 01, 04 and 05), numbered 13–15 here and merged into one Part,
XV, and a fourth of batch 78 (its manuscript 06, placed separately in
cluster H3), numbered 16 here and added as Part XVI, and two of batch 79
(its manuscripts 02 and 03, cluster J1), numbered 17 and 18 here and merged
into Part XVII, and two more of batch 79 (its manuscripts 05 and 11, cluster
J3), numbered 19 and 20 here: 19 proves Part XVI's main theorems again and
is printed inside Part XVI as a marked second route, and 20 is added as Part
XVIII. The base is manuscript 05, *Canonical
Trace Polytopes*; its `article.tex` was staged unprefixed and has been
replaced in place by the merged text. All twenty manuscripts prove the same
kind of theorem: an explicit integer polynomial whose natural zeros are in
bijection with the bounded executions (or trace classes of executions) of a
discrete substrate, with exactly one witness each; in 12 the execution is a
terminating chip-routing run, represented by its outcome (firing counts and
sink outputs) rather than its history. In 13–15 the executions are
scheduled reductions of Lafont's interaction combinators, with exact port
wiring and exact counts of port-free cyclic wires. In 16 the execution is the
stabilization of an abelian sandpile on a finite undirected sink graph,
represented by its odometer and stable endpoint. In 17 and 18 the object is
the complete discrete sign chart of a positive-base exponential polynomial
(a loop guard along an exponentially growing trajectory), with one witness
in arithmetic augmented by exact power atoms `y = b^n`, or, for an
externally fixed exponent bit bound, in an ordinary quartic. In 19 the object
is again the sandpile odometer, certified by a system of quadratic residuals
and, on `ℤ³`, by a fixed normal form of 47 finite-deviation fields. In 20 it
is a reliable FIFO execution whose transition trace is supplied as a
straight-line grammar, and a supplied closed macro that repeats
indefinitely. They continue the Lean
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
program" (14), "Research report prepared for the ProveIt project" (16),
and "Research manuscript prepared with ChatGPT for the ProveIt program" (17
and 18, also their PDF metadata), "Research-assistance draft prepared for
the ProveIt project" (19; its PDF metadata reads "OpenAI research-assistance
draft for the ProveIt project") and "Research prepared for Vladimir
Reshetnikov / Developed with ChatGPT for the ProveIt research program" (20;
its PDF metadata reads "Research prepared for Vladimir Reshetnikov with
ChatGPT"). The article prints the batch-62, batch-78
and batch-79 author lines in neutral form and records these assistant names only in its
provenance appendix; the author lines of 12 and 16 name no assistant.

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
| 16 | batch 78, manuscript 06 | `sandpile_diophantine_research`, inner directory `sandpile_diophantine_certificates` (27-page PDF) | *Cubic Diophantine Certificates Without Computation Histories: Canonical sandpile odometers, spatial universality, and exact eventual periods* | `928ea9701` | `1977e6ea6` | `41e7f1189` | Section 3.16 (abstract, package statement, §1); Part XVI (§§2–16, Appendices A–B) |
| 17 | batch 79, manuscript 02 | `Positive_Spectrum_Diophantine`, inner directory `Positive_Spectrum_Diophantine` (27-page PDF) | *Beyond Polynomial Trajectories: Canonical Exponential-Diophantine Certificates for Computation* | `e58b724c2` | `060e08a07` | `224ca41df` | Section 3.17 (scope box, abstract, §1); Part XVII (§§2–14, Appendices A–B), printed first |
| 18 | batch 79, manuscript 03 | `Spectral_Guards_Without_Time_Expansion`, inner directory `Spectral_Guards` (25-page PDF) | *Spectral Guards Without Time Expansion: Canonical Diophantine certificates for exponentially long linear computation* | `e58b724c2` | `060e08a07` | `224ca41df` | Section 3.18 (status boxes, abstract, §1); Part XVII (§§2–14, Appendices A–B), second route |
| 19 | batch 79, manuscript 05 | `no_borrowed_firings`, inner directory `no_borrowed_firings` (24-page PDF) | *No Borrowed Firings: Canonical Diophantine Certificates for Abelian Sandpiles* | `e58b724c2` | `060e08a07` | `bbaf322e5` | Section 3.19 (abstract, §1); Part XVI, Sections M19.1–M19.14 (opening, §§2–14) and M19.A–M19.B (Appendices A–B), a marked second route |
| 20 | batch 79, manuscript 11 | `Compressed_Queue_Diophantine_Research`, inner directory `Compressed_Queue_Diophantine` (28-page PDF) | *Compressed Queue Computation: Grammar-size quartic certificates, exact periodic acceleration, and certified infinite loops* | `44983ed7e` | `ef2fc7990` | `bbaf322e5` | Section 3.20 (status box, abstract, §1); Part XVIII (§§2–15, Appendices A–B) |

Section numbers in the last column are those of each manuscript. Manuscripts
01–07 also contribute to the Introduction and to the back matter
(Implementation and validation, Formalization targets, Research questions,
Conclusions of the manuscripts, Provenance); manuscripts 08–12 keep their
validation, formalization plans, questions and conclusions inside their
Parts, and appear in the back matter only in the provenance appendix and
the bibliography. Manuscripts 13–15 are merged by subject into Part XV,
which closes with their validation, questions, conclusions and
appendices; the source audits of 13 and 14 are in the provenance appendix.
Manuscript 16 is Part XVI in its own order, closing with its validation,
formalization route, questions, conclusion and appendices. Manuscripts 17
and 18 form Part XVII: 17's Sections 2–12, then 18's as a second route, a
written comparison, both question lists, both conclusions and both
appendices. Manuscript 19 is printed inside Part XVI after 16's conclusion,
in its own sections M19.1–M19.14, numbered outside the report's sequence so
that no number moved, and its appendices M19.A–M19.B follow 16's;
manuscript 20 is Part XVIII in its own order, closing with its validation,
formalization path, questions, conclusion and appendices. The Parts are: I Exact commutation and resource algebra;
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
combinators: exact wiring, loop-exact gluing and bounded quartic frontends;
XVI Sandpile certificates: cubic polynomials and quadratic systems, spatial
closure, fixed fields and exact periods; XVII Exponential trajectories:
positive-spectrum sign charts and the order-two power boundary; XVIII
Compressed queue traces: grammar-size quartics, exact macro repetition and
infinite-loop certificates.

The full pins are `e8bb0931d67f80d9fce87a8cddb0f661ff19f956` (01–06),
`725d2ebb6909fe11a13a92354c0f47367a3cbbf5` (07),
`4e128356d0ef75308be8ed405d89aea2ffdb8a57` (08–11; 11 also names
`ccfb084adaa2f32e8d2738a25f82a00377fb3a8c`, a later commit it read on the
live branch) and `e18718e837d43e162252f9a314e8cb797fbd1a1f` (12), and `439c0a2d9c1052595f3de6a29c11511a24fb2e11` (13),
`6914ccca6685baf53b7a35f25efc89366c76ba74` (14) and
`928ea97017a25ebe56d240c84f27d2275d818c75` (15 and 16), and
`e58b724c25bd34533b7a5834cfcbe873dfa01288` (17, 18 and 19), and
`44983ed7ebfd545de55bfdb50e040c82f3d24295` (20). The pin of 07 is the commit
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

Manuscript 16 was written the same morning at `928ea9701`, the pin of 15,
and arrived in the same commit `1977e6ea6`; it was placed separately, by
`41e7f1189` (batch 78, cluster H3), after the placement `aa11f3fef` of
13–15. It read the project README and MRDP guide and this report's
`12-rle-routing-SOURCES.md`, not the article, so it does not cite Part
XIV's question on infinite-background abelian computation, which it
answers, or the Part IX theorems that its single-fold boundary
instantiates. The files it read are unchanged at the batch-78 write except
the project README, which still states the 75- and 87-operation figures it
quotes.

Manuscripts 17 and 18 were written on 2 October 2026 at `e58b724c2`
(11:52), when Parts I–XIV had been written and Parts XV–XVI had not, and
arrived together in `060e08a07` (14:27); they were placed by `224ca41df`
(batch 79, cluster J1). Each read this report's README (18 also
`02-poly-trajectories-sources.md`), not the article, names Part IV as its
starting point, and does not know the other. The repository files they
cite, `Lean/Diophantine/Paper1984/DPR.lean` (17) and
`Lean/Diophantine/Common/DiophantineTrace.lean` (18, blob `08e5796b2`), are
unchanged at the batch-79 write; the project README has grown since and
still states the 75- and 87-operation figures.

Manuscripts 19 and 20 were written on 2 October 2026. 19 was pinned at
`e58b724c2` (11:52), the pin of 17 and 18, when Parts I–XIV had been
written; 16's archive had arrived (`1977e6ea6`, 11:34) but was placed only
at 13:31 (`41e7f1189`), so 16 and 19 are independent texts, and 19's
repository search for "sandpile" found only `12-rle-routing-SOURCES.md`.
19 read the project README, the MRDP guide and that ledger. 20 was pinned
at `44983ed7e` (14:30), when Parts I–XV had been written; it read the
collection README, this report's README and
`07-queue-causality-lean_integration.md` (blob `019f1bb2c`), and could not
retrieve the article (1,456,594 bytes at that pin), so about a quarter of
it re-proves Parts I and VI in one coordinate. 19 arrived in `060e08a07`
(14:27) with 17 and 18, 20 in `ef2fc7990` (16:44); both were placed by
`bbaf322e5` (batch 79, cluster J3). The MRDP guide, the routing ledger and
the integration note are unchanged at this write; the project README and
this report's README have grown, and the project README still states the
75- and 87-operation figures.

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
- **16** for a finite loopless undirected multigraph whose components reach
  a sink: the exact support criterion (a candidate odometer with stable
  nonnegative endpoint is the true one exactly when the endpoint is
  burnable on its support); canonical parallel burning ranks characterized
  by two local comparisons per ordered adjacency; a baseline cubic with
  `13n+6m = 13n+12E` natural coordinates and `14n+6m` summands and a
  compact cubic with `10n+6E` and `10n+7E`, each with exactly one natural
  zero for every input (carrying the odometer, endpoint and ranks), related
  by explicit inverse maps on their zero sets; a two-site example with an
  input needing `10^100+6` topplings (26 witnesses); a directed
  counterexample fixing the scope; on `ℤ^d` with a stable periodic
  background, an exterior collar certifying global halting exactly and a
  unique canonical radius; quadratic witness heights in a box; with Cairns's
  universality theorem, no computable bound on the necessary radius; the
  single-fold equivalence for Cairns's uniform sandpile relation (an
  instance of `cdc:bd:thm:universal`); and the exact minimal eventual period
  `q` of the stabilization along an input ray `a+th`, the least `q` with
  `qL⁻¹h` integral.
- **17** for a fixed shape of positive integer bases `B` and degree bounds
  `d_b` (order `D = Σ(d_b+1)`): the ladder `f_{j+1} = (E−a_j) f_j` ends at
  zero, a row of declared order `m` has at most `2m−1` maximal sign runs
  (sharp), and `D²+1` slots suffice; the local verifier V1–V5, checked only
  at run endpoints through the normalized monotonicity identity, accepts
  exactly the true padded profiles, on `{0,…,T}` and on all of `ℕ` (the tail
  through a leading-coefficient sign test, with no guessed cutoff); a
  compiler with `O(D³)` natural witnesses, quadratic residuals and
  fixed-base power atoms, one complete witness per input; safety, first
  failure, exact minimum and least minimizer; positive rational bases;
  affine maps with split rational spectrum and polynomial guards;
  positive-diagonal triangular polynomial loops through invariant monomial
  spaces; fixed-phase schedules of repeated instruction words; the theorem
  that the complete sign-chart graph of `2^n−y` has a single-fold
  (finite-fold) ordinary representation exactly when every c.e. set has one,
  order one being unconditional; a rational rotation with exactly
  `⌊Tθ/π+1/2⌋` sign changes; non-closure of positive spectra under products;
  exports for the shape `{1,2,4}` (finite: 1,231 witnesses, 1,703 residuals,
  52 atoms, 7,502 quartic monomials; infinite: 1,297, 1,767, 52, 8,256).
- **18** the same sign-chart theorem with ordered bases as inputs: the
  root-removing ladder, the zero bound, the sharp capacity `2d−1`, the
  endpoint theorem with exactly `Q_D = (4D³−6D²−D+6)/3` slot pairs, an
  `O(D⁴)` power-assisted compiler, and, for each externally fixed bit bound
  `B` with `T < 2^B`, an ordinary single-fold quartic with `O(D⁴(B+1))`
  witnesses by binary powering; witness-height bounds; an
  `O(D² log(T+2))`-evaluation chart constructor; an explicit permanent-sign
  threshold `T₀` and an all-time nonnegativity certificate; affine macro
  and first-exit certificates; the oscillation theorem (`u_n =
  Re((3+4i)^n)` changes sign with density `δ_q/π > 0` on every residue
  class); a million-horizon chart with nine occupied blocks; exports for
  `4^n − 10·2^n + 16` (power atoms: 1,294 witnesses, 1,212 residuals, 104
  atoms; quartic `B = 3`: 1,935 witnesses, 1,995 residuals).
- **19** (a second route to 16, written independently) for a finite
  loopless undirected multigraph with an absorbing sink: support burning
  and canonical parallel burning ranks characterized by two local
  inequalities (as in 16); a system of `12n+16E` quadratic residuals in
  `11n+12E` natural witnesses (`E` distinct unordered adjacent pairs, which
  19 writes `m`) with exactly one natural zero, carrying the odometer, if
  legal stabilization terminates and none otherwise; its sum of squares is
  a quartic of exact degree four with an integral rejection gap; unique
  positivity, comparison and mask gadgets; a complete 34-variable example
  (201 monomials) and a false integer root once negative helpers are
  allowed; a no-firing halo on a lattice cube (`47ℓ³−30ℓ²` witnesses and
  `60ℓ³−42ℓ²` residuals in `ℤ³`, `ℓ = 2R+1`); one fixed radius-one quartic
  difference expression with 47 finite-deviation fields and 60 local
  residuals in `ℤ³` whose field solution exists, uniquely, exactly when the
  input stabilizes globally, with unique finite codes and a decidable code
  verifier, and so, with Cairns's theorem, a `Σ⁰₁`-complete relation with a
  unique field witness; no computable input-only bound on the support
  radius, the number of fired sites or the code length; and the height
  bound `u ≤ M/2((R+1)²−x₁²)` in a supplied cube.
- **20** for reliable FIFO actions along a prescribed straight-line trace
  grammar (`g` nodes, `l` leaves, `c` concatenations): the causal endpoint
  theorem `q →τ r ⇔ |q| ≥ R(τ) and qV(τ) = U(τ)r` (the one-queue case of
  07's network theorem); a quartic with exactly `6g+3c+1` natural witnesses
  and `6l+9c+3` quadratic residuals with one zero exactly when the trace
  connects the supplied words, quantifying no intermediate queue (a
  17-node grammar of `2^16` steps gives 151 variables and a witness of
  103,873 bits); the exact number `min(N_len, ⌊M/a⌋)` of copies of a
  closed macro; infinite repeatability as the word equation
  `U^{b/d} q = q V^{a/d}`; a Fine–Wilf pumping threshold
  `⌈(L+a+b−d)/a⌉`; an ordinary unique-witness quartic with `6g+3c+2H+1`
  witnesses for a supplied infinite loop; powered schemas with at most two
  explicit `Pow` predicates per power node; `d` channels; polynomial-time
  decision of supplied grammars through Jeż's external algorithm; no
  computable bound on the size of accepting grammars, and incompleteness of
  periodic lassos for universal divergence.

**Status.** The report is AI-assisted and unrefereed. None of its theorems
is formalized in Lean or Rocq, and no manuscript ships Lean or Rocq files.
The Python programs are finite exact checks of the implementations and
examples, not proofs; the proofs are the mathematical arguments of the
article. The research programme's review of 2 October 2026
(`review_compressed_queue_aebfa.md`, commit `be1fc3f62`) found that the
low-level `Poly` and `Action` constructors of manuscript 20 accept
non-integer coefficients and mutable read words; the compiler's own output
is unaffected and the theorems are not touched. The shipped
`code/20-compressed-queue-queue_certificates.py` is the original; the
tested repair is `compressed_queue_exact_inputs.patch` in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
(see Disclosures, which also record the reviews of 16, 17, 18 and 19).

## Files

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 571 pages
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
16-sandpile-SOURCES.md                   manuscript 16's pinned repository files, literature and novelty boundary
17-positive-spectrum-SOURCE_AUDIT.md     manuscript 17's pin, inspected repository files, literature and verification scope
18-spectral-guards-SOURCES.md            manuscript 18's pin and blob, inspected repository files, literature and claim boundary
19-no-borrowed-firings-SOURCES.md        manuscript 19's pin, inspected repository files, literature and contribution status
20-compressed-queue-CLAIMS_AND_PROVENANCE.md  manuscript 20's claims (by its own theorem numbers), scope, pin, sources and validation

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
code/16-sandpile-build.sh                manuscript 16's suites-and-PDF build script, delivery paths (do not run it here)
code/16-sandpile-sandpile_compact.py     compact compiler, five-way gadget, inverse zero-set maps (prints a demo)
code/16-sandpile-sandpile_cubic.py       baseline compiler, evaluator, certificate constructor, stabilizers, burning ranks
code/16-sandpile-sandpile_spatial.py     compact spatial polynomial: periodic table, collar, canonical radius (prints a demo)
code/16-sandpile-verify.py               baseline checks (seed 20261002); writes --output and the --export-dir examples
code/16-sandpile-verify_compact.py       compact checks (seed 20261003); writes verification_compact.json and example/compact_*
code/16-sandpile-verify_spatial.py       spatial checks; writes verification_spatial.json
code/17-positive-spectrum-Makefile       manuscript 17's make targets (all, pdf, test, clean), delivery paths (do not use it here)
code/17-positive-spectrum-check_export.py    independent JSON checker of the two exports (its expansion test is two-point; see Disclosures)
code/17-positive-spectrum-compiler.py    parametric residual and power-atom compiler; writes the two exports and compiler_summary.json
code/17-positive-spectrum-profiles.py    exponential polynomials, annihilator chain, profile construction, endpoint verifier (prints a demo)
code/17-positive-spectrum-test_applications.py   triangular, parity, minimum and non-closure checks; writes application_checks.json
code/17-positive-spectrum-test_profiles.py   profile and compiler tests (seed 20261002); writes test_results.json
code/18-spectral-guards-Makefile         manuscript 18's make targets (all, pdf, test, clean), delivery paths (do not use it here)
code/18-spectral-guards-quartic_compiler.py  functional gates, power-atom and bounded-bit compilers, serialized-export checker
code/18-spectral-guards-run_tests.py     main tests (seed 20261002); rewrites the seven examples and results.json
code/18-spectral-guards-spectral_guards.py   sequences, ladders, chart construction, endpoint verifier, first negative index, tail threshold
code/18-spectral-guards-supplementary_checks.py  54 single-mode assignments and fractional-input rejections; writes supplementary_checks.json
code/19-no-borrowed-firings-Makefile     manuscript 19's make targets (all, check, pdf, clean), delivery paths (do not use it here)
code/19-no-borrowed-firings-sandpile_certificates.py  exact polynomials, graph and periodic-input interfaces, cube and field certificates, field verifier (prints a demo)
code/19-no-borrowed-firings-verify.py    finite checks (seed 20261002); rewrites examples/ and verification/ beside itself
code/20-compressed-queue-Makefile        manuscript 20's make targets (all, pdf, verify, clean), delivery paths (do not use it here)
code/20-compressed-queue-check_certificate.py  independent checker of the two exports (does not import the compiler; prints JSON)
code/20-compressed-queue-queue_certificates.py  actions, grammars, radix and resource summaries, finite and infinite-loop compilers, loop analyzer
code/20-compressed-queue-verify.py       259,025 exact checks (seed 20261002); rewrites the two exports and verification.json in ../data

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
data/16-sandpile-BUILD_REPORT.json                 build record of the delivered 27-page PDF and the three suites
data/16-sandpile-compact_huge_input_certificate.json   compact 26-coordinate certificate for input (10^100+7, 0)
data/16-sandpile-compact_two_site_polynomial.json  compact two-site cubic: 26 witnesses, degree 3, 324 monomials
data/16-sandpile-compact_two_site_polynomial.txt   the same, expanded as text
data/16-sandpile-huge_input_certificate.json       baseline 38-coordinate certificate for input (10^100+7, 0)
data/16-sandpile-requirements.txt                  sympy==1.14.0
data/16-sandpile-two_site_polynomial.json          baseline two-site cubic: 38 witnesses, degree 3, 216 monomials
data/16-sandpile-two_site_polynomial.txt           the same, expanded as text
data/16-sandpile-verification.json                 recorded run of verify.py (86,975 odometer candidates, 7,660 rank vectors, ...)
data/16-sandpile-verification_compact.json         recorded run of verify_compact.py
data/16-sandpile-verification_spatial.json         recorded run of verify_spatial.py
data/17-positive-spectrum-application_checks.json  recorded run of test_applications.py (735 triangular checks, 82 parity identities, minimum -32 at 3)
data/17-positive-spectrum-compiler_summary.json    counts of the two exports (1,238 and 1,303 coordinates, 1,703 and 1,767 residuals, 52 atoms each)
data/17-positive-spectrum-export_check_log.txt     recorded output of check_export.py on the two exports (PASS)
data/17-positive-spectrum-finite_certificate.json  finite-mode system for the shape {1,2,4}, with sample assignment and expanded quartic (7,502 monomials)
data/17-positive-spectrum-infinite_certificate.json  infinite-mode system for the same shape (8,256 monomials)
data/17-positive-spectrum-test_results.json        recorded run of test_profiles.py (1,134 shapes, 2 x 1,419 exhaustive candidates, 2,528 mutants; elapsed time)
data/18-spectral-guards-artifact_checks.json       delivery record of the delivered 25-page PDF and of the two test records (no script writes it)
data/18-spectral-guards-discrete_not_continuous.json   chart of 4^n - 6*2^n + 8 on [0,6] (integer zeros at 1 and 2; negative at 3/2)
data/18-spectral-guards-hidden_negative.json       chart of 4^n - 10*2^n + 16 on [0,4]
data/18-spectral-guards-hidden_negative_quartic.json   its ordinary quartic, B = 3: 10 inputs, 1,935 witnesses, 1,995 residuals
data/18-spectral-guards-hidden_negative_quasi.json     its power-atom system: 10 inputs, 1,294 witnesses, 1,212 residuals, 104 atoms
data/18-spectral-guards-identically_zero.json      chart of a declared two-coefficient mode with zero coefficients on [0,4]
data/18-spectral-guards-jordan_block.json          chart of (n-2)(n-5)2^n on [0,8]
data/18-spectral-guards-million_step_chart.json    chart of (2^n-2^400)(2^n-2^600) on [0,10^6]: nine occupied blocks, 75 evaluations
data/18-spectral-guards-results.json               recorded run of run_tests.py (seed 20261002; 3,087 + 700 charts, 704 forged, 3,134 perturbations)
data/18-spectral-guards-supplementary_checks.json  recorded run of supplementary_checks.py (54 assignments, 4 fractional-input rejections, 2 exports)
data/19-no-borrowed-firings-pdf_preflight.json  delivery record of the delivered 24-page PDF (no script writes it)
data/19-no-borrowed-firings-results.json   recorded run of verify.py (Python 3.13.5; 43 graphs, 4,855 inputs, 305,620 candidate odometers, 290 witnesses; elapsed time)
data/19-no-borrowed-firings-results.txt    the same run as text (the delivery's latest_run.txt is a byte copy, not shipped)
data/19-no-borrowed-firings-three_dimensional_avalanche.json  odometer and ranks of 100 chips at the origin of Z^3 (19 fired sites, 49 topplings)
data/19-no-borrowed-firings-three_dimensional_field_certificate.json  its normalized 47-field exception table (57 sites)
data/19-no-borrowed-firings-two_vertex_certificate.json  the 34-variable, 40-residual system and its 201-monomial quartic
data/19-no-borrowed-firings-two_vertex_witness.json  its unique witness (zero-based vertex indices)
data/20-compressed-queue-example_quartic.json  four-action example: 31 variables, 33 residuals, 98 monomials, and its witness
data/20-compressed-queue-export_checks.json   recorded output of check_certificate.py on the two exports (PASS)
data/20-compressed-queue-infinite_growth_quartic.json  nine-variable infinite-loop quartic (11 residuals, 29 monomials)
data/20-compressed-queue-verification.json  recorded run of verify.py (Python 3.13.5; 259,025 assertions)
```

Placed in this directory and not yet printed in the article (the write
that prints them will describe them): manuscript 21 (batch-79 manuscript
17, cluster J2), placed by `a7ae02511`:

```
21-eager-tree-VERIFICATION.md
code/21-eager-tree-{analyze_growth,audit_exact_count,build_pdf,canonical,canonical_overlay_audit,canonical_projected,canonical_projected_audit,constant_bit_bound,counter_source,eager_compiler,export_shared_macro,independent_audit,independent_compiler_audit,independent_growth_audit,independent_shared_audit,reproduce,shared_compression,symbolic_audit,tree_kernel,verify_packet_assumptions,verify_shared_macro}.py
data/21-eager-tree-{audit_exact_count_receipt,canonical_identity,canonical_overlay_receipt,canonical_projected_audit_receipt,canonical_projected_identity,canonical_projected_receipt,canonical_receipt,constant_bit_bound,counter_source_receipt,cyclic_counterfeit,eager_compiler_receipt,exact_growth_receipt,identity_certificate,independent_compiler_receipt,independent_growth_receipt,independent_receipt,independent_shared_receipt,literal_universal_tree,packet_assumptions_receipt,receipt,shared_compression_program,shared_compression_receipt,shared_symbolic_proofs,sources,symbolic_receipt,universal_code_circuit,universal_lambda_source}.json
data/21-eager-tree-literal_universal_tree.sexpr
data/21-eager-tree-requirements-optional.txt
```

The directory holds 296 files: 24 at the root (the article, its PDF, this
README and twenty-one provenance and audit files), 106 in `code/` and 166 in
`data/`. Of these, 51 (1 at the root, 21 in `code/`, 29 in `data/`) belong
to manuscript 21, listed in the second block above; the other 245 (23
at the root, 85 in `code/`, 137 in `data/`) are the article, its PDF, this
README and the files of manuscripts 01–20. Per manuscript: 01 has 12 files, 02 10, 03 17, 04 10, 05 16
besides the replaced `article.tex` and `README.md`, 06 15, 07 14, 08 8, 09
9, 10 14, 11 9, 12 9, 13 9, 14 12, 15 10, 16 19 (1 at the root, 7 in
`code/`, 11 in `data/`), 17 13 (1, 6, 6), 18 16 (1, 5, 10), 19 11 (1, 3, 7)
and 20 9 (1, 4, 4). Every file of
manuscripts 01–20 except
`article.tex`, `article.pdf` and `README.md` is byte-identical to the
delivery.

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
| 16 | `cdc:sp:` | `cdc:sp:thm:support` |
| 17 | `cdc:ps:` | `cdc:ps:thm:powbarrier` |
| 18 | `cdc:sg:` | `cdc:sg:thm:quartic` |
| 19 | `cdc:nb:` | `cdc:nb:thm:fields` |
| 20 | `cdc:cq:` | `cdc:cq:thm:compiler` |

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

The batch-78 cluster-H3 write (Part XVI) raised the count from 1105 to 1179.
It adds all 68 labels of manuscript 16, each with the sub-prefix `cdc:sp:`
and none dropped (its bare `thm:compiler` is also a bare label of
manuscripts 13 and 15), and 6 written labels: the Part (`cdc:part:sandpile`),
its conventions section (`cdc:conv:b78-XVI`), the manuscript subsection
(`cdc:sec:ms16`), two labels on unlabelled statements of the manuscript
(`cdc:sp:prop:twosite`, the two-site odometer formula;
`cdc:sp:cor:sites`, no computable bound on the number of toppled sites)
and one on its first question (`cdc:sp:q:digraphs`). No existing label was
renamed, removed or renumbered: the 1105 labels of the Part XV build have
the same numbers and types in the new `.aux` (compared entry by entry).
Part XVI's equations are numbered within its sections; Section 3.16 has no
equation, and no captioned table follows Part XVI.

The batch-79 cluster-J1 write (Part XVII) raised the count from 1179 to
1322. It adds all 114 labels of manuscripts 17 and 18 (17 63, 18 51), each
with its sub-prefix and none dropped (the two share the bare names
`lem:zeros`, `lem:monotone`, `eq:normalized`, `eq:slots`, `sec:compiler`
and `sec:validation`, among others), and 29 written labels: the Part
(`cdc:part:exp`), its conventions section (`cdc:conv:b79-XVII`), the two
manuscript subsections (`cdc:sec:ms17`, `cdc:sec:ms18`), the written
comparison section (`cdc:sec:b79-routes`), six labels on sections and a
subsection that the manuscripts left unlabelled (`cdc:ps:sec:construct`,
`cdc:ps:sec:conclusions`, `cdc:ps:app:checklist`, `cdc:sg:sec:conclusion`,
`cdc:sg:app:format`, `cdc:sg:app:ledger`) and eighteen question labels
(`cdc:ps:q:1` … `cdc:ps:q:10` for 17's Q1–Q10, and `cdc:sg:q:capacity`,
`…:values`, `…:algebraic`, `…:frontend`, `…:branching`, `…:tail`,
`…:complex`, `…:bounded` for 18's questions). 17's section label
`sec:intro`, on its Section 1, sits on the first subsection of Section 3.17.
No existing label was renamed, removed or renumbered: the 1179 labels of
the previous build have the same numbers and types in the new `.aux`
(compared entry by entry). Part XVII's equations are numbered within its
sections and Section 3.17's within subsections (17's equation (1.1) is
(3.17.1)); 17's Table 1 is Table 31, after every existing captioned
table.

The batch-79 cluster-J3 write (manuscript 19 inside Part XVI, Part XVIII)
raised the count from 1322 to 1482. It adds all 129 labels of manuscripts
19 and 20 (19 67, 20 62), each with its sub-prefix and none dropped (the
two share bare names such as `sec:scope`, `sec:compiler`, `sec:examples`
and `eq:counts`, and 20's `sec:subtrates`, a typo, is spelled
`cdc:cq:sec:substrates`), and 31 written labels: the two manuscript
subsections (`cdc:sec:ms19`, `cdc:sec:ms20`), the Part
(`cdc:part:cqueue`), two conventions sections (`cdc:conv:b79-nb`, a
subsection of 19's opening, and `cdc:conv:b79-XVIII`), 19's opening
section (`cdc:nb:sec:opening`), six labels on sections that the
manuscripts left unlabelled (`cdc:nb:sec:conclusion`,
`cdc:nb:app:dependencies`, `cdc:nb:app:artifacts`, `cdc:cq:sec:conclusion`,
`cdc:cq:app:notation`, `cdc:cq:app:package`), nine question labels
(`cdc:nb:q:smaller`, `…:digraphs`, `…:scalar`, `…:sparse`, `…:geometry`,
`…:local`, `…:planar`, `…:abelian`, `…:formal`) and ten
(`cdc:cq:q:constants`, `…:cubic`, `…:summaries`, `…:phases`, `…:periodic`,
`…:simulation`, `…:partialorder`, `…:loss`, `…:practice`, `…:exports`). No
existing label was renamed, removed or renumbered: the 1322 labels of the
previous build have the same numbers, types and anchors in the new `.aux`
(compared entry by entry), except two retitled entries (`cdc:sec:manuscripts`,
now "The twenty manuscripts", and `cdc:part:sandpile`, whose Part title now
names both routes) and the hyperlink anchor of the unnumbered paragraph
`cdc:conv:b62q` (number 71 unchanged; seven unnumbered paragraphs were added
before it). Manuscript 19's sections inside Part XVI are numbered M19.1–M19.14
and M19.A–M19.B, outside the report's sequence (their theorems and
equations M19.`N`.`k`), so that Part XVI's appendices stay Sections
173–174 and Part XVII stays Sections 175–206; its conventions longtable
restores the table counter, so 17's Table 1 is still Table 31. Part XVIII
is Sections 207–223, after every existing numbered section.

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

**Manuscript 16** (package root `sandpile_diophantine_certificates/`; flat,
with `example/`)

| Delivered | Shipped |
|---|---|
| `SOURCES.md` | `16-sandpile-SOURCES.md` |
| `build.sh` | `code/16-sandpile-build.sh` |
| `sandpile_compact.py` | `code/16-sandpile-sandpile_compact.py` |
| `sandpile_cubic.py` | `code/16-sandpile-sandpile_cubic.py` |
| `sandpile_spatial.py` | `code/16-sandpile-sandpile_spatial.py` |
| `verify.py` | `code/16-sandpile-verify.py` |
| `verify_compact.py` | `code/16-sandpile-verify_compact.py` |
| `verify_spatial.py` | `code/16-sandpile-verify_spatial.py` |
| `BUILD_REPORT.json` | `data/16-sandpile-BUILD_REPORT.json` |
| `example/compact_huge_input_certificate.json` | `data/16-sandpile-compact_huge_input_certificate.json` |
| `example/compact_two_site_polynomial.json` | `data/16-sandpile-compact_two_site_polynomial.json` |
| `example/compact_two_site_polynomial.txt` | `data/16-sandpile-compact_two_site_polynomial.txt` |
| `example/huge_input_certificate.json` | `data/16-sandpile-huge_input_certificate.json` |
| `example/two_site_polynomial.json` | `data/16-sandpile-two_site_polynomial.json` |
| `example/two_site_polynomial.txt` | `data/16-sandpile-two_site_polynomial.txt` |
| `requirements.txt` | `data/16-sandpile-requirements.txt` |
| `verification.json` | `data/16-sandpile-verification.json` |
| `verification_compact.json` | `data/16-sandpile-verification_compact.json` |
| `verification_spatial.json` | `data/16-sandpile-verification_spatial.json` |

Part XVI is Sections 157–174 of the article: 157 its conventions, 158–172
manuscript 16's Sections 2–16 (its Section `N` is Section `156+N`), and
173–174 its Appendices A–B; its Section 1 is Section 3.16.1. Its theorem
and equation numbers `N.k` become `(156+N).k` (for example its Theorem 6.1,
the baseline compiler, is Theorem 162.1, and equation (6.6) is (162.6)),
because both are numbered within sections and the write added no numbered
item. 16's delivered README (not shipped) proves the two-site formula by
reference to "article.tex, Section 8": that is Section 164 and
Proposition 164.1 (`cdc:sp:prop:twosite`).

**Manuscript 17** (package root `Positive_Spectrum_Diophantine/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/17-positive-spectrum-Makefile` |
| `SOURCE_AUDIT.md` | `17-positive-spectrum-SOURCE_AUDIT.md` |
| `code/check_export.py` | `code/17-positive-spectrum-check_export.py` |
| `code/compiler.py` | `code/17-positive-spectrum-compiler.py` |
| `code/profiles.py` | `code/17-positive-spectrum-profiles.py` |
| `code/test_applications.py` | `code/17-positive-spectrum-test_applications.py` |
| `code/test_profiles.py` | `code/17-positive-spectrum-test_profiles.py` |
| `data/application_checks.json` | `data/17-positive-spectrum-application_checks.json` |
| `data/compiler_summary.json` | `data/17-positive-spectrum-compiler_summary.json` |
| `data/export_check_log.txt` | `data/17-positive-spectrum-export_check_log.txt` |
| `data/finite_certificate.json` | `data/17-positive-spectrum-finite_certificate.json` |
| `data/infinite_certificate.json` | `data/17-positive-spectrum-infinite_certificate.json` |
| `data/test_results.json` | `data/17-positive-spectrum-test_results.json` |

**Manuscript 18** (package root `Spectral_Guards/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/18-spectral-guards-Makefile` |
| `SOURCES.md` | `18-spectral-guards-SOURCES.md` |
| `code/quartic_compiler.py` | `code/18-spectral-guards-quartic_compiler.py` |
| `code/run_tests.py` | `code/18-spectral-guards-run_tests.py` |
| `code/spectral_guards.py` | `code/18-spectral-guards-spectral_guards.py` |
| `code/supplementary_checks.py` | `code/18-spectral-guards-supplementary_checks.py` |
| `examples/discrete_not_continuous.json` | `data/18-spectral-guards-discrete_not_continuous.json` |
| `examples/hidden_negative.json` | `data/18-spectral-guards-hidden_negative.json` |
| `examples/hidden_negative_quartic.json` | `data/18-spectral-guards-hidden_negative_quartic.json` |
| `examples/hidden_negative_quasi.json` | `data/18-spectral-guards-hidden_negative_quasi.json` |
| `examples/identically_zero.json` | `data/18-spectral-guards-identically_zero.json` |
| `examples/jordan_block.json` | `data/18-spectral-guards-jordan_block.json` |
| `examples/million_step_chart.json` | `data/18-spectral-guards-million_step_chart.json` |
| `validation/artifact_checks.json` | `data/18-spectral-guards-artifact_checks.json` |
| `validation/results.json` | `data/18-spectral-guards-results.json` |
| `validation/supplementary_checks.json` | `data/18-spectral-guards-supplementary_checks.json` |

Part XVII is Sections 175–206 of the article: 175 its conventions,
176–186 manuscript 17's Sections 2–12 (its Section `N` is Section
`174+N`), 187–197 manuscript 18's Sections 2–12 (its Section `N` is
Section `185+N`), 198 the written comparison, 199 and 200 the two
manuscripts' Sections 13 (research questions), 201 and 202 their Sections
14 (conclusions), 203–204 17's Appendices A–B and 205–206 18's Appendices
A–B. Section 1 of 17 is Section 3.17.1–3.17.4, that of 18 is Section
3.18.1–3.18.3. In Sections 176–197 theorem and equation numbers `N.k`
become `(174+N).k` for 17 and `(185+N).k` for 18 (for example 17's Theorem
4.2, the local verifier, is Theorem 178.2, and its Theorem 10.3, the
order-two boundary, is Theorem 184.3; 18's Theorem 4.1 is Theorem 189.1
and its equation (4.4), the pair count, is (189.4)), because both are
numbered within sections and the write added no numbered item there. 17's
Q1–Q10 are Research questions 199.1–199.10 (199.1 also prints 18's first
question), and 18's other eight questions are 200.1–200.8. Neither
delivered README nor audit cites a theorem by number.

**Manuscript 19** (package root `no_borrowed_firings/`; flat, with
`examples/` and `verification/`)

| Delivered | Shipped |
|---|---|
| `Makefile` | `code/19-no-borrowed-firings-Makefile` |
| `SOURCES.md` | `19-no-borrowed-firings-SOURCES.md` |
| `sandpile_certificates.py` | `code/19-no-borrowed-firings-sandpile_certificates.py` |
| `verify.py` | `code/19-no-borrowed-firings-verify.py` |
| `examples/three_dimensional_avalanche.json` | `data/19-no-borrowed-firings-three_dimensional_avalanche.json` |
| `examples/three_dimensional_field_certificate.json` | `data/19-no-borrowed-firings-three_dimensional_field_certificate.json` |
| `examples/two_vertex_certificate.json` | `data/19-no-borrowed-firings-two_vertex_certificate.json` |
| `examples/two_vertex_witness.json` | `data/19-no-borrowed-firings-two_vertex_witness.json` |
| `verification/pdf_preflight.json` | `data/19-no-borrowed-firings-pdf_preflight.json` |
| `verification/results.json` | `data/19-no-borrowed-firings-results.json` |
| `verification/results.txt` | `data/19-no-borrowed-firings-results.txt` |

**Manuscript 20** (package root `Compressed_Queue_Diophantine/`)

| Delivered | Shipped |
|---|---|
| `CLAIMS_AND_PROVENANCE.md` | `20-compressed-queue-CLAIMS_AND_PROVENANCE.md` |
| `Makefile` | `code/20-compressed-queue-Makefile` |
| `code/check_certificate.py` | `code/20-compressed-queue-check_certificate.py` |
| `code/queue_certificates.py` | `code/20-compressed-queue-queue_certificates.py` |
| `code/verify.py` | `code/20-compressed-queue-verify.py` |
| `data/example_quartic.json` | `data/20-compressed-queue-example_quartic.json` |
| `data/export_checks.json` | `data/20-compressed-queue-export_checks.json` |
| `data/infinite_growth_quartic.json` | `data/20-compressed-queue-infinite_growth_quartic.json` |
| `data/verification.json` | `data/20-compressed-queue-verification.json` |

Manuscript 19 is printed inside Part XVI as Sections M19.1–M19.14 (M19.1
is a written opening in place of its Section 1, which is Section 3.19.1;
its Section `N ≥ 2` is Section M19.`N`) and M19.A–M19.B (its Appendices
A–B), after Part XVI's Section 172 and after its Section 174 respectively.
Its theorem and equation numbers `N.k` become M19.`N`.`k` (its Theorem 6.1,
the finite compiler, is Theorem M19.6.1, and its equation (6.12), the
counts, is (M19.6.12)); its nine questions are Research questions
M19.13.1–M19.13.9. Part XVIII is Sections 207–223 of the article: 207 its
conventions, 208–221 manuscript 20's Sections 2–15 (its Section `N` is
Section `206+N`), and 222–223 its Appendices A–B; its Section 1 is Section
3.20.1. Its theorem and equation numbers `N.k` become `(206+N).k`, because
both are numbered within sections and the write added no numbered item
there: its Theorem 3.3 is Theorem 209.3, 5.1 is 211.1, 7.1 and 7.2 are
213.1 and 213.2, 8.2 is 214.2, 9.1 is 215.1, 10.2 is 216.2, 11.1 is 217.1,
12.2 and 12.3 are 218.2 and 218.3, and its Corollary 12.1 is Corollary
218.1 (20's claims ledger cites the theorems by its own numbers); its ten
research items are Research questions 220.1–220.10. 19's delivered texts
cite no theorem by number.

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
so nothing was excluded as a heavy regenerable artifact. For the batch-78
addition 16: its `article.tex`, delivery `README.md` and 27-page
`article.pdf` survive in the same arrival commit `1977e6ea6`, as members of
`sandpile_diophantine_research.zip`
(`git show 1977e6ea6:docs/incoming/sandpile_diophantine_research.zip`); its
checksum ledger `MANIFEST.sha256` (22/22) was verified and retired at
placement (`41e7f1189`). Its largest file is 121,573 bytes, so nothing was
excluded as heavy. For the batch-79 additions 17 and 18: their
`article.tex`, delivery `README.md` and PDFs (27 and 25 pages) survive in
the arrival commit `060e08a07`, as members of
`Positive_Spectrum_Diophantine.zip` and
`Spectral_Guards_Without_Time_Expansion.zip`
(`git show 060e08a07:docs/incoming/<archive>.zip`). 18's checksum ledger
`SHA256SUMS.txt` (20/20) was verified and retired at placement
(`224ca41df`); 17 delivered no ledger. Two in-archive copies were not
shipped: 17's `data/test_log.txt` (the same bytes as
`data/test_results.json`; its Makefile writes it by redirection) and 18's
`validation/test_output.txt` (the same bytes as `validation/results.json`).
The largest file of the two is 18's `hidden_negative_quartic.json`
(483,010 bytes), so nothing was excluded as a heavy regenerable artifact
and no data need reconstructing. For the batch-79 additions 19 and 20: their
`article.tex`, delivery `README.md` and PDFs (24 and 28 pages) survive in
the arrival commits `060e08a07` and `ef2fc7990`, as members of
`no_borrowed_firings.zip` and `Compressed_Queue_Diophantine_Research.zip`
(`git show 060e08a07:docs/incoming/no_borrowed_firings.zip`,
`git show ef2fc7990:docs/incoming/Compressed_Queue_Diophantine_Research.zip`).
19's checksum ledger `SHA256SUMS` (15/15) was verified and retired at
placement (`bbaf322e5`); 20 delivered no ledger. Two in-archive copies were
not shipped: 19's `verification/latest_run.txt` (the same bytes as
`verification/results.txt`) and 20's `data/verification_stdout.txt` (the
same bytes as `data/verification.json`). The largest file of the two is
19's `three_dimensional_field_certificate.json` (35,829 bytes), so nothing
was excluded as heavy and no data need reconstructing.

## What is claimed and what is not

The report claims the theorems of the twenty manuscripts, with the proofs
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
scheduled compiler with its exact ledger, disjunction and lasso. For Part
XVI: 16's support criterion, canonical-rank characterization, comparison
and five-way gadgets, the baseline and compact cubic compilers with their
exact coordinate and summand counts and inverse zero-set maps, the two-site
formula, the collar and canonical-radius theorems with their spatial counts,
the box height bound, the no-computable-radius theorem (conditional on
Cairns's universality theorem), the single-fold equivalence and the exact
eventual period. For Part XVII: 17's ladder, run bound, local verifier for
finite and infinite profiles, `O(D³)` power-assisted compiler and its
consequences (safety, first failure, minimum, rational bases, affine,
triangular and fixed-phase transfers), the order-two equivalence and the
rotation count; 18's endpoint theorem with its pair count, the `O(D⁴)`
compiler, the bounded-bit quartics, the height bounds, the chart
constructor, the tail threshold and all-time certificate, the affine macro
certificates and the residue-class oscillation theorem. For Part XVI, also
19's quadratic residual system with its integral gap, its gadgets, its
halo, the fixed-field normal form with its unique codes, its completeness
statement (conditional on Cairns's theorem) and its seed and code-length
statements, besides its second proofs of 16's theorems. For Part XVIII: 20's
endpoint theorem (a second route to Part VI's), the grammar-size quartic
with its exact counts, the exact repetition count, the conjugacy
criterion, the pumping threshold, the infinite-loop quartic, the powered
schemas with their explicit predicates, the multichannel extension, the
compressed decision corollary (conditional on Jeż's algorithm) and the two
impossibility theorems. It does not claim the following. Each item is stated by at least the
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
  for neither. 16 has not established worldwide priority for its compilers
  (abstract, Appendix B, `SOURCES.md`); burning (Dhar), least action
  (Fey–Levine–Peres; Friedrich–Levine), sandpile universality (Cairns) and
  the group-periodicity mechanism are prior work, and its single-fold
  boundary is the pattern of `cdc:bd:thm:universal`, not a new theorem. The
  write adds the credits to Dhar and Fey–Levine–Peres, which 16 names or
  omits without citation. Batch 79: 17 proposes novelty only relative to
  its targeted audit (scope box, `SOURCE_AUDIT.md`) and credits the loop
  classes, closed forms and linearizations to Tiwari, Hosseini–Ouaknine–
  Worrell and Hark–Frohn–Giesl, the real zero bound as a standard
  Chebyshev mechanism, and the single-fold exponential representation to
  Jones–Matiyasevich; 18 states that historical priority is not
  established and claims neither recurrence-positivity decidability,
  single-fold exponential representability, the sum-of-squares quartic
  reduction nor binary powering (status box, `SOURCES.md`). Their case of
  base 1 is Part IV's sign tower and quartic (`cdc:pt:thm:tower`,
  `cdc:pt:thm:main`), and 17's power-graph lemma re-proves
  `cdc:pt:prop:exponential-boundary`; the article prints these as
  pointers, with no novelty claimed. Batch 79, cluster J3: 19 says that the
  priority of its products "has not been established" and claims neither
  burning nor universality (Section 1, `SOURCES.md`); its support
  criterion, ranks, halo, height bound and radius barrier are also 16's,
  proved independently the same day, and an editorial note claims
  priority for neither. 20 asserts no priority (status box, Section 1.3,
  claims ledger), credits queue action algebras to
  Huschenbett–Kuske–Zetzsche, loop acceleration and queue universality to
  Köcher, the two-period theorem to Fine–Wilf (Rankin) and cyclic-tag
  universality to Cook and Woods–Neary; its resource algebra and endpoint
  theorem are Part I's and Part VI's, printed with pointers.
- **Not formal.** No new Lean, Rocq or Coq proof was written or compiled,
  the repository's Lean build and axiom audits were not rerun, and
  repository documentation is not treated as a kernel audit (all twenty;
  16's MRDP axiom audit was not rerun, and its formalization route names
  "proposed module boundaries, not names of already implemented files").
  17 and 18 present formalization checklists only (17's Appendix B, 18's
  Section 12.3), and 17's citation of `DPR.lean` is "inspected, not
  rebuilt".
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
  Section 10, 15's Section 8.2 and `CLAIMS.md`). 16's single-fold boundary
  is likewise an equivalence, and it settles neither single-fold nor
  finite-fold MRDP nor a fixed cubic universal equation; canonical spatial
  witnesses do not prove single-fold MRDP, because encoding the
  variable-length tuple introduces new auxiliaries. 17's order-two theorem
  is likewise an equivalence: the chart graph of `2^n−y` is as hard as the
  general single-fold (finite-fold) problem ("a reduction, not a
  resolution", in its delivered README), and it is no lower bound for every order-two shape.
  Replacing the power atoms of 17's and 18's systems by MRDP witnesses
  keeps existence and loses the unique witness. Neither manuscript resolves
  the Skolem or Positivity problems.
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
  ledger and 15's counts decline that comparison. 16's finite-graph cubics
  have fixed arity for one graph and are a family indexed by the graph; its
  spatial cubics are a family indexed by the radius, whose arity grows with
  it, and the radius has no computable input-only bound. Its counts are
  coordinates and structured summands, not expanded monomials (the compact
  two-site cubic has fewer coordinates but more monomials, 324 against
  216) or arithmetic operations, and it does not improve the 75/87 figures.
  17's and 18's systems have fixed arity for one shape, uniform in the
  coefficients and the horizon, but they are power-assisted (exact atoms
  `y = b^n`, so their quartics are not complete ordinary equations); 18's
  ordinary quartics are a family indexed by an externally fixed bit bound
  `B`, valid for `T < 2^B`. Their counts are coordinates, residuals and
  atoms, not bit lengths (a value at the horizon `T` has about `T log b`
  bits; 18's squaring table about `2^B log M`) or expanded monomials, and
  neither improves the 75/87 figures.
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
- **16, scope.** The theorems need finite, loopless, undirected multigraphs
  whose components reach a sink; general dissipative directed graphs are
  excluded, and the manuscript's two-vertex directed example shows that
  burning alone accepts a false odometer there. Natural witnesses are
  essential; over the integers the weighted squares need not be
  nonnegative, and the four-square variant is finite-fold of degree six, not
  single-fold. Cairns's three-dimensional universality is imported, not
  reproved or implemented: no Turing-machine-to-sandpile loader exists in
  the package. The radius is a compiler parameter; the spatial compiler
  takes a finite periodic table and finite overrides, not an oracle. The
  height bound bounds witnesses in a given box, not the radius. `T₀` is a
  sufficient transient, not the first periodic time. The implementation is
  a dense-matrix reference compiler, not an optimized sparse-grid solver.
  The finite tests do not test all graphs, all witnesses or the universal
  reduction. The rational generating-function formula asserts no OEIS
  identity. The planar questions are attributed to Cairns's arXiv version
  2, without an exhaustive audit of their later status. The delivered
  constructors accept inputs mutated after validation (three cases found
  by the research tree's review; see Disclosures); no theorem depends on
  them.
- **19, scope.** Finite loopless undirected multigraphs; directed toppling
  matrices are excluded, and the directed example shows why. The natural
  domain is essential (a false integer root exists with negative helpers);
  replacing natural witnesses by four integer squares keeps existence and
  destroys uniqueness. The 47 fields are fields, not 47 integer witnesses:
  no uniqueness-preserving conversion to a fixed-arity integer polynomial,
  no single-fold MRDP, no arithmetic-operation optimality, no improvement
  of the 87-operation bound and no Lean claim. The rejection gap is
  discrete; no numerical conditioning is claimed. The counts are not
  claimed optimal, and the linear size is a residual-level statement for
  unbounded degree. Cairns's simulation is imported, not reproved or
  instantiated; the questions attributed to Cairns are not certified as
  open in October 2026. The height bound is conditional on a supplied cube
  and not sharp; the radius bounds exclude computable majorants only. The
  lower-level cube interface leaves the stable-tail and containment
  obligations to the caller. The tests cover finite graphs and explicit
  avalanches, not a universal Turing-machine-to-sandpile compiler.
- **20, scope.** The whole trace grammar (or macro, or lasso) is supplied:
  no schedule synthesis, no inference of macros, no claim that a long
  computation has a small grammar. The endpoints are actual words;
  arbitrary numbers are not assumed to be radix encodings. Witnesses range
  over `ℕ`; no uniqueness over `ℤ`. The size bounds count variables and
  residuals, not bit lengths (the doubling example's witness has 103,873
  bits). Powered schemas keep explicit `Pow` predicates and are not
  ordinary polynomials; no single-fold or finite-fold MRDP. Periodic lassos
  are sound but incomplete. Corollary 218.1 relies on Jeż's external
  algorithm, which the package does not implement; the measured runtimes
  are not a realization of it. Simulations of other models need not
  preserve grammar size. The pumping threshold is not claimed optimal, and
  the constants are not claimed optimal. Two low-level constructors accept
  noninteger coefficients and mutable read words (found by the research
  tree's review; see Disclosures); no theorem depends on them.
- **17, scope.** Bases are fixed positive integers (or rationals after a
  fixed scaling, where minimizing `Kq^n f(n)` is not minimizing `f(n)`);
  positive algebraic irrational bases are outside the encoding. Repetition
  counts of fixed phases are inputs: unbounded branching is not compressed,
  and existentially quantified counts may give several witnesses. The
  rotation theorem limits bounded raw sign-run certificates, not every
  short description of the recurrence. The implementation is a scalar
  compiler: the affine and triangular front ends are proved and
  illustrated, not implemented; the large-horizon experiment tests the
  profile generator, not an exported assignment. The finite tests and the
  2,528 mutations are not the uniqueness proof. The delivered programs have
  three defects reproduced by the research tree's review (see
  Disclosures); no theorem depends on them.
- **18, scope.** The quartic family depends on the externally fixed `B`;
  it is not one fixed-arity polynomial eliminating exponentiation
  single-fold, and its witnesses can have about `2^B log M` bits. The tail
  threshold is deliberately conservative; the scalar threshold is
  implemented, but no global-positivity polynomial front end is exported.
  The oscillation theorem rules out maximal sign-chart compression and its
  fixed-residue variants, not other Diophantine certificates, and proves no
  undecidability. Rational update matrices need an extra integrality
  argument. There is no automatic matrix or Jordan front end, no branching
  compiler and no Lean artifact. `verify_export` checks the equations
  present in an export, not that they are the compiler's output; the
  research tree's review adds a checker-contract defect (see
  Disclosures).
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

Part XVI (manuscript 16) relies on no formal declaration either. It cites,
as context only, the MRDP guide `Lean/MRDP.md` (natural witnesses, a fixed
witness tuple, no numerical complexity bound) and the project README's
75- and 87-operation figures, which it does not improve; its formalization
route names proposed modules, none of which exists, and leaves Cairns's
reduction as a named assumption. The project has no sandpile, chip-firing
or burning material, and no theorem of Part XVI is formalized in Lean or
Rocq; placing the manuscript beside the formal project confers no formal
status on it. The research note `incoming_substrate_review_1977e6ea6.md`
(`44b28c395`) of the separately maintained research tree reviews this
archive too: it confirms the support criterion, the coordinate counts, the
collar and canonical-radius arguments and the eventual period, reproduces
three constructor defects (see Disclosures) and supplies the patch
`sandpile_immutable_input_guards.patch` beside it, which is not applied
here.

**Relations (batch 78, cluster H3).** Part XVI answers Part XIV's question
"Infinite-background abelian computation" for finite undirected sink graphs
and finite global stabilization on `ℤ^d` (directed dissipative graphs stay
open), answers in part the next question, "Explicit preperiods and more
general abelian processors", and answers in part `cdc:q:restricted` for
finite sandpiles. Dated notes record this after the three questions, in
Part XIV's opening ("Batch 78") and after its remark on Cairns, in Part IX
(after the universal-halting equivalence and in the no-bound
proposition's specializations), and inside Part XVI, where a note shows
that Part XI's classification (`cdc:of:thm:classification`,
`cdc:of:cor:no-cubic-universal`) applies to its orthant-nonnegative cubics,
so that no fixed-arity cubic of that kind can carry Cairns's universality.
No neighbouring report was edited in this write.

**Reciprocal notes (batch 78, cluster H3).** The same cluster opened
[quadratic-orthant-certificates](../quadratic-orthant-certificates/)
(`qoc:`, written in `c51b9880d` from batch-78 manuscripts 08, 12 and 14,
its sources 08, 12 and 14), whose three Parts are degree-two,
orthant-nonnegative certificates at the level `D⁺₂ = SL` of Part XI.
Dated notes of 2 October 2026 record the relation here, without new
labels: after `cdc:of:thm:classification` (its source 08 re-proves
`D⁺₃ ⊆ SL`, `cdc:of:cor:squares`, `cdc:of:cor:no-cubic-universal`, the
penalty `E_a` and `cdc:of:prop:quartic`, printed there as second routes;
its program-uniform quartic theorem `qoc:mp:thm:programdegree` is new);
after the remark following `cdc:of:thm:ranks` (its Theorem
`qoc:ts:thm:fixedpoint` generalizes the two-cut ranks to positive delays,
exclusive labels and certified absence); after `cdc:q:acceleration` (its
Part III realizes the restricted target for one fixed universal Waterfall
program at each fixed horizon); after `cdc:q:restricted` (answered in part
by its decidable common-column class, a horizon-free single-fold quadratic
for the outcome); and after Part XII's questions "Canonical macro
decompositions" (a forced macrostep normal form, for a substrate other than
priority programs) and "A small explicit fixed interpreter" (an analogue in
another substrate, not an answer). No question of this report is answered
in full.

Part XVII (manuscripts 17 and 18) relies on no formal declaration either.
17 cites, as the classical input of its order-two theorem, the
single-fold unary exponential representation `JM1984.RM.re_sfu` and
`JM1984.RM.re_single_equation` (`Lean/Diophantine/Paper1984/DPR.lean`,
lines 309 and 318), which the project does formalize (the article's remark
`cdc:bd:rem:sfu`); 18 cites `Diophantine.boundedForall_dioph`,
`Diophantine.exactIter_dioph` and `Diophantine.existsExactIter_dioph`
(`Lean/Diophantine/Common/DiophantineTrace.lean`) as existence-level
context. Both files are unchanged since their pin. No theorem of Part XVII
is formalized in Lean or Rocq, neither manuscript ships Lean or Rocq
files, and placing them beside the formal project confers no formal status
on them. The research note `review_spectral_060e08a07.md` (`2c311e525`,
indexed in `incoming_substrate_review_2a8a39599.md`, `c00ce825a`) of the
separately maintained research tree reviews both archives (with a third
batch-79 archive placed elsewhere): it finds the endpoint argument, the
eventual-sign test, the triangular transfer, the order-two boundary, the
pair count, the bounded-bit quartic, the tail threshold and the
oscillation theorem sound, reproduces three defects of 17's programs and
one checker contract of 18's (see Disclosures), and supplies the tested
patches `positive_boundaries.patch` and `spectral_boundaries.patch` in
`Papers/research-wip/native-stream-queue/spectral_repairs_060e08a07/`,
which are not applied here.

**Relations (batch 79, cluster J1).** Part XVII extends Part IV from
polynomial to positive-base exponential trajectories (its case of base 1
is Part IV's tower) and sharpens Part IX's
`cdc:pt:prop:exponential-boundary` to an equivalence for one explicit
order-two chart graph. It answers in part, and re-scopes, Source 02 of
`cdc:q:compression` ("the first genuinely exponential extension"): the
subclass has unique horizon-independent certificates with the
exponentiation exposed as power atoms, ordinary quartics for every
externally fixed bit bound, and the uniform ordinary target is equivalent
to the single-fold problem already for `2^n−y`. Dated notes record this
after the remark that follows `cdc:pt:thm:tower`, after
`cdc:pt:prop:exponential-boundary` and at `cdc:q:compression`. The same
placement opened the neighbouring reports
[polynomial-witness-histories](../polynomial-witness-histories/) and
[smooth-diophantine-finalizers](../smooth-diophantine-finalizers/); the
latter's finalizer post-processes any quadratic residual system, such as
18's bounded-bit residuals, but no note about it was added here. No
neighbouring report was edited in this write.

Manuscripts 19 and 20 rely on no formal declaration either. 19 cites, as
context only, the MRDP guide `Lean/MRDP.md` and its natural-witness
interface `Diophantine.mrdp` (`Lean/Diophantine/MRDP.lean`) for its
ordinary-existence corollary, and the project README's 87-operation
figure, which it does not improve; its formalization paragraph is a
proposal. 20 names no Lean declaration; its formalization path follows
07's integration note (`07-queue-causality-lean_integration.md`, "not an
implemented formalization"). No theorem of 19 or 20 is formalized in Lean
or Rocq, neither ships Lean or Rocq files, and placing them beside the
formal project confers no formal status on them. The separately
maintained research tree reviewed both archives:
`review_boundary_sandpile_060e08a07.md` (`49bc4c654`, indexed in
`incoming_substrate_review_2a8a39599.md`) finds no semantic or domain
defect in 19 and verifies a projection to `8n+12E` witnesses and `9n+16E`
residuals (44 fields and 57 residuals in `ℤ³`), a zero-set equivalence
with no operation saving claimed; `review_compressed_queue_aebfa.md`
(`be1fc3f62`, indexed in `incoming_substrate_review_aebfa386e.md`) finds
no theorem-level defect in 20, reproduces two constructor defects (see
Disclosures) with the patch `compressed_queue_exact_inputs.patch`, which
is not applied here, and verifies a projection of the finite compiler to
`6c+1` coordinates and `6c+3` residuals. Its review of the placement
(`review_placement_bbaf322e5.md`, `5b633fcf9`) authenticates the shipped
files against the archives and supplies a portable stager,
`replay_placed_substrates_bbaf322e5.py`, that restores the delivered
layouts from Git.

**Relations (batch 79, cluster J3).** 19 is a second route to Part XVI's
answer to Part XIV's question "Infinite-background abelian computation"
(a dated note after that question), and answers nothing else. 20 answers
the queue clause of `cdc:q:storage` (reliable FIFO actions have an exact
six-coordinate summary composing by unique quadratic gadgets; arbitrary
powers keep explicit exponentiation predicates) and bears in part on
`cdc:q:acceleration` (prescribed macros only) and `cdc:q:readcounts`
(action-dependent reads along a supplied schedule); dated notes record
this after the three questions. The research tree's projections answer in
part 19's first question and 20's first (dated notes in the article).
Part XVIII cites the neighbouring report *liveness-beyond-halting* by its
label `lbh:qd:prop:lasso` (finite-region lassos and the remark that lassos
are not complete), and Part XVI and Part XVIII cite each other for the
same borrowing obstruction. No neighbouring report was edited in this
write.

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

The recorded build has 571 pages (196 before batch 62, 306 before batch 63,
338 before batch 78, 419 after Part XV, 449 after Part XVI,
451 after the reciprocal notes, 452 after restoring the XVI organization row,
509 after Part XVII, 571 after manuscripts 19 and 20),
with no errors, warnings, undefined references or citations, multiply
defined labels, duplicate destinations or overfull boxes; the one underfull
line (in manuscript 01's introduction, Section 3.2) is the same as in the batch-62 build. Batch 63 adds
five macros for manuscript 12 (`\rankf`, `\UP`, `\coUP`, `\NP`, `\coNP`) and
no package. Batch 78 adds five macros for manuscripts 13–15 (`\M`, `\PP`,
`\multiset`, `\cyc`, `\id`) and no package; the batch-78 build has no
error, warning or overfull box, and its one underfull line is the one
above. Part XVI (batch 78, cluster H3) adds no macro and no package
(manuscript 16's `\Ccmp`, `\Poly` and `\diag` are written out and its
`\ind` printed with `\indset`); its build likewise has no error, warning,
undefined reference, duplicate destination or overfull box, and the same
single underfull line. The reciprocal notes of cluster H3 (six dated notes, no label) add two
pages and change no label number (compared in the `.aux`); that build has
the same clean log and the same single underfull line.

The organization-table correction was rebuilt in a scratch directory with
three `pdflatex -interaction=nonstopmode -halt-on-error article.tex` passes
(`latexmk` was unavailable). The final pass has no errors, warnings, unresolved
references or overfull boxes; the same single underfull line remains. The
corrected table was visually inspected. The integration review and pinned
byte-preservation checker are recorded in
[the research review](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_canonical_revision_cb8238b64.md).

Part XVII (batch 79, cluster J1) adds three macros (`\Pow`, `\wt`,
`\Repart`) and no package. It was built in a scratch directory with
`latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX,
pdfTeX): no errors, warnings, undefined references or citations, multiply
defined labels, duplicate destinations or overfull boxes, and the same
single underfull line as before. Layout-only changes, with the words
unchanged: 17's `\texttt{Paper1984/DPR.lean}`, `\texttt{re\_sfu}` and
`\texttt{re\_single\_equation}` print with `\path` so that they can break
(one overfull and one underfull line otherwise), and the three columns of 18's theorem
ledger are set ragged right (one underfull line otherwise). The title page,
Sections 3.17 and 198, the opening and conventions of Part XVII, Table 31,
the merged question and the provenance table were rendered and inspected.

Manuscripts 19 and 20 (batch 79, cluster J3) add fourteen macros (19's
`\degS`, `\GE`, `\NZ`, `\FS`, `\shift`; 20's `\pref`, `\suff`, `\lcp`,
`\readw`, `\writew`, `\scale`, `\res`, `\sur`, and `\qval` for 20's
radix value, which 20 wrote `\code`), two counters (`cdcsavedsection`,
`cdcsavedtable`) and a length macro `\cdctocsec` for the width of section
numbers in the contents (2.1em, and 3.6em for the entries M19.x), and no
package. Built in a scratch directory with
`latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX,
pdfTeX): 571 pages, no errors, warnings, undefined references or citations,
multiply defined labels, duplicate destinations or overfull boxes, and the
same single underfull line as before. Layout-only changes: the three
columns of 19's Section-1 table are set ragged right, and 19's two
`\Needspace` hints are dropped. The title page, the contents page with the
entries M19.x, Sections 3.19–3.20, the opening of 19's block (M19.1), its
compiler section, and the opening of Part XVIII were rendered and
inspected.

## Rerunning the checks

Every suite needs Python 3.10 or later and the standard library only,
except 16's three verifiers, which need SymPy 1.14.0
(`data/16-sandpile-requirements.txt`; the recipe uses `uv`). Every
suite rewrites its recorded outputs at fixed paths relative to its own
location, and most scripts import their siblings by delivered name, so run
them **on a copy with the delivered layout**, never in the report
directory. The recipes below build such copies, `r01` … `r20`, beside
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

# 16: writes r16/verification{,_compact,_spatial}.json and six files in r16/example; the demos print only
mkdir -p r16
for f in sandpile_cubic sandpile_compact sandpile_spatial verify verify_compact verify_spatial; do cp code/16-sandpile-$f.py r16/$f.py; done
(cd r16 && uv run --no-project --with sympy==1.14.0 python verify.py --output verification.json --export-dir example \
  && uv run --no-project --with sympy==1.14.0 python verify_compact.py \
  && uv run --no-project --with sympy==1.14.0 python verify_spatial.py \
  && py sandpile_cubic.py && py sandpile_compact.py && py sandpile_spatial.py)

# 17: writes r17/data/{test_results,application_checks,compiler_summary,finite_certificate,infinite_certificate}.json and export_check_log.txt
mkdir -p r17/code r17/data
for f in profiles compiler check_export test_profiles test_applications; do cp code/17-positive-spectrum-$f.py r17/code/$f.py; done
(cd r17 && py code/profiles.py > /dev/null && py code/test_profiles.py > /dev/null && py code/test_applications.py > /dev/null \
  && py code/compiler.py > /dev/null \
  && py code/check_export.py data/finite_certificate.json data/infinite_certificate.json > data/export_check_log.txt)

# 18: rewrites r18/examples/*.json (seven files), r18/validation/results.json and supplementary_checks.json
mkdir -p r18/code r18/examples r18/validation
for f in spectral_guards quartic_compiler run_tests supplementary_checks; do cp code/18-spectral-guards-$f.py r18/code/$f.py; done
(cd r18 && py code/run_tests.py > /dev/null && py code/supplementary_checks.py > /dev/null)

# 19: rewrites r19/examples/*.json and r19/verification/results.{json,txt}
mkdir -p r19
for f in sandpile_certificates verify; do cp code/19-no-borrowed-firings-$f.py r19/$f.py; done
(cd r19 && py verify.py > /dev/null && py sandpile_certificates.py)

# 20: rewrites r20/data/{example_quartic,infinite_growth_quartic,verification}.json, then the independent check
mkdir -p r20/code r20/data
for f in queue_certificates verify check_certificate; do cp code/20-compressed-queue-$f.py r20/code/$f.py; done
(cd r20 && py code/verify.py > /dev/null \
  && py code/check_certificate.py data/example_quartic.json data/infinite_growth_quartic.json > data/export_checks.json)
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
residuals, energy 0`. The recipe for 16 was run the same way in the
batch-78 cluster-H3 write (Python 3.14.4, SymPy 1.14.0 through `uv`,
Windows; about 37 seconds with `uv` start-up): all three receipts report
`"all_checks_passed": true`, and the nine regenerated files (three
receipts, six example files) equal the shipped ones after removing
carriage returns (no elapsed time or Python version is recorded in them).
The demos print 38 coordinates, 40 summands and value 0 for the baseline
`10^100+7` input (`10^100+6` topplings), 26 coordinates, 27 summands and
value 0 for the compact one, and a spatial certificate of 173 coordinates
with canonical radius 5 and value 0. The recipes for 17 and 18 were run the
same way in the batch-79 cluster-J1 write (Python 3.14.4, Windows; about 7
and 3 seconds). 17's five regenerated files and `export_check_log.txt`
equal the shipped ones after removing carriage returns, except the
`elapsed_seconds` field of `test_results.json` (1.621 recorded);
`check_export.py` prints `PASS` for both exports (1,238 and 1,303 natural
coordinates, 1,703 and 1,767 residuals, 52 power atoms each). 18's seven
examples, `results.json` and `supplementary_checks.json` equal the shipped
ones after removing carriage returns (no elapsed time is recorded). The
research tree's review reports the same outcome for the delivered programs
and for its patched copies. The recipes for 19 and 20 were run the same way
in the batch-79 cluster-J3 write (Python 3.14.4, Windows; about 9 and 5
seconds). 19's `verify.py` prints its text report with `status: PASS`; its
four regenerated examples equal the shipped ones after removing carriage
returns, and `results.json` and `results.txt` differ only in the Python
version (3.13.5 recorded) and `elapsed_seconds` (5.014 recorded);
`sandpile_certificates.py` prints 34 variables, 40 residuals, degree 4,
odometer `[2, 1]` and ranks `[2, 1]`. 20's two exports and
`export_checks.json` equal the shipped ones after removing carriage
returns, and `verification.json` (`"status": "PASS"`, 259,025 checks)
differs only in the Python version. The research tree's reviews report the
same outcome; its review of 20 also reruns the delivered programs with its
patch applied.

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
- Batch 78, cluster H3: 16's verifiers write into the **working
  directory** (`verify.py` where `--output` and `--export-dir` say, by
  default `verification.json` and `example/`; `verify_compact.py` writes
  `verification_compact.json` and `example/compact_*`; `verify_spatial.py`
  `verification_spatial.json`), so run them only inside `r16`. The shipped
  `code/16-sandpile-*` scripts that import a sibling fail at that import,
  because the siblings carry prefixes. Do not run
  `code/16-sandpile-build.sh`: it changes to its own directory and runs
  `verify.py`, `verify_compact.py` and `verify_spatial.py` there, then
  `pdflatex` three times on `article.tex`. As shipped it stops at the first
  step (`code/` holds no `verify.py`); a copy beside unprefixed programs
  would rewrite their receipts and `example/` and then fail on the missing
  manuscript source. It also defaults to `python3`, which may not resolve
  on Windows. Do not run the verifiers with `python -O`: their
  checks are assertions, and the entry points refuse that mode.
- Batch 79, cluster J1: 17's `compiler.py`, `test_profiles.py` and
  `test_applications.py` write into `data/` beside their own `code/`
  directory (the parent of the script's directory), and 18's
  `run_tests.py` and `supplementary_checks.py` into `examples/` and
  `validation/` there, overwriting recorded files; run them only inside
  `r17` and `r18`. The shipped `code/17-*` and `code/18-*` scripts that
  import a sibling (`profiles`, `compiler`, `spectral_guards`,
  `quartic_compiler`) fail at that import, because the siblings carry
  prefixes. 18's `supplementary_checks.py` reads the two
  `hidden_negative_*` exports that `run_tests.py` writes, so run it second.
  Do not run 18's suites with `python -O` (its checks are assertions). Do
  not use `code/17-positive-spectrum-Makefile` or
  `code/18-spectral-guards-Makefile`: their `pdf` targets run `pdflatex`
  three times on `article.tex`, which is now the merged article, and their
  `clean` targets delete its auxiliary files; 17's `test` target writes
  `data/test_log.txt`, which is not shipped, and both use `python3`.
- Batch 79, cluster J3: 19's `verify.py` writes `examples/` and
  `verification/` beside itself (the script's own directory), and 20's
  `verify.py` writes into `data/` beside its own `code/` directory,
  overwriting recorded files; run them only inside `r19` and `r20`. The
  shipped `code/19-no-borrowed-firings-verify.py` and
  `code/20-compressed-queue-verify.py` fail at their imports
  (`sandpile_certificates`, `queue_certificates`), because the siblings
  carry prefixes. 19's checks are assertions: do not run it with
  `python -O`. Do not use `code/19-no-borrowed-firings-Makefile` or
  `code/20-compressed-queue-Makefile`: their `pdf` targets run `latexmk` on
  `article.tex`, which is now the merged article, their `clean` targets
  delete its auxiliary files, and their checks call `python` with the
  delivered names.
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
- **Batch 78, cluster H3 (manuscript 16): shipped text that uses delivery
  names or names unshipped files.** `16-sandpile-SOURCES.md` calls the
  bibliography "in `article.tex`" (16's, not shipped; its text is Section
  3.16 and Part XVI) and names `verification.json`,
  `verification_compact.json` and `verification_spatial.json` (now
  `data/16-sandpile-verification*.json`), and describes the delivered PDF's
  build and rendering check. `data/16-sandpile-BUILD_REPORT.json`
  names the three receipts by delivered name and describes the delivered
  27-page PDF and its rendering review, which are not shipped (the PDF
  survives in `1977e6ea6`); no script writes it. `code/16-sandpile-build.sh`
  runs `verify.py`, `verify_compact.py`, `verify_spatial.py` and `pdflatex
  article.tex` by delivered names. The scripts import one another by
  delivered name (`sandpile_cubic`, `sandpile_compact`, `verify`) and write
  `verification*.json` and `example/…` into the working directory. The
  `coefficient_table_sha256` and certificate hashes inside the three
  receipts hash normalized JSON objects (sorted keys, compact separators),
  not the bytes of the shipped files; the retired `MANIFEST.sha256` held
  file-byte hashes. The article prints the shipped names where 16 names its
  files in prose and keeps its command listing in the delivered layout with
  a note. `data/16-sandpile-requirements.txt` (`sympy==1.14.0`) has the
  same bytes as the requirements files of many other reports, among them
  *group-theoretic-substrates* and
  *probabilistic-quantum-and-continuous-computation*. Layout: the
  article sets the two columns of 16's Section-1 claim table ragged right,
  to avoid two underfull lines; the words are unchanged.
- **Batch 78, cluster H3: defects of 16's delivered programs.** The review
  `incoming_substrate_review_1977e6ea6.md` (`44b28c395`) of the
  Hilbert's-tenth-problem research tree reproduces three input-contract
  defects in `sandpile_cubic.py` and `sandpile_spatial.py` (shipped as
  `code/16-sandpile-sandpile_cubic.py` and
  `code/16-sandpile-sandpile_spatial.py`): `Graph` keeps mutable adjacency
  and degree lists, so a graph mutated after validation into the directed
  counterexample yields an accepted certificate for odometer (2,1) at input
  (0,2), whose true odometer is (0,0); `PeriodicInput` keeps its background
  list, so a background made unstable after a certificate was built still
  evaluates to zero; and a directly constructed `SpatialInstance` bypasses
  the checked builder and can leave a distant defect outside its collar.
  The review's tested patch `sandpile_immutable_input_guards.patch` (beside
  the review in
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`)
  snapshots the inputs and checks direct construction; with it all three
  suites pass and the recorded files are unchanged. It is **not applied**:
  the shipped programs are the delivered bytes, and applying it to the
  prefixed copies (with the file names rewritten) is left to the owner of
  that tree. No theorem of Part XVI depends on the defects, since each
  bypasses a hypothesis the theorems state.
- **Batch 79, cluster J1 (manuscripts 17 and 18): shipped text that uses
  delivery names or names unshipped files.** `17-positive-spectrum-SOURCE_AUDIT.md`
  speaks of "the manuscript", "the article" and "the paper" (17's delivered
  text, now Section 3.17 and Part XVII), says that the PDF was compiled and
  visually reviewed (the 27-page PDF is not shipped; it survives in
  `060e08a07`), and names repository paths only.
  `18-spectral-guards-SOURCES.md` speaks of "the article" and "the supplied
  work" and names repository paths only. `code/17-positive-spectrum-Makefile`
  uses `code/…`, `data/…` (including the unshipped `data/test_log.txt`) and
  `article.tex`; `code/18-spectral-guards-Makefile` uses `code/…` and
  `article.tex`. The scripts use delivery names in their imports and paths:
  17 (`profiles`, `compiler`; `data/`), 18 (`spectral_guards`,
  `quartic_compiler`; `examples/`, `validation/`). Recorded data name
  delivery files: `data/18-spectral-guards-artifact_checks.json` names
  `validation/results.json` and `validation/supplementary_checks.json` and
  describes the delivered 25-page PDF (not shipped) and its Python 3.13.5
  run; no script writes it. 18's examples and 17's exports name no files.
  The article prints the shipped names where 17 and 18 name their files in
  prose and keeps their listings in the delivered layout with notes. 18's
  `SOURCES.md` reports inspecting printed page 590 of the
  Cantone–Cuzziol–Omodeo article, which Part IX cites at page 588 for the
  single-fold normal form; both pages are in the same article.
- **Batch 79, cluster J1: defects of 17's and 18's delivered programs.** The
  review `review_spectral_060e08a07.md` (`2c311e525`) of the
  Hilbert's-tenth-problem research tree reproduces, in 17's programs
  (shipped as `code/17-positive-spectrum-*`): (1) the public constructor
  and verifier in `profiles.py` accept a supplied chain without checking
  that it is the annihilator chain, so the chain `[f, 0]` with rows
  `[0,6]:+` and `[0,6]:0` passes for `f = 4^n − 20·2^n + 64` although
  `f(3) = −32` (the compiler's own path builds the chain; the batch-79
  intake reproduced this case); (2) cached coefficients are mutable, so a
  coefficient changed after caching leaves stale endpoint values and an old
  chart still verifies; (3) `check_export.py` compares the expanded quartic
  with the sum of squared residuals at two points only, so adding
  `(x0−64)(x0−3)` to the delivered finite quartic still prints `PASS`.
  17's text calls that comparison "an independent check of the expansion
  identity"; the article prints an editorial bracket there. The review
  confirms the delivered expansions by full sparse coefficient equality
  (7,502 and 8,256 monomials). In 18's `quartic_compiler.py` the
  serialized-export checker accepts a Boolean coordinate, a float
  coefficient and a negative variable index aliasing a legal coordinate,
  and the emitter accepts `True` as a bit width; the article qualifies
  18's sentence on `verify_export` with a bracket. The tested patches
  `positive_boundaries.patch` and `spectral_boundaries.patch` (in
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/spectral_repairs_060e08a07/`)
  apply with zero fuzz to the delivered files and change no residual,
  arity or recorded export. They are **not applied**: the shipped programs
  are the delivered bytes, and applying them to the prefixed copies (with
  the file names rewritten) is left to the owner of that tree. No theorem
  of Part XVII depends on the defects.
- **Batch 79, cluster J3 (manuscripts 19 and 20): shipped text that uses
  delivery names or names unshipped files.** `19-no-borrowed-firings-SOURCES.md`
  speaks of "this package", "the present paper" and "the article" (19's
  delivered text, now Section 3.19 and Sections M19.1–M19.14 and
  M19.A–M19.B of Part XVI) and names repository paths only.
  `20-compressed-queue-CLAIMS_AND_PROVENANCE.md` cites 20's theorems by its
  own numbers (mapped in "Delivered names and shipped names" above and in
  the article's conventions of Part XVIII), speaks of "the article" and
  "this manuscript", runs `python code/verify.py` and says that the PDF was
  compiled and rendered (the 28-page PDF is not shipped; it survives in
  `ef2fc7990`). `code/19-no-borrowed-firings-Makefile` runs
  `python verify.py` and `latexmk` on `article.tex`;
  `code/20-compressed-queue-Makefile` runs `python code/verify.py`,
  `python code/check_certificate.py data/…` and `latexmk` on
  `article.tex`. The scripts use delivery names in their imports and paths:
  19 (`sandpile_certificates`; `examples/`, `verification/`), 20
  (`queue_certificates`; `../data/`). Recorded data name delivery files:
  `data/20-compressed-queue-export_checks.json` names
  `example_quartic.json` and `infinite_growth_quartic.json`;
  `data/19-no-borrowed-firings-pdf_preflight.json` describes the delivered
  24-page PDF (not shipped), and no script writes it. 19's and 20's
  verification records give Python 3.13.5 of the deliveries' runs, and
  19's an elapsed time. The article prints the shipped names where 19 and
  20 name their files in prose and keeps their listings in the delivered
  layout with notes.
- **Batch 79, cluster J3: corrections and renamings in the printed text.**
  19's source breaks one subscript (a line break where `\rm` was meant, so
  its PDF prints `deg_madj`); the article prints `\deg_{\mathrm{adj}}(v)`
  with a bracket. 19's `m` (distinct unordered adjacent pairs) is printed
  as `E`, 16's letter, and its number of residuals `E` as `𝓡`; 20's
  `\code` (its radix value `𝖢`) is typeset with `\qval` and its `\Pow`
  with this report's (upright, not sans-serif). 19 says that "no existing
  repository file has been changed"; it describes its own delivery.
- **Batch 79, cluster J3: reviews of 19 and 20.** The review
  `review_boundary_sandpile_060e08a07.md` (`49bc4c654`) of the
  Hilbert's-tenth-problem research tree reruns 19's two entry points, finds
  no semantic or domain defect and supplies no patch; it notes that
  `Poly.evaluate` is an unrestricted algebraic evaluator, not a domain
  guard (the domain checks are in `Certificate.vector` and `evaluate`).
  The review `review_compressed_queue_aebfa.md` (`be1fc3f62`) reproduces
  two defects of 20's low-level constructors in `queue_certificates.py`
  (shipped as `code/20-compressed-queue-queue_certificates.py`): `Poly(terms)`
  (line 132) accepts noninteger coefficients, so for
  `Poly({(): float(2**60), (0,): -1.0})` the natural witness `2**60+1`
  gives the floating residual `0.0` and a directly constructed
  `Certificate` accepts, although the exact residual is −1; and
  `Action(read=['0'], write='0')` keeps the caller's mutable list, so
  changing it after compilation leaves the old certificate at zero. The
  compiler's own output is unaffected (integer coefficients; the export
  checker rejects floats). The tested patch
  `compressed_queue_exact_inputs.patch` (SHA-256 `ed4aa550…3501`, beside the
  review in
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`)
  is **not applied**: the shipped program is the delivered bytes, and
  applying it to the prefixed copy is left to the owner of that tree. All
  259,025 author checks pass with and without it. No theorem of Part XVIII
  depends on the defects. That tree's index once called Part XVI "a
  different report from the new quartic No Borrowed Firings archive"; that
  is true of the archives and their formats, but the theorems coincide, as
  the article's editorial note says.
- **Byte-identical duplicates within a manuscript** (checked with `cmp`):
  03's `test_results.json` and `test_run.txt`, `linear_test_results.json`
  and `linear_test_run.txt`, and `example-events.json` and
  `linear_example-events.json`; 05's `verification.json` and
  `verification_stdout.txt`; 10's `verification.json` and `test_output.txt`.
  Batch 78 shipped none: 14's two console copies and 15's
  `verification.txt` were left in the arrival commit. 15's `build.sh` is
  byte-identical to the build script of another batch-78 manuscript, placed
  in another report. Batch 79 shipped none of 17's and 18's in-archive
  copies (17's `data/test_log.txt`, 18's `validation/test_output.txt`).
  The console files are the scripts' printed JSON. Batch 79, cluster J3,
  shipped neither 19's `verification/latest_run.txt` (a copy of
  `results.txt`) nor 20's `data/verification_stdout.txt` (a copy of
  `verification.json`). No two files of different manuscripts are identical.
- **Machine-dependent fields.** 08's `receipt.json` and 10's
  `verification.json` (and hence `test_output.txt`) record an elapsed time,
  which a rerun changes; nothing else in the batch-62 records depends on
  the machine. In batch 78, 15's `verification.json` records a
  `runtime_seconds` field and 13's `verification.json` the Python version
  of its run (13's comparison mode ignores elapsed time). 16's three
  receipts record neither; its `BUILD_REPORT.json` records Python 3.13.5,
  SymPy 1.14.0 and pdfTeX 1.40.26 of the delivery's own run. In batch 79,
  17's `test_results.json` records an `elapsed_seconds` field, and 18's
  `artifact_checks.json` the Python version 3.13.5 of the delivery's run;
  19's `results.json` and `results.txt` record Python 3.13.5 and an
  `elapsed_seconds` field, and 20's `verification.json` Python 3.13.5.
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
  all are different files, told apart by their prefixes. 16 delivers yet
  another `verify.py` and `verification.json` (at its package root), and a
  `build.sh` different from 15's. In batch 79, 18's `code/quartic_compiler.py`
  and `code/run_tests.py` are not 02's `quartic_compiler.py` and
  `run_tests.py`, 17's `code/check_export.py` is not 15's, 17's
  `code/compiler.py` is not 06's, 17's `data/test_results.json` is not the
  `test_results.json` of 03, 06 or 12, and 18's `validation/results.json`
  is not the `results.json` of 04, 07 or 11; all are different files,
  told apart by their prefixes. In batch 79, cluster J3, 19 delivers yet
  another `verify.py` (at its package root) and 20 a `code/verify.py`, and
  20's `code/queue_certificates.py` is not 07's `code/queue_certificates.py`
  (shipped as `code/07-queue-causality-queue_certificates.py`); 20's
  `data/verification.json` and `data/example_quartic.json` are not the
  files of those names of 14, 15, 02 or 07; all are told apart by their
  prefixes.
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
  `repo-mrdp`, which now also record that pin. 16 inspected `928ea9701`
  through the GitHub connector (the project README, the MRDP guide and this
  report's `12-rle-routing-SOURCES.md`); its keys `repo-readme`,
  `repo-mrdp` and `matiyasevich` are merged into `repo-h10`, `repo-mrdp`
  and `mat2010`, and its `repo-routing` became the new entry
  `repo-rtsources`. Its statement that the project README reports
  75- and 87-operation figures is still true at the write. 17 and 18
  inspected `e58b724c2` (17's audit calls it the "main snapshot"; 18 read it
  through the GitHub connector), when this report had Parts I–XIV; their
  descriptions of its README are of that version. 17's keys `repo-h10`,
  `repo-canonical`, `jm1984`, `matiyasevich` and `hfg` are merged into
  `repo-h10`, `repo-cdc`, `jm1984`, `mat-scholarpedia` (17 dates the
  Scholarpedia article 2012) and `hfg2024` (17 cites the journal version);
  18's `RepoLean`, `RepoCertificates`, `LF`, `HFG`, `CCO` and `Mat` into
  `repo-trace`, `repo-cdc`, `lf2022`, `hfg2024`, `cco2024` and `mat2010`.
  19 inspected `e58b724c2`, the pin of 17 and 18, and 20 inspected
  `44983ed7e` through the GitHub connector (its claims ledger records the
  root tree `ecc70fbdb`); their descriptions of this report are of the
  versions with Parts I–XIV and I–XV. 19's keys `proveit-h10`,
  `proveit-mrdp`, `proveit-routing` and `cairns` are merged into
  `repo-h10`, `repo-mrdp`, `repo-rtsources` and `cairns`, and its `dhar`,
  Dhar's 1998 review, became the new entry `dhar1998` (not the 1990
  article `dhar1990`); 20's `repo`, `cook` and `woodsneary` are merged into
  `repo-cdc`, `cook` and `woods-neary`, and its `queueprior` (07's
  integration note) became the new entry `repo-qcint`.

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
- **Batch 78, cluster H3 (Part XVI).** Manuscript 16 arrived with 13–15
  but was placed separately (`41e7f1189`) and written after Part XV. It is
  printed as one Part in its own order (its Sections 2–16 and both
  appendices), appended after Part XV and before the appendices, so that
  no existing number changed; its title page, abstract, package statement
  and Section 1 are Section 3.16 (the Section 3 heading became "The sixteen
  manuscripts"). The Part opens with its source, its relation to the other
  Parts, its hypotheses and a conventions table (`L`, `n`, `m`, `E`, `u`,
  `d`, `r_v`, `D_k`, `K_vw`, `H`, `h`, `ρ`, `U(e,x)`, `π_S`, `c`, `T₀`,
  "without histories", "global halting"). It duplicates no printed
  theorem, so nothing is merged; the overlaps are pointers: its
  least-action lemma is credited to Fey–Levine–Peres with a pointer to
  `cdc:rt:lem:least`, its burning test to Dhar; its single-fold boundary is
  printed with a note that it is `cdc:bd:thm:universal` (a)⇔(b) for
  Cairns's relation; the finite search of its radius theorem is
  `cdc:bd:prop:nobound`'s, and its corollary repeats the predecessor-path
  argument of `cdc:of:prop:nocutoff`. A written note observes that its
  cubics are nonnegative on the real orthant, so Part XI's classification
  applies and sharpens its "cubic-degree boundary". Its eight questions
  (unnumbered subsections) are `question` environments at the end of the
  Part, cross-referenced to Part XIV's and to `cdc:q:repsize`,
  `cdc:q:verified`, `cdc:q:compression` and `cdc:q:ffprimitives`, not
  merged. Renamed: its pairing `π` is `π_S` (Part IX's `π` is
  `(a+b)^2+a`; `π_S = 2π_C`); its `\ind` prints with `\indset`, and
  `\Ccmp`, `\Poly`, `\diag` are written out. Where it names its files in
  prose the shipped names are printed. Bibliography keys mapped:
  `matiyasevich` → `mat2010`, `repo-readme` → `repo-h10`, `repo-mrdp` →
  `repo-mrdp` (both with 16's pin), `repo-routing` → the new entry
  `repo-rtsources`; `cairns` and `friedrich-levine` extended; `jarai` and
  `bayer-david` new; `dhar1990` and `fey-levine-peres` added by the write
  (78 distinct works in all). Dated `[write]` notes: after Part XIV's
  questions on infinite-background abelian computation (answered for
  undirected graphs) and on more general abelian processors (answered in
  part), after `cdc:q:restricted` (answered in part), in Part XIV's
  opening and after its Cairns remark, in Part IX, and inside Part XVI on
  the three constructor defects found by the research tree's review,
  whose patch is not applied.
- **Batch-78 reciprocal notes (cluster H3).** Six dated `[write]` notes of
  2 October 2026 point to the new report `quadratic-orthant-certificates`:
  in Part XI after the classification theorem and after the remark that
  follows the two-cut ranks theorem, after `cdc:q:acceleration` and
  `cdc:q:restricted`, and after Part XII's questions on canonical macro
  decompositions and on a small explicit fixed interpreter (see
  "Reciprocal notes (batch 78, cluster H3)" above). They cite that
  report's labels by name; no label was added, renamed or renumbered, and
  no printed text was changed.
- **Batch 79, cluster J1 (Part XVII).** Manuscripts 17 and 18 prove one
  theorem by one method in independent texts written from the same pin, so
  they are merged into one Part, appended after Part XVI and before the
  appendices; no existing number changed. Base: 17, because its scope is
  wider (the infinite horizon inside the verifier, `O(D³)` size, the
  minimum and the affine, triangular and fixed-phase applications, and the
  order-two boundary). The Part prints 17's Sections 2–12, then 18's
  Sections 2–12, a written comparison section (interfaces, sizes, horizons,
  exponentiation, boundaries, exports), both question lists, both
  conclusions and the four appendices; their title pages, abstracts,
  status statements and introductions are Sections 3.17–3.18 (the Section 3
  heading became "The eighteen manuscripts"). Second routes: 18's ladder,
  monotonicity identity, zero bound, capacity bound, endpoint theorem,
  power-assisted compiler and chart algorithm keep their statements and
  proofs, each after a bracket that names 17's result and says why the
  proof is kept (the bases are inputs); 18's oscillation theorem is
  printed as the residue-class strengthening of 17's rotation theorem, with
  notes both ways. Pointers, with no novelty claimed: the case of base 1
  is Part IV's tower and quartic, and 17's power-graph lemma re-proves
  Part IX's `cdc:pt:prop:exponential-boundary`; notes on 17's affine,
  triangular, first-failure and fixed-phase statements name the Part IV
  statements they generalize. Questions: 17's Q1 and 18's first question
  (the same saving at two levels) are one `question` environment printing
  both texts, with a note that 17's shared endpoints reach 18's `O(D³)`
  target for fixed bases; the other seventeen are printed in their lists
  and cross-referenced (17's Q4 and 18's question on positive algebraic
  eigenvalues ask the same thing). Renamed: no symbol; `\Pow`, `\wt` and
  `\Repart` were added; 17's `\pin` is printed literally, 18's `\repo` is
  replaced by the word ProveIt (it would clash with 03's `\repo`), its
  `\pathcode` prints as `\code` and its status boxes as the report's
  boxes. A conventions table lists the letters that differ or clash (`B`,
  `D`, `d`, `m`, `H`, `Q`, `K`, `L`, `M`, `T₀`, `π`; run/block and
  profile/chart are one notion each). Editorial brackets: 17's description
  of its two-point expansion check, and 18's of its export checker, citing
  the research tree's review, whose patches are not applied. Where 17 and
  18 name their own files in prose, the shipped names are printed.
  Bibliography: eleven of their seventeen items were merged into existing
  entries, six new entries (`repo-dpr`, `tiwari`, `how2019`, `cow2023`,
  `fggl2026`, `bkl-survey`) and the review (`repo-sprev`) were added (85
  distinct works in all). Dated `[write]` notes: in Part IV after the
  remark that follows `cdc:pt:thm:tower`, in Part IX after
  `cdc:pt:prop:exponential-boundary`, and at Source 02 of
  `cdc:q:compression` (answered in part, and re-scoped). The title-page
  lines naming the AI assistant are in the provenance appendix only.
- **Batch 79, cluster J3 (manuscript 19 inside Part XVI, Part XVIII).** 19
  proves Part XVI's main theorems again, independently and from a pin at
  which Part XVI did not exist, so it is not a new Part: it is printed
  inside Part XVI after 16's conclusion and before 16's appendices, as a
  marked second route in its own sections M19.1–M19.14 (M19.1 a written
  opening with the source paragraph, an editorial note on priority, the
  relation to other Parts, the setting and a conventions table; M19.`N` its
  Section `N`), and its two appendices follow 16's as M19.A–M19.B; these
  sections are numbered outside the report's sequence, so that no existing
  section, theorem, equation or table number moved. Its Section 1 and
  abstract are Section 3.19. Brackets before 19's least-action lemma,
  termination lemma, support theorem, rank theorem, halo theorem, radius
  theorem, cardinality corollary (first assertion), height theorem and
  coordinate bound name 16's statements; 19's proofs are kept as second
  routes. Its directed example and borrowed-firing example, the same as
  16's, are printed as delivered with brackets. A comparison paragraph
  explains why neither certificate improves the other (`11n+12E`
  witnesses and `12n+16E` quadratic residuals, projected `8n+12E`,
  against 16's cubics with `13n+12E` and `10n+6E` coordinates; degree two
  and a quartic against one cubic) and how Part XI applies. New, with
  credit: the residual system and gap, the gadgets, the field normal form,
  the unique codes, the completeness statement, the seed lemma and the
  code-length clause. 20 is appended as Part XVIII after Part XVII and
  before the appendices, in its own order (Sections 2–15 and Appendices
  A–B); its Section 1, abstract and status box are Section 3.20. Its
  resource algebra and minimum gadget (Part I) and its endpoint theorem
  (the one-queue case of Part VI's network theorem) carry brackets and are
  kept as second routes, with no novelty claimed. Questions: 19's nine and
  20's ten are labelled `question` environments (20's were numbered
  paragraphs), with lines naming the overlapping questions; none is merged.
  Renamed: 19's `m` is `E` and its residual count `E` is `𝓡`; 20's `\code`
  is `\qval`, its `\Pow` prints with this report's, and its label
  `sec:subtrates` is `cdc:cq:sec:substrates`. Corrected: 19's broken
  subscript. Bibliography: seven items merged, six new entries (`dhar1998`,
  `hkz`, `kocher`, `rankin`, `jez`, `repo-qcint`) and the two reviews
  (`repo-bsrev`, `repo-cqrev`) added (93 distinct works in all). Dated
  `[write]` notes: after Part XIV's question on infinite-background abelian
  computation (a second route), after `cdc:q:storage` (queue clause
  answered), after `cdc:q:acceleration` and `cdc:q:readcounts` (in part),
  and after 19's and 20's first questions (answered in part by the
  research tree's projections). The research tree's reviews of both
  archives are disclosed; the patch for 20 is not applied. The title-page
  lines naming the AI assistant are in the provenance appendix only.
- **Macros.** One `\code` (01's `\texttt{\detokenize{#1}}`); 02's `\_`
  escapes inside `\code` removed; the pin macros `\repoSHA` (01 and 07,
  different commits), `\repoCommit` (02) and `\reposha` (04) printed as
  literal identifiers; 04's unused `\repo` URL macro dropped (03's `\repo`
  kept); 06's unused `\word` dropped in favour of 07's. No mathematical
  symbol was renamed; letters that change meaning between Parts are listed
  in the conventions.
