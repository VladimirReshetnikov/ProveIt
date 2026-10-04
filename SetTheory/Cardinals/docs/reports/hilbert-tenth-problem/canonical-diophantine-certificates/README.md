# Canonical Diophantine certificates

**Witness-faithful polynomial representations of bounded discrete computation: resource algebra, trace classes, accelerators, polynomial trajectories, memory logs, queues, rewriting, heaps, self-assembly, priority pumping, reaction networks, routing networks, interaction combinators, abelian sandpiles, exponential trajectories, compressed queue traces, eager Tree Calculus, literal periodic sandpiles and fixed-arity sandpile certificates**

This is a research report dated 30 September 2026, with Parts XV–XIX dated 2 October
2026, Part XX dated 3 October 2026 and Part XXI dated 4 October 2026, merged from twenty-seven manuscripts: six of batch 60 (its manuscripts 01–06), the only manuscript
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
XVIII, and one more of batch 79 (its manuscript 17, cluster J2), numbered
21 here and added as Part XIX, and two of batch 83 (its manuscripts 07 and 08, cluster H1; the research
pipeline's Reports 35 and 36), numbered 22 and 23 here and merged into
Part XX, and four of batch 91 (its manuscripts 02, 04, 05 and 06, cluster
A; the pipeline's Reports 50, 52, 53 and 54), numbered 24–27 here and merged
into Part XXI. The base is manuscript 05, *Canonical
Trace Polytopes*; its `article.tex` was staged unprefixed and has been
replaced in place by the merged text. Manuscripts 01–23 prove the same
kind of theorem: an explicit integer polynomial whose natural zeros are in
bijection with the bounded executions (or trace classes of executions) of a
discrete substrate, with exactly one witness each; manuscripts 24–27 give up
the single witness for fixed arity (below); in 12 the execution is a
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
indefinitely. In 21 it is a terminating eager application in Barry Jay's
Tree Calculus, represented by its memoized proof DAG, for an externally
fixed bound on the number of distinct calls. In 22 the execution is the global stabilization of an ordinary
sandpile on `ℤ³` with a binary odometer in a fixed rectangular prism,
represented by its odometer, endpoint and canonical burning ranks; 22 also
makes the input loader of a universal periodic sandpile literal, for the
Neary–Woods machine `U₁₅`. In 23 the same certificate becomes exact over
the nonnegative reals. In 24–27 one ordinary positive integer codes a
stable periodic tile and a finite patch on `ℤ³`, and one polynomial of fixed
arity and degree 18 has a positive integer zero exactly when that sandpile
stabilizes globally with a binary odometer (24), fires a given target in a
prefix where every site fires at most once (25), fires it in some finite
legal sequence (26), or stabilizes globally after finitely many topplings
(27); every successful input has infinitely many witnesses. They continue the Lean
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
ChatGPT") and "Prepared for Vladimir Reshetnikov" (21; its PDF metadata
reads "Research report prepared for Vladimir Reshetnikov") and "Mathematical
research report" (22 and 23; their PDF metadata has an empty author
field), "Mathematical construction and reproducibility report" (24 and 25;
PDF metadata "Research report"), none (26; PDF metadata "Research report")
and "Report54" (27, also its PDF metadata). The article prints the batch-62, batch-78
and batch-79 author lines in neutral form and records these assistant names only in its
provenance appendix; the author lines of 12, 16 and 21–27 name no assistant.

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
| 21 | batch 79, manuscript 17 | `Eager_Tree_Calculus_Research_Package`, inner directory `eager-tree-certificates` (30-page PDF) | *Eager Tree Calculus: Exact quartic proof-DAG certificates, operational universality, and binary sharing compression* | none (Jay's upstream `baa877d91`) | `aebfa386e`; corrected code edition `4e270aa46` (batch 80, manuscript 01) | `a7ae02511`; corrected code `8a4e64732` | Section 3.21 (title-page box and status lines, abstract, §1); Part XIX (§§2–12, Appendices A–B) |
| 22 | batch 83, manuscript 07 | `Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package`, inner directory `Research_Report35` (23-page PDF) | *A Literal Periodic Sandpile Loader and Finite Prism Certificates: Ordinary three dimensional sandpiles from finite binary tapes* (Research Report 35) | `83befe707` | `3051d1446` | `216bd81e1` | Section 3.22 (abstract, §1; its Figure 1 at the opening of Part XX); Part XX (§§2–13) |
| 23 | batch 83, manuscript 08 | `Real_Exactness_of_Binary_Sandpile_Certificates_Package`, inner directory `Research_Report36` (13-page PDF) | *Real Orthant Exactness for the Binary Sandpile Cubic: A strengthening with unchanged variables degree summands and support* (Research Report 36) | `83befe707` (and `0055e1c4d` for *quadratic-orthant-certificates*) | `3051d1446` | `216bd81e1` | Section 3.23 (abstract, §1); Part XX (§§2–9, §4 as a pointer) |
| 24 (base of XXI) | batch 91, manuscript 02 | `A_Fixed_Arity_Integer_Certificate_for_Binary_Sandpile_Stabilization_Package`, inner directory `Research_Report50` (20-page PDF) | *A horizon free fixed arity integer certificate for binary sandpile stabilization* (Research Report 50) | `216bd81e1` | `0d7f51c44` | `b0a536b63` | Section 3.24 (abstract, §1); Part XXI (§§2–14, Appendices A–B) |
| 25 | batch 91, manuscript 04 | `Finite_Legal_Binary_Target_Firing_in_Periodic_Sandpiles_Package` (24-page PDF) | *Finite legal binary target firing in periodic three dimensional sandpiles* (Research Report 52) | none; inherits 24's `216bd81e1` through its bundled copy of 24 | `0d7f51c44` | `b0a536b63` | Section 3.25 (abstract, §1); Part XXI (§§2–5 as pointers to 24's §§3–6, §§6–17, Appendices A–B) |
| 26 | batch 91, manuscript 05 | `Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package` (17-page PDF) | *Ordinary repeated target firing: A fixed positive integer polynomial for raw sandpile inputs* (Report 53) | none (pins 25's files by hash) | `0d7f51c44` | `b0a536b63` | Section 3.26 (abstract, §1); Part XXI (§§2–12) |
| 27 | batch 91, manuscript 06 | `Unrestricted_Finite_Global_Sandpile_Stabilization_Package`, manuscript at `article/Report54.tex` (20-page PDF) | *Unrestricted Finite Global Sandpile Stabilization: An explicit fixed arity positive integer polynomial* (Report 54) | none (pins 22's loader and composition proofs, 24's and 26's notes by hash) | `0d7f51c44` | `b0a536b63` | Section 3.27 (abstract, scope paragraph, §1); Part XXI (§§2–14, Appendices A–B) |

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
formalization path, questions, conclusion and appendices; manuscript 21 is
Part XIX in its own order, closing with its reproducibility record, six
questions, closing remarks and appendices. Manuscripts 22 and 23 form Part XX: 22's Sections 2–13 in its own
order, then 23's Sections 2–9 (its Section 4, a further proof of 22's
certificate theorem, printed as a pointer), the research programme's review
and nine research questions. Manuscripts 24–27 form Part XXI: 24's
Sections 2–14 and appendices, 25's Sections 2–5 as pointers to 24 and its
Sections 6–17 and appendices, 26's Sections 2–12, 27's Sections 2–14 and
appendices, then the research programme's review, a section on six printed
passages of Cairns's paper, and 21 research questions. The Parts are: I Exact commutation and resource algebra;
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
infinite-loop certificates; XIX Eager Tree Calculus: exact quartic proof-DAG
certificates and a literal universal tree; XX Literal periodic sandpiles: an
explicit `U₁₅` loader, binary prism certificates and real-orthant
exactness; XXI Fixed-arity packed sandpile certificates: binary and
unrestricted global stabilization and target firing.

The full pins are `e8bb0931d67f80d9fce87a8cddb0f661ff19f956` (01–06),
`725d2ebb6909fe11a13a92354c0f47367a3cbbf5` (07),
`4e128356d0ef75308be8ed405d89aea2ffdb8a57` (08–11; 11 also names
`ccfb084adaa2f32e8d2738a25f82a00377fb3a8c`, a later commit it read on the
live branch) and `e18718e837d43e162252f9a314e8cb797fbd1a1f` (12), and `439c0a2d9c1052595f3de6a29c11511a24fb2e11` (13),
`6914ccca6685baf53b7a35f25efc89366c76ba74` (14) and
`928ea97017a25ebe56d240c84f27d2275d818c75` (15 and 16), and
`e58b724c25bd34533b7a5834cfcbe873dfa01288` (17, 18 and 19), and
`44983ed7ebfd545de55bfdb50e040c82f3d24295` (20); 21 names no ProveIt commit
and pins only Barry Jay's Tree Calculus repository at
`baa877d916eb640280ed2df7ef4385ecd5957d19`. 22 and 23 pin `83befe707f2840c2b53e0606701d8a2b28598e47`; 23 also names
`0055e1c4d5bd890878edf75a11fb412b9d15f6cc` as its observed revision of
the neighbouring report *quadratic-orthant-certificates*. 24 pins
`216bd81e116297214f443afddc2fc6252a7767a6` (the placement of 22 and 23);
25 states no ProveIt commit and inherits that pin through its bundled copy
of 24; 26 and 27 state none. The pin of 07 is the commit
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

Manuscript 21 was written on 2 October 2026 (its PDF was built at 14:30
Pacific time) without inspecting ProveIt: it names no ProveIt commit,
cites neither the repository nor this report, and pins its semantics to
Barry Jay's upstream commit `baa877d91`. It arrived in `aebfa386e`
(16:47), with the batch-79 manuscripts placed in the neighbouring reports
*signal-machine-collision-certificates* and *quadratic-orthant-certificates*,
and was placed by `a7ae02511` (17:39; batch 79, cluster J2), after Parts
XVII and XVIII had been placed. Its closing remarks allude, without a
reference, to "earlier canonical and scheduled SKI certificate
constructions"; these are Part VII's and Part V's, and a note says so.

A corrected code edition of manuscript 21,
`Eager_Tree_Calculus_Research_Package_corrected.zip` (598,941 bytes,
SHA-256 `2c053f50…0f3dbd`; the archive dates its correction 3 October
2026), arrived in `4e270aa46` (batch 80, manuscript 01) and was placed by
`8a4e64732` (batch 80, cluster K1). Its `CORRECTION.md` pins the batch-79
archive's SHA-256 and answers the research tree's review `3b5989da9`
(finding P3), which its authors read but did not execute. Its manuscript
source and PDF are byte-identical to the batch-79 delivery, so no printed
statement, proof, count or label changes; 50 of its 58 members are
byte-identical to batch-79 members. It replaced four placed files and
added two (see Files); the note "Added 2 October 2026 (batch 80):
corrected code edition" in the reproducibility section of Part XIX
(`cdc:et:sec:reproduce`) records it.

Manuscripts 22 and 23 were written on 3 October 2026 at `83befe707`
(10:38 Pacific time), when Parts I–XIX had been written, and arrived
together in `3051d1446` (14:47); they were placed by `216bd81e1` (15:46;
batch 83, cluster H1). They read this report's article at the pin (Part
XVI and manuscript 19, by line ranges and labels; 23 records that the
article blob is the same at `0055e1c4d`), and 22 read four files of this
report by blob (this README and the programs
`code/16-sandpile-sandpile_compact.py`, `code/16-sandpile-sandpile_spatial.py`
and `code/19-no-borrowed-firings-sandpile_certificates.py`), none executed;
23 also read Part VI of *quadratic-orthant-certificates* at `0055e1c4d`. No
file of this report changed between the pin and the placement. The
research programme reviewed both archives at 15:19 (`c120b34df`), before
the placement (see Disclosures). Both name "Research Report 35"/"36" and
call each other by those numbers: "Report 35" in 23's text is 22.

Manuscripts 24–27 are dated 4 October 2026, arrived together with twenty
other archives of batch 91 in `0d7f51c44` (10:16 Pacific time), were
reviewed by the research programme at 10:46 (`bc6e1a62c`, see Disclosures)
and were placed by `b0a536b63` (11:25; batch 91, cluster A), when Parts
I–XX had been written. They read no file of this report's article. 24 read
three of Part XX's shipped proofs at `216bd81e1`
(`22-literal-sandpiles-evidence-composition-PROOF.md`,
`22-literal-sandpiles-evidence-loader-LOADER-PROOF.md`,
`23-real-sandpiles-evidence-real-PROOF.md`, blobs `0f595718`, `a7f1a89b`,
`4eec3822`) and the research programme's Part XX review (blob `7a0c927b`);
25 bundles 24 whole; 26 pins five of 25's files; 27 pins two of those Part XX
proofs, 24's `PROOF.md` and 26's `ARCHITECTURE.md`. No file they pin changed
between their reading and this write. They call themselves and each other
"Report 50", "52", "53" and "54" (27 writes "Report50", "Report54"), and
Part XX's manuscripts "Report 35" and "36"; Research Report 51 (four-mass
timed charts) is a different subject, placed in *signal-machine-collision-certificates*
(`d750d98dd`).

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
- **21** for Barry Jay's original Tree Calculus with its five eager
  value-application rules: a coding bijection of tree values with `ℕ`
  (`code(F(a,b)) = (a+b)(a+b+1)+2b+2`) with quadratic constructor
  equations; additive call costs as a well-foundedness certificate for
  proof DAGs (a cyclic counterfeit is rejected with sum of squares 81);
  for every externally fixed `N ≥ 1` a quartic of exact degree four with
  `3N²+19N` natural witnesses and `23N+3` quadratic residuals whose zero
  set projects to the terminating applications with at most `N` distinct
  calls, every pointer lookup paid by one-hot selectors, with a literal
  ledger of `27N²+125N+8` gates; a canonical refinement with exactly one
  natural witness at the exact DAG size (`3N²+22N−3` witnesses, `31N`
  residuals for `N ≥ 2`); a strict bracket-abstraction compiler from weak
  left-to-right call-by-value lambda calculus that preserves and reflects
  termination; a counter-program frontend and a quoted-syntax
  interpreter giving a literal universal tree `U` of 175 constructor-DAG
  nodes (949 unshared) with an r.e.-complete halting domain, whose
  44,926,990,249–44,960,544,677-bit code is charged by 175 quadratic
  equations, never materialized; and, for a different fixed 108-node
  program `R` on unary inputs, `H_n = 562·2^n−468` unfolded calls with
  `O(n²)` witness bits and the exact canonical DAG size `D_n = 64n+113`
  (`n ≥ 2`; `D_0 = 44`, `D_1 = 179`), proved by a finite symbolic kernel
  proof, induction and a complete template-equality classification.

- **22** for the Neary–Woods machine `U₁₅` (fifteen states, two symbols,
  the pair `(J,1)` undefined) on finite two-sided binary tapes: one
  explicit stable periodic background `b: ℤ³ → {0,4,5}` with periods
  (1,303,671,936, 744,955,392, 1,955,501,604) and a 0/1 loader of at most
  `n+7` chips with coordinates at most `B(n+4)`, `B = 186,238,848`, such
  that `U₁₅` halts exactly when `b+δ` has finitely many topplings in total
  (one-shot: every site topples at most once, also on nonhalting inputs);
  built from a literal 34-state radius-two lazy automaton with 388,146
  positive rules and exact shutdown, a circuit of 3,879,975 primitives and
  5,819,945 edges with exact numbering, AND/OR/diode/wire/fork lattice
  primitives with one-shot confinement and all-port contracts, a
  seven-segment periodic router with every seam included, and a pointwise
  background-coefficient algorithm; a halting prism of at most
  `C(n+T+1)²` sites, `C = 5,426,111,451,172,075,939,316,367,360`, where the
  run halts after `T` transitions, and total toppling work between
  `(n+T+1)²/6` and `C(n+T+1)²`; for a fixed rectangular prism `P` and a
  natural input stable outside `P`, a cubic with `8V+6E+H` natural
  witnesses and `8V+7E+H` summands (`V`, `E`, `H` the vertices, internal
  edges and face-halo sites) with one natural zero exactly when the lattice
  stabilizes with a binary odometer supported in `P` (the binary case of
  16's compact cubic with its collar, a second route); a fractional real
  zero of that cubic; exact raw, expansion and evaluation ledgers with a
  bounded-record local collection and the coefficient bound
  `max(215V, 773,136)`; and a 43-chip example that halts after 75
  transitions.
- **23** replacing `f·g` by `f·(g+k+c)` in 22's cubic gives a polynomial
  (printed `Q^real`; 23 writes `Q_R`) whose nonnegative-real zero set equals
  22's natural zero set, empty or one point, for every fixed prism, with
  the same variables, summands, degree three, collected support and
  coefficient height (only `[fk]` and `[fc]` change, from 2 to 3;
  `[kc] = 86` at every vertex), by a real-exact edge gadget, binary activity
  and a finite predecessor-rigidity lemma; four ledger counts grow by `2V`
  in 22's convention; the real-orthant loader corollary; a fractional zero
  of 16's unrestricted compact certificate even with all pair penalties
  (so the binary hypothesis is essential); and a comparison variant with
  the same zeros and a larger height.
- **24** for one positive input `I` that decodes by seven Cantor pairings
  into `(p,q,r,T,d,e,f,D)` (a radix-32 tile with digits 0–5, periodic on
  `ℤ³`, and a radix-32 patch with digits 0–15 at the nonnegative box): an
  explicit `P ∈ ℤ[I, w₁, …, w₂₅₆₆]`, the sum of squares of 1,491 residuals,
  exact degree 18, 11,469 binary gates (4,518 ×, 3,933 +, 3,018 −; integer
  literals free), with a positive integer zero exactly when the input is
  valid and the sandpile has a finite legal global stabilization with a
  binary odometer; least action for a finite supersolution (a second route
  to Parts XVI and XX); the fifteen-equation Pell macro `POWER` (the macro of
  *periodic-turmite-first-revisits*, credited), binary containment by
  binomial parity (Jones–Matiyasevich masking, credited with its Lean
  formalization), a three-subset AND, stable digit planes, block spreading,
  a padded period-aligned prism with an unknown size, a zero shell for exact
  neighbours and a stable exterior, one carry-free balance; the exact
  leading part `48(pqrdef·t_{x0}t_{y0}t_{z0})²`; an overfiring example (the
  stream may be a supersolution, not the odometer).
- **25** the same input with three zigzag-coded target coordinates: a
  polynomial with 3,308 positive witnesses, 1,923 residuals, degree 18 and
  14,778 gates whose zeros exist exactly when a finite legal prefix in which
  every site fires at most once fires the target; time frames, one
  cumulative recurrence forcing an empty start and disjoint layers, exact
  neighbours in every frame, paid legality at new firings, the signed target;
  separators (mutual support, `[12,4]`, uniform five plus one chip with an
  extremal proof of non-stabilization). Its §§2–5 repeat 24's §§3–6.
- **26** the same eleven-field input, repeated firings allowed: 3,865
  witnesses, 2,251 residuals, degree 18, 17,275 gates; an existential radix
  `b = 32^L` with two paid conversions of the raw codes, a noncircular count
  recurrence (with a second, gcd uniqueness proof), legality with a
  half-radix slack guard against false carries (with the `[0,7]`
  counterexample to the relaxed guard), the target as an event, so even
  final counts are accepted; the exact residual degree histogram; and a
  conditional corollary: through Cairns's vertex/alarm simulation, with two
  readings of its initialization, the positive zero set is r.e.-complete,
  also on one fixed-tile slice.
- **27** the eight-field input, any finite odometer: 3,262 witnesses, 1,897
  residuals, degree 18, 14,571 gates for finite global stabilization (the
  empty sequence allowed); least action for general counts, precision
  `b = 32^L` with `16h = b` and count capacity `b/16−1`, two carry bounds;
  a non-power-of-two counterexample to spreading; four separators (a height-12
  singleton accepted here and rejected by 24, `[12,4]`, adjacent fives as a
  nonleast witness, uniform five plus one chip by a conservation identity);
  and a conditional corollary: through Part XX's loader and the Neary–Woods
  universality, finite global stabilization is r.e.-complete already for one
  fixed tile and binary patches, with four readings of Cairns's Sections 5–6.
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
The same tree's review of manuscript 21 (`review_eager_tree_aebfa.md`,
commit `3b5989da9`) found no theorem-level defect and one defect of the
evaluator's input boundary, with the tested repair
`eager_tree_exact_application_inputs.patch` beside that review. At the
batch-79 write the shipped `code/21-eager-tree-tree_kernel.py` was the
original; since batch 80 (placement `8a4e64732`) it is the archive's
corrected code edition (`Eager_Tree_Calculus_Research_Package_corrected.zip`,
arrival `4e270aa46`), whose own repair is equivalent to that patch. Do not
apply the patch to the shipped file: the repair is already present, and the
patch's hunk no longer applies. The same tree's correction audit
(`review_batch80_corrected.md`, commit `abfc0cb25`) confirms the repair and
that nothing mathematical changed.
The same tree reviewed the archives of 22 and 23 before placement
(`review_sandpile35_36_intake.md`, commit `c120b34df`): no defect and no
change requested, within a stated scope; it adds a shared-arithmetic
schedule and a real-algebraic limit of its own (see Disclosures).
It reviewed the archives of 24–27 before placement as well
(`review_new_sandpiles_0d7f51c44.md`, commit `bc6e1a62c`): a bounded text
and inert-source review that found no concrete defect and confirmed the
four DAGs' counts and exact degree 18 (see Disclosures and the article's
`cdc:sec:b91-review`).

## Files

```
article.tex                              the report, standalone LaTeX with an internal bibliography
article.pdf                              the compiled report, 742 pages
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
21-eager-tree-CORRECTION.md              manuscript 21's corrected code edition: the application-input repair, its scope and evidence, as delivered (batch 80)
21-eager-tree-VERIFICATION.md            manuscript 21's verification scope: evidence by type, deliberate limits, portability
22-literal-sandpiles-INTEGRITY.md        manuscript 22's release trust boundary, replay and archive behaviour (delivery names)
22-literal-sandpiles-evidence-composition-PROOF.md  the binary prism certificate proof and ledger of 22's composition packet (= 23's approved_base PROOF.md)
22-literal-sandpiles-evidence-composition-README.md  guide to 22's composition packet
22-literal-sandpiles-evidence-composition-review-INDEPENDENT_AUDIT.md  independent audit of the binary certificate (natural witnesses, fixed prism)
22-literal-sandpiles-evidence-loader-INDEPENDENT-AUDIT.md  independent adversarial audit of the loader (PASS), with the files it hashed
22-literal-sandpiles-evidence-loader-LOADER-PROOF.md  the loader proof: automaton, primitives, router, composition, prism
22-literal-sandpiles-evidence-loader-README.md  guide to 22's loader packet
22-literal-sandpiles-evidence-loader-ca-SEMANTICS_AND_BOUNDS.md  the lazy automaton: data, rule families, shutdown, bounds
22-literal-sandpiles-evidence-loader-gates-GATE-PROOF.md  the lattice primitives and their all-port contracts
22-literal-sandpiles-evidence-loader-geometry-periodic_router_proof.md  the periodic router and its separation proof
23-real-sandpiles-INTEGRITY.md           manuscript 23's release authentication boundary and replay contract (delivery names)
23-real-sandpiles-evidence-real-PROOF.md  the real-orthant exactness proof
23-real-sandpiles-evidence-real-PUBLIC_PRIOR_ART.md  23's pins, the lines and labels it read, and its claim boundary
23-real-sandpiles-evidence-real-README.md  guide to 23's real-exactness packet
23-real-sandpiles-evidence-real-independent_math_review.md  independent review of 23's real-zero argument, support and ledger (pass)
24-fixed-arity-audit_replay-README.md    guide to 24's portable replay of its independent audit (delivery names)
24-fixed-arity-independent_audit-AUDIT.md  24's independent audit: exact reconstruction of every residual, interface and witness; PASS relative to the Pell theorems
24-fixed-arity-science-PROOF.md          24's construction proof (frozen; says the audit is "in progress")
24-fixed-arity-science-README.md         guide to 24's science packet (frozen; says the audit is "in progress")
24-fixed-arity-science-SCOPE.md          24's research scope and non-claims
24-fixed-arity-science-periodic-input-periodic_packing_lemma.md  periodic input, padding and exact six-neighbour packing; cites the programme's Part XX review by blob
24-fixed-arity-science-stream-products-AND_SPREAD_PROOF.md  the paid AND and block-spreading proofs
24-fixed-arity-science-stream-products-MASK_SUBSET_PROOF.md  the paid binary-containment (Sub) proof
24-fixed-arity-verification-MANUSCRIPT_REVIEW.md  independent review of 24's manuscript
25-binary-target-audit_replay-README.md  guide to 25's portable audit replay (delivery names)
25-binary-target-independent_audit-AUDIT.md  25's independent audit (PASS relative to the Pell theorems)
25-binary-target-independent_audit-SEMANTICS.md  25's independent semantic review of the binary tableau
25-binary-target-science-ARCHITECTURE.md  25's construction proof (frozen; says it is "not yet independently audited")
25-binary-target-science-SOURCE_NOTES.md  25's literal source and evidence notes (frozen; "independent review is pending")
25-binary-target-verification-manuscript_review-MANUSCRIPT_REVIEW.md  independent review of 25's manuscript
26-repeated-target-audit_replay-PORTABILITY_REPORT.md  26's replay portability record
26-repeated-target-audit_replay-README.md  guide to 26's portable audit replay (delivery names)
26-repeated-target-dependencies-NOTICE.md  the pinned mathlib source and its licence (files not shipped)
26-repeated-target-independent_audit-AUDIT.md  26's independent adversarial audit, with the corollary boundary
26-repeated-target-independent_audit-semantic-challenge-report.md  independent semantic challenge of the repeated-firing tableau
26-repeated-target-science-ARCHITECTURE.md  26's construction proof
26-repeated-target-science-SOURCE_NOTES.md  26's literal source, ledger and evidence notes
26-repeated-target-science-recurrence-review-REVIEW.md  independent recurrence and legality review
26-repeated-target-science-source-review-REVIEW.md  independent exact-source review
26-repeated-target-universality-PRIMARY_SOURCE.md  locators and two short quotations of Cairns's paper
26-repeated-target-universality-REVIEW.md  the raw-interface hardness review behind 26's corollary
26-repeated-target-verification-manuscript_audit-AUDIT.md  independent audit of 26's manuscript
27-unrestricted-stab-audit_replay-PORTABILITY_REPORT.md  27's replay portability record
27-unrestricted-stab-audit_replay-README.md  guide to 27's portable audit replay (delivery names)
27-unrestricted-stab-hardness-interface-CORRECTIONS.md  27's four readings of Cairns's Sections 5–6 (checked in the article's cdc:sec:b91-cairns)
27-unrestricted-stab-hardness-interface-POTENTIAL_COROLLARY.md  statement of the conditional corollary
27-unrestricted-stab-hardness-interface-PRIMARY_LOCATORS.md  locators in Cairns's paper and verification record
27-unrestricted-stab-hardness-interface-REVIEW.md  the exact physical-interface hardness review
27-unrestricted-stab-independent_audit-AUDIT.md  27's root-assigned adversarial audit (PASS relative to the Pell theorems)
27-unrestricted-stab-science-PROOF.md    27's construction proof
27-unrestricted-stab-science-README.md   guide to 27's science packet
27-unrestricted-stab-science-math-audit-AUDIT.md  independent mathematical audit
27-unrestricted-stab-science-source-audit-SOURCE_AUDIT.md  independent exact source audit
27-unrestricted-stab-verification-manuscript-review-AUDIT.md  independent review of 27's manuscript

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
code/21-eager-tree-analyze_growth.py  complete unary-template equality classification and the exact all-n DAG size; writes exact_growth_receipt.json
code/21-eager-tree-audit_exact_count.py  independent direct evaluations and whole-call-set comparisons; writes audit_exact_count_receipt.json
code/21-eager-tree-build_pdf.py  manuscript 21's PDF builder: three pdflatex passes on eager-tree-certificates.tex, which is not shipped (do not use it)
code/21-eager-tree-canonical.py  canonical baseline with explicit root-distinctness equations; writes canonical_identity.json and canonical_receipt.json
code/21-eager-tree-canonical_overlay_audit.py  optional SymPy checks of the canonical overlay; writes canonical_overlay_receipt.json
code/21-eager-tree-canonical_projected.py  the preferred canonical polynomial (31N residuals); writes canonical_projected_identity.json and its receipt
code/21-eager-tree-canonical_projected_audit.py  optional SymPy checks of the canonical polynomial and its uniqueness regressions; writes its receipt
code/21-eager-tree-constant_bit_bound.py  integer-only bit interval of code(U); writes constant_bit_bound.json
code/21-eager-tree-counter_source.py  counter-table-to-CBV source constructor and four checked examples; writes counter_source_receipt.json
code/21-eager-tree-eager_compiler.py  strict bracket compiler, CEK evaluator, quoted-syntax interpreter, universal tree; writes the universal artifacts
code/21-eager-tree-export_shared_macro.py  exports the finite symbolic kernel proofs of R (shared_symbolic_proofs.json)
code/21-eager-tree-independent_audit.py  independent kernel semantics, residual expansion and counterexample checks; writes independent_receipt.json
code/21-eager-tree-independent_compiler_audit.py  independent de Bruijn substitution semantics and tree context reduction; writes its receipt
code/21-eager-tree-independent_growth_audit.py  independent all-index structural equality classification; writes independent_growth_receipt.json
code/21-eager-tree-independent_shared_audit.py  independent symbolic-proof checking, graph composition and mutation rejection; writes its receipt
code/21-eager-tree-reproduce.py  manuscript 21's replay driver (batch-80 corrected edition): runs the 17 (with --symbolic 20) stages in code/, the regression suite first, and writes replay-output/
code/21-eager-tree-shared_compression.py  generator and finite structural experiments for R; writes shared_compression_program.json and its receipt
code/21-eager-tree-symbolic_audit.py  optional SymPy expansion of the small-N residual systems (exact degree four); writes symbolic_receipt.json
code/21-eager-tree-test_application_domain.py  regression suite for exact-natural application inputs (batch 80; 5 groups, 303 scenarios; --kernel tests another kernel; writes no file)
code/21-eager-tree-tree_kernel.py  (batch-80 corrected edition) coding, memoized eager kernel, structural evaluator, polynomial circuit and gate counter; writes the two fixtures and receipt.json
code/21-eager-tree-verify_packet_assumptions.py  kernel-proof validity and full reachability for the exact-growth identification; writes its receipt
code/21-eager-tree-verify_shared_macro.py  standalone symbolic-row, acyclicity, program-identity and bit-bound verifier (prints JSON; writes no file)
code/22-literal-sandpiles-archive_regression.py  22's archive safe-inventory regression (release tool; needs the delivered tree)
code/22-literal-sandpiles-archive_release.py  22's deterministic ZIP builder and checker (release tool)
code/22-literal-sandpiles-build_pdf.py   22's PDF rebuild of the unshipped Research_Report35.tex (do not run here)
code/22-literal-sandpiles-evidence-composition-literal_composition.py  literal adapter from loader coefficients to prism certificates (prints its receipt)
code/22-literal-sandpiles-evidence-composition-prism_certificate.py  the binary prism certificate compiler (= 23's approved_base compiler)
code/22-literal-sandpiles-evidence-composition-review-audit_adapter.py  independent audit of the adapter (prints its receipt)
code/22-literal-sandpiles-evidence-composition-review-audit_crosscheck.py  independent cross-check of compiler and ledgers (prints)
code/22-literal-sandpiles-evidence-composition-review-audit_independent.py  independent direct model of the certificate (prints)
code/22-literal-sandpiles-evidence-composition-review-audit_polynomial.py  independent polynomial expansion and ledger (prints)
code/22-literal-sandpiles-evidence-composition-review-audit_streaming.py  independent local-versus-global collection audit (prints)
code/22-literal-sandpiles-evidence-composition-test_prism_certificate.py  the composition test suite (prints its receipt)
code/22-literal-sandpiles-evidence-loader-ca-lazy_u15.py  the 34-state lazy automaton and its rule-stream writer
code/22-literal-sandpiles-evidence-loader-ca-test_lazy_u15.py  automaton tests against the machine table and the rule stream; rewrites its receipt
code/22-literal-sandpiles-evidence-loader-compiler-literal_loader.py  circuit numbering, port incidence and pointwise coefficients; --audit rewrites the circuit manifest
code/22-literal-sandpiles-evidence-loader-compiler-make_example.py  the 43-chip worked example; rewrites its receipt
code/22-literal-sandpiles-evidence-loader-compiler-test_coefficients.py  coefficient-suite tests; rewrites its receipt
code/22-literal-sandpiles-evidence-loader-gates-check_gates.py  all-port primitive checks by least closure and firing orders; rewrites its receipt
code/22-literal-sandpiles-evidence-loader-geometry-periodic_router.py  the periodic router and its finite tori (--output)
code/22-literal-sandpiles-evidence-loader-verify_bundle.py  the loader packet's own bundle check (delivered layout)
code/22-literal-sandpiles-seal_release.py  22's maintainer seal tool (do not run)
code/22-literal-sandpiles-tamper_regression.py  22's tamper regression (release tool; POSIX modes)
code/22-literal-sandpiles-verify_release.py  22's release verifier and replay wrapper (needs the delivered tree and POSIX modes)
code/23-real-sandpiles-archive_regression.py  23's archive regression (release tool)
code/23-real-sandpiles-archive_release.py  23's deterministic ZIP builder and checker (release tool)
code/23-real-sandpiles-build_pdf.py      23's PDF rebuild of the unshipped Research_Report36.tex (do not run here)
code/23-real-sandpiles-evidence-real-exact_checks.py  exact symbolic and LP checks of the real-exact certificate (SymPy 1.14.0; --output)
code/23-real-sandpiles-evidence-real-freeze_packet.py  23's packet freezer (hashes its files, approved_base included)
code/23-real-sandpiles-evidence-real-independent_coefficient_ledger_checks.py  independent coefficient and ledger audit, 54 cases (--output)
code/23-real-sandpiles-evidence-real-real_certificate.py  the real-exact compiler (subclasses approved_base/prism_certificate.py)
code/23-real-sandpiles-seal_release.py   23's maintainer seal tool (do not run)
code/23-real-sandpiles-tamper_regression.py  23's tamper regression (release tool; POSIX modes)
code/23-real-sandpiles-verify_release.py  23's release verifier and replay wrapper (needs the delivered tree and POSIX modes)
code/24-fixed-arity-archive_release.py   24's deterministic ZIP builder (release tool; needs the delivered tree)
code/24-fixed-arity-audit_replay-replay_independent_audit.py  path-only replay adapter for 24's frozen independent checker (delivered layout)
code/24-fixed-arity-audit_replay-test_replay_runner.py  16 safety and relocation tests of that adapter
code/24-fixed-arity-build_pdf.py         24's PDF rebuild of the unshipped Research_Report50.tex (do not run here)
code/24-fixed-arity-independent_audit-independent_check.py  24's independent exact-polynomial checker (reads the DAG as data)
code/24-fixed-arity-science-build_certificate.py  24's fixed-shape DAG builder; writes evidence/polynomial-dag.json and its receipt
code/24-fixed-arity-science-check_exact_degree.py  univariate specialization proving the degree lower bound 18
code/24-fixed-arity-science-check_source.py  24's own read-only checks of the emitted source
code/24-fixed-arity-science-periodic-input-check_periodic_packing.py  finite checks of the periodic-packing lemma
code/24-fixed-arity-science-stream-products-verify_and_spread.py  finite AND and spreading checks
code/24-fixed-arity-science-stream-products-verify_mask_subset.py  finite Sub checks
code/24-fixed-arity-verify_release.py    24's release verifier and replay wrapper (needs the delivered tree and POSIX modes)
code/25-binary-target-archive_release.py  25's deterministic ZIP builder (release tool)
code/25-binary-target-audit_replay-replay_audits.py  path-only replay of 25's two frozen checkers (delivered layout)
code/25-binary-target-audit_replay-test_replay_adapter.py  relocation and refusal tests of that adapter
code/25-binary-target-build_pdf.py       25's PDF rebuild of the unshipped Research_Report52.tex (do not run here)
code/25-binary-target-independent_audit-independent_check.py  25's independent symbolic and finite checker
code/25-binary-target-independent_audit-semantics_check.py  25's independent semantic probes
code/25-binary-target-science-build_target_certificate.py  25's fixed-shape DAG builder
code/25-binary-target-science-check_target_certificate.py  25's own checks of the DAG
code/25-binary-target-test_release_tools.py  tests of 25's release tools (POSIX modes)
code/25-binary-target-verification-manuscript_review-check_manuscript.py  manuscript and source consistency checks
code/25-binary-target-verify_release.py  25's release verifier (needs the delivered tree and POSIX modes)
code/26-repeated-target-audit_replay-replay_audit.py  path-only replay of 26's three frozen auditors (POSIX paths; see Rerunning)
code/26-repeated-target-independent_audit-audit_arithmetic.py  independent arithmetic checks
code/26-repeated-target-independent_audit-audit_source.py  independent exact source auditor
code/26-repeated-target-independent_audit-freeze_audit.py  the audit's freeze tool
code/26-repeated-target-independent_audit-semantic-challenge-independent_checks.py  independent semantic challenge checks
code/26-repeated-target-release.py       26's release tool: integrity, PDF build, ZIP (delivered tree)
code/26-repeated-target-science-build_repeated_certificate.py  26's DAG builder; regenerates the unshipped polynomial-dag.json byte for byte
code/26-repeated-target-science-check_repeated_semantics.py  26's finite semantic probes
code/26-repeated-target-science-finalize_manifest.py  26's packet manifest tool
code/26-repeated-target-science-recurrence-review-check_recurrence.py  independent recurrence probes
code/26-repeated-target-science-source-review-check_source.py  independent exact source review (hard-coded /workspace/shared paths; does not run as shipped)
code/26-repeated-target-verification-check_layout.py  PDF layout checks (Poppler)
code/26-repeated-target-verification-check_release_tools.py  tests of the release tool
code/26-repeated-target-verification-manuscript_audit-check_literal_dag.py  independent DAG recount and degree check
code/27-unrestricted-stab-audit_replay-replay_audit.py  path-only replay of 27's three frozen auditors (POSIX paths; see Rerunning)
code/27-unrestricted-stab-independent_audit-challenge_checker.py  mutation challenges of the audit's checker
code/27-unrestricted-stab-independent_audit-check_exact.py  independent exact source checker
code/27-unrestricted-stab-independent_audit-check_semantics_fresh.py  independent semantic challenges
code/27-unrestricted-stab-release.py     27's release utility (delivered tree, POSIX modes)
code/27-unrestricted-stab-science-build_stabilization.py  27's DAG builder
code/27-unrestricted-stab-science-check_semantics.py  27's finite semantic regressions
code/27-unrestricted-stab-science-finalize_manifest.py  27's packet manifest tool
code/27-unrestricted-stab-science-math-audit-check_math.py  finite checks of the mathematical audit
code/27-unrestricted-stab-science-source-audit-audit_source.py  independent source-to-equations audit
code/27-unrestricted-stab-science-source-audit-run_replay_checks.py  replay and mutation runner of the source audit
code/27-unrestricted-stab-verification-check_release_guards.py  negative tests of the release utility
code/27-unrestricted-stab-verification-manuscript-review-check_manuscript_evidence.py  manuscript ledger, degree and pin checks

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
data/21-eager-tree-audit_exact_count_receipt.json  recorded run of audit_exact_count.py (whole call-set comparisons)
data/21-eager-tree-canonical_identity.json  canonical-baseline witness of the identity example
data/21-eager-tree-canonical_overlay_receipt.json  recorded run of canonical_overlay_audit.py
data/21-eager-tree-canonical_projected_audit_receipt.json  recorded run of canonical_projected_audit.py
data/21-eager-tree-canonical_projected_identity.json  the unique natural witness of the canonical N = 4 identity certificate (133 witnesses, 124 residuals)
data/21-eager-tree-canonical_projected_receipt.json  recorded run of canonical_projected.py (184 single-coordinate mutations rejected)
data/21-eager-tree-canonical_receipt.json  recorded run of canonical.py
data/21-eager-tree-constant_bit_bound.json  bit interval 44,926,990,249–44,960,544,677 of code(U), with the SHA-256 of its input table
data/21-eager-tree-counter_source_receipt.json  recorded run of counter_source.py
data/21-eager-tree-cyclic_counterfeit.json  the false locally matching proof of omega omega, rejected by its height residual (sum of squares 81)
data/21-eager-tree-eager_compiler_receipt.json  recorded run of eager_compiler.py
data/21-eager-tree-exact_growth_receipt.json  the complete template-equality classification behind D_n = 64n+113
data/21-eager-tree-identity_certificate.json  full N = 4 scalar certificate of E(10,10) = 10 (124 witnesses, 95 residuals)
data/21-eager-tree-independent_compiler_receipt.json  recorded run of independent_compiler_audit.py (707 compiled normal forms)
data/21-eager-tree-independent_growth_receipt.json  recorded run of independent_growth_audit.py
data/21-eager-tree-independent_receipt.json  recorded run of independent_audit.py (batch 80: kernel hash refreshed)
data/21-eager-tree-independent_shared_receipt.json  recorded run of independent_shared_audit.py
data/21-eager-tree-literal_universal_tree.json  the 175-node constructor table of U (Appendix A)
data/21-eager-tree-literal_universal_tree.sexpr  the unshared 949-node expression of U
data/21-eager-tree-packet_assumptions_receipt.json  recorded run of verify_packet_assumptions.py, with SHA-256 of the two R files
data/21-eager-tree-receipt.json  recorded run of tree_kernel.py (10,000 round trips, 768 input pairs; batch 80: kernel hash refreshed)
data/21-eager-tree-requirements-optional.txt  sympy>=1.13,<2, for the optional symbolic stages only
data/21-eager-tree-shared_compression_program.json  the 108-node constructor table of R (Appendix A)
data/21-eager-tree-shared_compression_receipt.json  recorded run of shared_compression.py (finite structural experiments for R)
data/21-eager-tree-shared_symbolic_proofs.json  two base proofs and the schematic step proof of R (44, 179 and 150 rows), with affine costs
data/21-eager-tree-sources.json  the pinned upstream sources (Jay's commit baa877d91, four files) and Dal Lago-Martini
data/21-eager-tree-symbolic_receipt.json  recorded run of symbolic_audit.py
data/21-eager-tree-universal_code_circuit.json  the 175 constant-code residuals of U
data/21-eager-tree-universal_lambda_source.json  the finite source lambda AST of U
data/22-literal-sandpiles-evidence-composition-FROZEN-INPUTS.json  status, layout and loader pin of the composition packet, with file hashes
data/22-literal-sandpiles-evidence-composition-PROVENANCE.json  the four repository files 22 read at 83befe707, by blob
data/22-literal-sandpiles-evidence-composition-VALIDATION.json  the composition packet's validation record
data/22-literal-sandpiles-evidence-composition-example_hypothetical_bound.json  receipt of literal_composition.py
data/22-literal-sandpiles-evidence-composition-review-AUDIT-FROZEN.json  status, scope and hashes of the composition audit
data/22-literal-sandpiles-evidence-composition-review-REPLAY.json  the composition audit's replay record
data/22-literal-sandpiles-evidence-composition-review-audit_adapter_results.json  receipt of audit_adapter.py
data/22-literal-sandpiles-evidence-composition-review-audit_crosscheck_results.json  receipt of audit_crosscheck.py
data/22-literal-sandpiles-evidence-composition-review-audit_independent_results.json  receipt of audit_independent.py
data/22-literal-sandpiles-evidence-composition-review-audit_ledger.json  receipt of audit_polynomial.py
data/22-literal-sandpiles-evidence-composition-review-audit_streaming_results.json  receipt of audit_streaming.py
data/22-literal-sandpiles-evidence-composition-verification.json  receipt of test_prism_certificate.py
data/22-literal-sandpiles-evidence-loader-PROVENANCE.json  the loader's sources, pinned machine data and repository obligation
data/22-literal-sandpiles-evidence-loader-VALIDATION.json  the loader packet's validation record
data/22-literal-sandpiles-evidence-loader-ca-manifest.json  the automaton manifest (rule counts, stream hash)
data/22-literal-sandpiles-evidence-loader-ca-rules.jsonl.gz  all 388,146 rules as gzip-compressed JSON lines (1,870,861 bytes; see below)
data/22-literal-sandpiles-evidence-loader-ca-verification.json  receipt of test_lazy_u15.py
data/22-literal-sandpiles-evidence-loader-compiler-circuit_manifest.json  receipt of literal_loader.py --audit (5,819,945 edges)
data/22-literal-sandpiles-evidence-loader-compiler-coefficient_checks.json  receipt of test_coefficients.py
data/22-literal-sandpiles-evidence-loader-compiler-worked_example.json  the 43-chip example with every seed (receipt of make_example.py)
data/22-literal-sandpiles-evidence-loader-gates-gate_receipt.json  receipt of check_gates.py
data/22-literal-sandpiles-evidence-loader-geometry-router_checks.json  receipt of periodic_router.py
data/22-literal-sandpiles-verification-document-qa.json  22's document quality record
data/22-literal-sandpiles-verification-expected-receipts.json  the 17 expected receipts and records of 22's replay
data/22-literal-sandpiles-verification-primary-references.json  Cairns and Neary-Woods, with verified publication metadata
data/22-literal-sandpiles-verification-replay-plan.json  22's 13 producers: working directory, arguments, receipt, capture
data/22-literal-sandpiles-verification-root-certificate-review.json  22's certificate review receipt
data/22-literal-sandpiles-verification-root-loader-review.json  22's loader review receipt
data/22-literal-sandpiles-verification-source-lineage.json  original-to-packaged identity of 60 evidence files (delivery paths)
data/23-real-sandpiles-evidence-real-ENVIRONMENT.json  23's environment and packet record: base hashes, branch count, LP scope
data/23-real-sandpiles-evidence-real-independent_coefficient_ledger_receipt.json  receipt of the 54-case ledger audit
data/23-real-sandpiles-evidence-real-report35_integrity_check.txt  record that 22's 78 release checksums pass
data/23-real-sandpiles-evidence-real-verification.json  receipt of exact_checks.py (18 expansions, 2,733 mutations, 1,863 branches)
data/23-real-sandpiles-verification-article-quality.json  23's article quality record
data/23-real-sandpiles-verification-expected-receipts.json  the four expected receipts of 23's replay (normal and optimized)
data/23-real-sandpiles-verification-pdf-rebuild.json  23's PDF rebuild record
data/23-real-sandpiles-verification-release-review.json  23's release review, including the LP scope statement
data/23-real-sandpiles-verification-replay-plan.json  23's two producers
data/23-real-sandpiles-verification-source-lineage.json  original-to-packaged identity of 18 evidence files (delivery paths)
data/23-real-sandpiles-verification-tooling-tests.json  23's tooling test record
data/24-fixed-arity-MANIFEST.json        24's release manifest: path, SHA-256, size and mode of every other release file (delivery paths)
data/24-fixed-arity-audit_replay-evidence-replay-runner-receipt.json  receipt of the replay adapter
data/24-fixed-arity-audit_replay-evidence-replay-scientific-receipt.json  receipt of the independent checker (= the audit's own receipt and log, not shipped again)
data/24-fixed-arity-audit_replay-evidence-test-results.json  receipt of test_replay_runner.py
data/24-fixed-arity-audit_replay-replay-pin-manifest.json  pins of the replay packet
data/24-fixed-arity-independent_audit-audit-manifest.json  the audit's file manifest
data/24-fixed-arity-science-evidence-build-receipt.json  receipt of build_certificate.py
data/24-fixed-arity-science-evidence-exact-degree-receipt.json  receipt of check_exact_degree.py
data/24-fixed-arity-science-evidence-polynomial-dag.json  24's polynomial as a literal DAG (661,089 bytes; SHA-256 2e240309…)
data/24-fixed-arity-science-evidence-source-check-receipt.json  receipt of check_source.py
data/24-fixed-arity-science-periodic-input-verification_receipt.json  receipt of check_periodic_packing.py
data/24-fixed-arity-science-sources-source-pins.json  pins of the four unshipped source texts (mathlib Pell, three Part XX proofs)
data/24-fixed-arity-science-stream-products-and-spread-check-receipt.json  receipt of verify_and_spread.py
data/24-fixed-arity-science-stream-products-mask-check-receipt.json  receipt of verify_mask_subset.py
data/24-fixed-arity-verification-coordinating-review.json  coordinating review record, with the title-only amendment
data/24-fixed-arity-verification-final-latex.log  LaTeX log of the delivered PDF build
data/24-fixed-arity-verification-helper-path-guards.json  path-guard tests of the release helpers
data/24-fixed-arity-verification-manuscript-review-receipt.json  receipt of the manuscript review
data/24-fixed-arity-verification-pdf-reproduction.json  PDF rebuild record
data/24-fixed-arity-verification-reference-check.json  bibliography reference check
data/24-fixed-arity-verification-release-readiness.json  release readiness record
data/24-fixed-arity-verification-science-freeze.json  freeze record of the science and audit packets (delivery paths)
data/24-fixed-arity-verification-science-preservation.json  preservation hashes of the science files
data/24-fixed-arity-verification-toolchain.json  toolchain record
data/24-fixed-arity-verification-visual-review.json  all-page visual review record
data/25-binary-target-MANIFEST.json      25's release manifest (delivery paths, including baseline_report50/)
data/25-binary-target-audit_replay-evidence-audit-receipt.json  receipt of the independent checker (= the audit's own receipt and logs, not shipped again)
data/25-binary-target-audit_replay-evidence-replay-receipt.json  receipt of the replay adapter
data/25-binary-target-audit_replay-evidence-semantics-receipt.json  receipt of the semantic checker
data/25-binary-target-audit_replay-evidence-test-results.json  receipt of test_replay_adapter.py
data/25-binary-target-audit_replay-replay-pin-manifest.json  pins of the replay packet
data/25-binary-target-independent_audit-audit-manifest.json  the audit's file manifest and verdict
data/25-binary-target-science-evidence-build-receipt.json  receipt of build_target_certificate.py
data/25-binary-target-science-evidence-check-receipt.json  receipt of check_target_certificate.py
data/25-binary-target-science-evidence-polynomial-dag.json  25's polynomial as a literal DAG (886,543 bytes; SHA-256 352b6dd9…)
data/25-binary-target-verification-manuscript_review-review-summary.json  manuscript review summary
data/25-binary-target-verification-manuscript_review-text-check-receipt.json  receipt of check_manuscript.py
data/25-binary-target-verification-manuscript_review-visual-review-receipt.json  visual review receipt
data/25-binary-target-verification-pdf-build.json  PDF build record
data/25-binary-target-verification-pdf-layout-checks.json  PDF layout checks
data/25-binary-target-verification-release-tool-tests.json  receipt of test_release_tools.py
data/25-binary-target-verification-source-preservation.json  preservation hashes of the packets
data/26-repeated-target-MANIFEST.json    26's release manifest (delivery paths)
data/26-repeated-target-audit_replay-independent-review-verification.json  replay verification record
data/26-repeated-target-audit_replay-portability-receipt.json  portability receipt
data/26-repeated-target-audit_replay-replay-package-manifest.json  replay packet manifest
data/26-repeated-target-independent_audit-arithmetic-audit-receipt.json  receipt of audit_arithmetic.py (= its run log, not shipped again)
data/26-repeated-target-independent_audit-audit-manifest.json  the audit's manifest, counts and corollary scope
data/26-repeated-target-independent_audit-freeze-audit-run.log  run log of freeze_audit.py
data/26-repeated-target-independent_audit-semantic-challenge-independent-check-results.json  receipt of the semantic challenge checks
data/26-repeated-target-independent_audit-semantic-challenge-replay.log  replay log of the semantic challenge
data/26-repeated-target-independent_audit-source-audit-receipt.json  receipt of audit_source.py (= its run log, not shipped again)
data/26-repeated-target-science-evidence-build-receipt.json  receipt of build_repeated_certificate.py
data/26-repeated-target-science-evidence-manifest.json  26's packet manifest; pins 25's files under historical directory names
data/26-repeated-target-science-evidence-semantics-receipt.json  receipt of check_repeated_semantics.py
data/26-repeated-target-science-recurrence-review-receipt.json  receipt of check_recurrence.py
data/26-repeated-target-science-source-review-manifest.json  manifest of the source review
data/26-repeated-target-science-source-review-receipt.json  receipt of check_source.py
data/26-repeated-target-universality-SOURCE_PINS.json  pins of Cairns's paper and the local sources
data/26-repeated-target-verification-final-latex.log  LaTeX log of the delivered PDF build
data/26-repeated-target-verification-manuscript_audit-audit-manifest.json  manuscript audit manifest
data/26-repeated-target-verification-manuscript_audit-literal-dag-check.json  receipt of check_literal_dag.py
data/26-repeated-target-verification-manuscript_audit-visual-check.json  visual check of the 17 rendered pages (their SHA-256s; renders not shipped)
data/26-repeated-target-verification-pdf-layout-checks.json  receipt of check_layout.py
data/26-repeated-target-verification-pdf-rebuild-a.json  PDF rebuild record (= pdf-rebuild-b, not shipped again)
data/26-repeated-target-verification-primary-source-accounting.json  quotation-length accounting for Cairns's paper
data/26-repeated-target-verification-release-tool-tests.json  receipt of check_release_tools.py
data/26-repeated-target-verification-scientific-replay.json  scientific replay record
data/26-repeated-target-verification-source-preservation.json  preservation hashes of the packets
data/26-repeated-target-verification-visual-review.json  all-page visual review record
data/27-unrestricted-stab-MANIFEST.json  27's release manifest (delivery paths)
data/27-unrestricted-stab-audit_replay-portability-receipt.json  portability receipt
data/27-unrestricted-stab-hardness-interface-SOURCE_PINS.json  pins of Cairns's paper and the Part XX proofs
data/27-unrestricted-stab-independent_audit-exact-normal.log  run log of check_exact.py (= its receipt and optimized log, not shipped again)
data/27-unrestricted-stab-independent_audit-fresh-semantics-receipt.json  receipt of check_semantics_fresh.py (= its two logs, not shipped again)
data/27-unrestricted-stab-independent_audit-mutation-receipt.json  receipt of challenge_checker.py (20 expected rejections)
data/27-unrestricted-stab-independent_audit-provenance-receipt.json  provenance receipt of the audit
data/27-unrestricted-stab-science-evidence-build-receipt.json  receipt of build_stabilization.py
data/27-unrestricted-stab-science-evidence-manifest.json  27's packet manifest (dependencies by hash)
data/27-unrestricted-stab-science-evidence-polynomial-dag.json  27's polynomial as a literal DAG (926,983 bytes; SHA-256 8622585b…)
data/27-unrestricted-stab-science-evidence-semantics-optimized-run.log  run log of check_semantics.py (= its receipt and normal log, not shipped again)
data/27-unrestricted-stab-science-math-audit-finite-check-receipt.json  receipt of check_math.py
data/27-unrestricted-stab-science-source-audit-audit-receipt.json  receipt of audit_source.py
data/27-unrestricted-stab-science-source-audit-replay-and-mutation-receipt.json  receipt of run_replay_checks.py
data/27-unrestricted-stab-verification-author-isolated-replay-receipt.json  author's isolated replay receipt
data/27-unrestricted-stab-verification-author-visual-qa.json  author's visual QA record
data/27-unrestricted-stab-verification-build-environment.json  build environment record
data/27-unrestricted-stab-verification-dependency-pins.json  dependency pins (Pell, Part XX proofs)
data/27-unrestricted-stab-verification-manuscript-review-COPY_PROVENANCE.json  provenance of the review's copies
data/27-unrestricted-stab-verification-manuscript-review-exact-ledger-optimized-receipt.json  receipt of check_manuscript_evidence.py (= its twins, not shipped again)
data/27-unrestricted-stab-verification-manuscript-review-pdf-fonts.txt  pdffonts output of the delivered PDF
data/27-unrestricted-stab-verification-manuscript-review-pdf-info.txt  pdfinfo output of the delivered PDF
data/27-unrestricted-stab-verification-manuscript-review-visual-review-receipt.json  visual review receipt
data/27-unrestricted-stab-verification-pdf-rebuild-receipt.json  PDF rebuild receipt
data/27-unrestricted-stab-verification-provenance-preservation.json  preservation hashes of the packets
data/27-unrestricted-stab-verification-release-negative-guards.json  receipt of check_release_guards.py
```

The directory holds 570 files: 79 at the root (the article, its PDF, this
README and seventy-six provenance, audit, proof, review and correction files), 189 in `code/` and 302 in
`data/`. Per manuscript: 01 has 12 files, 02 10, 03 17, 04 10, 05 16
besides the replaced `article.tex` and `README.md`, 06 15, 07 14, 08 8, 09
9, 10 14, 11 9, 12 9, 13 9, 14 12, 15 10, 16 19 (1 at the root, 7 in
`code/`, 11 in `data/`), 17 13 (1, 6, 6), 18 16 (1, 5, 10), 19 11 (1, 3, 7),
20 9 (1, 4, 4), 21 53 (2, 22, 29), 22 61 (10, 22, 29), 23 26 (5, 10, 11),
24 46 (9, 12, 25), 25 34 (6, 11, 17), 26 54 (12, 14, 28) and 27 51 (12, 13, 26). Every file of manuscripts 01–27
except `article.tex`, `article.pdf` and `README.md` is byte-identical to the
delivery; for 21 the delivery is, since batch 80, the corrected code edition
(`Eager_Tree_Calculus_Research_Package_corrected.zip`, arrival `4e270aa46`,
placement `8a4e64732`), which replaced four placed files
(`code/21-eager-tree-tree_kernel.py`, `code/21-eager-tree-reproduce.py`,
`data/21-eager-tree-receipt.json`, `data/21-eager-tree-independent_receipt.json`;
the original bytes remain in `a7ae02511` and `aebfa386e`) and added two
(`21-eager-tree-CORRECTION.md`, `code/21-eager-tree-test_application_domain.py`).
The other 47 files of 21 are byte-identical in both editions.

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
| 21 | `cdc:et:` | `cdc:et:thm:certificate` |
| 22 | `cdc:lp:` | `cdc:lp:thm:loader` |
| 23 | `cdc:ro:` | `cdc:ro:thm:main` |
| 24 | `cdc:fx:` | `cdc:fx:thm:main` |
| 25 | `cdc:bt:` | `cdc:bt:thm:main` |
| 26 | `cdc:rp:` | `cdc:rp:thm:main` |
| 27 | `cdc:us:` | `cdc:us:thm:main` |

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

The batch-79 cluster-J2 write (Part XIX) raised the count from 1482 to
1566. It adds all 74 labels of manuscript 21 with the sub-prefix `cdc:et:`,
none dropped, and 10 written labels, which carry the same sub-prefix:
the manuscript subsection `cdc:et:sec:ms` (Section 3.21), the Part
`cdc:et:part`, its conventions section `cdc:et:conv`, the remark
`cdc:et:rem:combinatory`, and six question labels (`cdc:et:q:pairing`,
`…:lookup`, `…:arity`, `…:overhead`, `…:mechanize`, `…:padding`). No
existing label was renamed, removed or renumbered: the 1482 labels of the
previous build have the same numbers, types and anchors in the new `.aux`
(2,964 entries compared one by one), except one retitled entry
(`cdc:sec:manuscripts`, now "The twenty-one manuscripts") and the
hyperlink anchor of the unnumbered paragraph `cdc:conv:b62q` (number 71
unchanged; Section 3.21 adds an unnumbered paragraph before it). Section
3.21's equations are numbered within the subsection ((3.21.1)–(3.21.3));
Part XIX is Sections 224–237, after every existing numbered section.

The batch-83 cluster-H1 write (Part XX) raised the count from 1566 to
1672. It adds all 88 labels of manuscripts 22 and 23 (22 61, 23 27), with
the sub-prefixes `cdc:lp:` and `cdc:ro:`, none dropped (the two share the
bare names `sec:result`, `sec:coefficients` and `eq:AB`), and 18 written
labels: the manuscript subsections `cdc:sec:ms22` and `cdc:sec:ms23`
(Sections 3.22–3.23), the Part `cdc:part:literalsandpile`, its conventions
section `cdc:conv:b83-XX`, the review and question sections
`cdc:sec:b83-review` and `cdc:sec:b83-questions`, `cdc:ro:cor:loader` on
23's unlabelled corollary, the review's equation `cdc:ro:eq:moment` and
remark `cdc:ro:rem:qelimit`, and nine question labels (`cdc:lp:q:encoder`,
`…:automaton`, `…:periods`, `…:variables`, `…:bounds`,
`cdc:ro:q:unbounded`, `…:rigidity`, `…:separation`, `…:packing`). 22's
Section 1 label `sec:result` sits on Section 3.22.1 and 23's on 3.23.1. No
existing label was renamed, removed or renumbered (see Build). Section
3.22's and 3.23's equations are numbered within the subsections; Part XX
is Sections 238–260, after every existing numbered section, and 22's three
diagrams are Figures 3–5, after every existing figure.

The batch-91 cluster-A write (Part XXI) raised the count from 1672 to
1940 (+268), none renamed or removed. It adds 234 labels of manuscripts
24–27 with the sub-prefixes `cdc:fx:` (24, 63), `cdc:bt:` (25, 49),
`cdc:rp:` (26, 38) and `cdc:us:` (27, 84). Manuscript 25's other 35 labels
(its equations, `lem:subset` and `lem:spread` inside its Sections 2–5,
which repeat 24's Sections 3–6 and are printed as pointers) are not
printed; its four section labels there stay on the pointer sections, and
its three references into them point to 24's labels. Written labels (34):
`cdc:sec:ms24`–`cdc:sec:ms27` (Sections 3.24–3.27),
`cdc:part:packedsandpile`, `cdc:conv:b91-XXI`, `cdc:sec:b91-review`,
`cdc:sec:b91-cairns` and `cdc:sec:b91-questions`; in the sub-prefixes,
`cdc:fx:app:inventory` and `cdc:fx:app:pins` on 24's unlabelled appendices,
`cdc:rp:sec:research` on 26's unlabelled closing section, the remark
`cdc:us:rem:cairns`, and 21 question labels (`cdc:fx:q:target`, `…:loader`,
`…:cost`, `…:nonbinary`, `…:formal`; `cdc:bt:q:unrestricted`, `…:loader`,
`…:compiler`, `…:optimization`, `…:formal`, `…:fibre`;
`cdc:rp:q:compiler`, `…:optimization`, `…:formal`; `cdc:us:q:capacity`,
`…:conversions`, `…:degree`, `…:least`, `…:compiler`, `…:formal`,
`…:cairns`). Part XXI is Sections 261–323: 261 its conventions, 262–276
manuscript 24 (its Section `N` is `260+N`; Appendices A–B are 275–276),
277–294 manuscript 25 (`275+N`; 277–280 the pointer sections;
appendices 293–294), 295–305 manuscript 26 (`293+N`), 306–320 manuscript 27
(`304+N`; appendices 319–320), 321 the research programme's review, 322
the Cairns passages and 323 the questions. Theorem numbers follow: 24's
Lemma 2.1 is 262.1, 26's Corollary 10.1 is 303.1, 27's Corollary 12.1 is
316.1. In Section 3, 24's Theorem 1.1 is Theorem 3.7, 25's Theorem 1.1 is
3.8, 26's Theorem 1.1 is 3.9, and 27's Definition 1.1 and Theorem 1.2 are
3.10 and 3.11; Sections 3.24–3.27 number their equations within the
subsections.

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

**Manuscript 21** (package root `eager-tree-certificates/`)

| Delivered | Shipped |
|---|---|
| `VERIFICATION.md` | `21-eager-tree-VERIFICATION.md` |
| `CORRECTION.md` (corrected edition, batch 80) | `21-eager-tree-CORRECTION.md` |
| `reproduce.py` | `code/21-eager-tree-reproduce.py` |
| `build_pdf.py` | `code/21-eager-tree-build_pdf.py` |
| `code/analyze_growth.py` | `code/21-eager-tree-analyze_growth.py` |
| `code/audit_exact_count.py` | `code/21-eager-tree-audit_exact_count.py` |
| `code/canonical.py` | `code/21-eager-tree-canonical.py` |
| `code/canonical_overlay_audit.py` | `code/21-eager-tree-canonical_overlay_audit.py` |
| `code/canonical_projected.py` | `code/21-eager-tree-canonical_projected.py` |
| `code/canonical_projected_audit.py` | `code/21-eager-tree-canonical_projected_audit.py` |
| `code/constant_bit_bound.py` | `code/21-eager-tree-constant_bit_bound.py` |
| `code/counter_source.py` | `code/21-eager-tree-counter_source.py` |
| `code/eager_compiler.py` | `code/21-eager-tree-eager_compiler.py` |
| `code/export_shared_macro.py` | `code/21-eager-tree-export_shared_macro.py` |
| `code/independent_audit.py` | `code/21-eager-tree-independent_audit.py` |
| `code/independent_compiler_audit.py` | `code/21-eager-tree-independent_compiler_audit.py` |
| `code/independent_growth_audit.py` | `code/21-eager-tree-independent_growth_audit.py` |
| `code/independent_shared_audit.py` | `code/21-eager-tree-independent_shared_audit.py` |
| `code/shared_compression.py` | `code/21-eager-tree-shared_compression.py` |
| `code/symbolic_audit.py` | `code/21-eager-tree-symbolic_audit.py` |
| `code/test_application_domain.py` (corrected edition, batch 80) | `code/21-eager-tree-test_application_domain.py` |
| `code/tree_kernel.py` | `code/21-eager-tree-tree_kernel.py` |
| `code/verify_packet_assumptions.py` | `code/21-eager-tree-verify_packet_assumptions.py` |
| `code/verify_shared_macro.py` | `code/21-eager-tree-verify_shared_macro.py` |
| `code/audit_exact_count_receipt.json` | `data/21-eager-tree-audit_exact_count_receipt.json` |
| `code/canonical_identity.json` | `data/21-eager-tree-canonical_identity.json` |
| `code/canonical_overlay_receipt.json` | `data/21-eager-tree-canonical_overlay_receipt.json` |
| `code/canonical_projected_audit_receipt.json` | `data/21-eager-tree-canonical_projected_audit_receipt.json` |
| `code/canonical_projected_identity.json` | `data/21-eager-tree-canonical_projected_identity.json` |
| `code/canonical_projected_receipt.json` | `data/21-eager-tree-canonical_projected_receipt.json` |
| `code/canonical_receipt.json` | `data/21-eager-tree-canonical_receipt.json` |
| `code/constant_bit_bound.json` | `data/21-eager-tree-constant_bit_bound.json` |
| `code/counter_source_receipt.json` | `data/21-eager-tree-counter_source_receipt.json` |
| `code/cyclic_counterfeit.json` | `data/21-eager-tree-cyclic_counterfeit.json` |
| `code/eager_compiler_receipt.json` | `data/21-eager-tree-eager_compiler_receipt.json` |
| `code/exact_growth_receipt.json` | `data/21-eager-tree-exact_growth_receipt.json` |
| `code/identity_certificate.json` | `data/21-eager-tree-identity_certificate.json` |
| `code/independent_compiler_receipt.json` | `data/21-eager-tree-independent_compiler_receipt.json` |
| `code/independent_growth_receipt.json` | `data/21-eager-tree-independent_growth_receipt.json` |
| `code/independent_receipt.json` | `data/21-eager-tree-independent_receipt.json` |
| `code/independent_shared_receipt.json` | `data/21-eager-tree-independent_shared_receipt.json` |
| `code/literal_universal_tree.json` | `data/21-eager-tree-literal_universal_tree.json` |
| `code/literal_universal_tree.sexpr` | `data/21-eager-tree-literal_universal_tree.sexpr` |
| `code/packet_assumptions_receipt.json` | `data/21-eager-tree-packet_assumptions_receipt.json` |
| `code/receipt.json` | `data/21-eager-tree-receipt.json` |
| `code/shared_compression_program.json` | `data/21-eager-tree-shared_compression_program.json` |
| `code/shared_compression_receipt.json` | `data/21-eager-tree-shared_compression_receipt.json` |
| `code/shared_symbolic_proofs.json` | `data/21-eager-tree-shared_symbolic_proofs.json` |
| `code/symbolic_receipt.json` | `data/21-eager-tree-symbolic_receipt.json` |
| `code/universal_code_circuit.json` | `data/21-eager-tree-universal_code_circuit.json` |
| `code/universal_lambda_source.json` | `data/21-eager-tree-universal_lambda_source.json` |
| `sources.json` | `data/21-eager-tree-sources.json` |
| `requirements-optional.txt` | `data/21-eager-tree-requirements-optional.txt` |

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
cite no theorem by number. Part XIX is Sections 224–237: 224 its
conventions, 225–235 manuscript 21's Sections 2–12 (its Section `N` is
Section `223+N`), and 236–237 its Appendices A–B; its Section 1 is Section
3.21.1–3.21.3 (three subsubsections). Its theorem numbers `N.k` become
`(223+N).k` (its Theorem 5.1, the base quartic, is Theorem 228.1; 7.2,
adequacy, 230.2; 8.3, the universal tree, 231.3; 10.3, the canonical
theorem, 233.3; 11.1 and 11.2, the sharing and growth theorems, 234.1 and
234.2); the written remark 230.3 follows the last numbered item of its
Section 7, and its six research directions are Research questions
235.1–235.6. Its equations, numbered globally in the delivery, are
numbered within sections here. Its delivered texts cite no theorem by
number.

**Manuscript 22** (package root `Research_Report35/`)

| Delivered | Shipped |
|---|---|
| `archive_regression.py` | `code/22-literal-sandpiles-archive_regression.py` |
| `archive_release.py` | `code/22-literal-sandpiles-archive_release.py` |
| `build_pdf.py` | `code/22-literal-sandpiles-build_pdf.py` |
| `evidence/composition/example_hypothetical_bound.json` | `data/22-literal-sandpiles-evidence-composition-example_hypothetical_bound.json` |
| `evidence/composition/FROZEN-INPUTS.json` | `data/22-literal-sandpiles-evidence-composition-FROZEN-INPUTS.json` |
| `evidence/composition/literal_composition.py` | `code/22-literal-sandpiles-evidence-composition-literal_composition.py` |
| `evidence/composition/prism_certificate.py` | `code/22-literal-sandpiles-evidence-composition-prism_certificate.py` |
| `evidence/composition/PROOF.md` | `22-literal-sandpiles-evidence-composition-PROOF.md` |
| `evidence/composition/PROVENANCE.json` | `data/22-literal-sandpiles-evidence-composition-PROVENANCE.json` |
| `evidence/composition/README.md` | `22-literal-sandpiles-evidence-composition-README.md` |
| `evidence/composition/review/AUDIT-FROZEN.json` | `data/22-literal-sandpiles-evidence-composition-review-AUDIT-FROZEN.json` |
| `evidence/composition/review/audit_adapter.py` | `code/22-literal-sandpiles-evidence-composition-review-audit_adapter.py` |
| `evidence/composition/review/audit_adapter_results.json` | `data/22-literal-sandpiles-evidence-composition-review-audit_adapter_results.json` |
| `evidence/composition/review/audit_crosscheck.py` | `code/22-literal-sandpiles-evidence-composition-review-audit_crosscheck.py` |
| `evidence/composition/review/audit_crosscheck_results.json` | `data/22-literal-sandpiles-evidence-composition-review-audit_crosscheck_results.json` |
| `evidence/composition/review/audit_independent.py` | `code/22-literal-sandpiles-evidence-composition-review-audit_independent.py` |
| `evidence/composition/review/audit_independent_results.json` | `data/22-literal-sandpiles-evidence-composition-review-audit_independent_results.json` |
| `evidence/composition/review/audit_ledger.json` | `data/22-literal-sandpiles-evidence-composition-review-audit_ledger.json` |
| `evidence/composition/review/audit_polynomial.py` | `code/22-literal-sandpiles-evidence-composition-review-audit_polynomial.py` |
| `evidence/composition/review/audit_streaming.py` | `code/22-literal-sandpiles-evidence-composition-review-audit_streaming.py` |
| `evidence/composition/review/audit_streaming_results.json` | `data/22-literal-sandpiles-evidence-composition-review-audit_streaming_results.json` |
| `evidence/composition/review/INDEPENDENT_AUDIT.md` | `22-literal-sandpiles-evidence-composition-review-INDEPENDENT_AUDIT.md` |
| `evidence/composition/review/REPLAY.json` | `data/22-literal-sandpiles-evidence-composition-review-REPLAY.json` |
| `evidence/composition/test_prism_certificate.py` | `code/22-literal-sandpiles-evidence-composition-test_prism_certificate.py` |
| `evidence/composition/VALIDATION.json` | `data/22-literal-sandpiles-evidence-composition-VALIDATION.json` |
| `evidence/composition/verification.json` | `data/22-literal-sandpiles-evidence-composition-verification.json` |
| `evidence/loader/ca/lazy_u15.py` | `code/22-literal-sandpiles-evidence-loader-ca-lazy_u15.py` |
| `evidence/loader/ca/manifest.json` | `data/22-literal-sandpiles-evidence-loader-ca-manifest.json` |
| `evidence/loader/ca/rules.jsonl.gz` | `data/22-literal-sandpiles-evidence-loader-ca-rules.jsonl.gz` |
| `evidence/loader/ca/SEMANTICS_AND_BOUNDS.md` | `22-literal-sandpiles-evidence-loader-ca-SEMANTICS_AND_BOUNDS.md` |
| `evidence/loader/ca/test_lazy_u15.py` | `code/22-literal-sandpiles-evidence-loader-ca-test_lazy_u15.py` |
| `evidence/loader/ca/verification.json` | `data/22-literal-sandpiles-evidence-loader-ca-verification.json` |
| `evidence/loader/compiler/circuit_manifest.json` | `data/22-literal-sandpiles-evidence-loader-compiler-circuit_manifest.json` |
| `evidence/loader/compiler/coefficient_checks.json` | `data/22-literal-sandpiles-evidence-loader-compiler-coefficient_checks.json` |
| `evidence/loader/compiler/literal_loader.py` | `code/22-literal-sandpiles-evidence-loader-compiler-literal_loader.py` |
| `evidence/loader/compiler/make_example.py` | `code/22-literal-sandpiles-evidence-loader-compiler-make_example.py` |
| `evidence/loader/compiler/test_coefficients.py` | `code/22-literal-sandpiles-evidence-loader-compiler-test_coefficients.py` |
| `evidence/loader/compiler/worked_example.json` | `data/22-literal-sandpiles-evidence-loader-compiler-worked_example.json` |
| `evidence/loader/gates/check_gates.py` | `code/22-literal-sandpiles-evidence-loader-gates-check_gates.py` |
| `evidence/loader/gates/GATE-PROOF.md` | `22-literal-sandpiles-evidence-loader-gates-GATE-PROOF.md` |
| `evidence/loader/gates/gate_receipt.json` | `data/22-literal-sandpiles-evidence-loader-gates-gate_receipt.json` |
| `evidence/loader/geometry/periodic_router.py` | `code/22-literal-sandpiles-evidence-loader-geometry-periodic_router.py` |
| `evidence/loader/geometry/periodic_router_proof.md` | `22-literal-sandpiles-evidence-loader-geometry-periodic_router_proof.md` |
| `evidence/loader/geometry/router_checks.json` | `data/22-literal-sandpiles-evidence-loader-geometry-router_checks.json` |
| `evidence/loader/INDEPENDENT-AUDIT.md` | `22-literal-sandpiles-evidence-loader-INDEPENDENT-AUDIT.md` |
| `evidence/loader/LOADER-PROOF.md` | `22-literal-sandpiles-evidence-loader-LOADER-PROOF.md` |
| `evidence/loader/PROVENANCE.json` | `data/22-literal-sandpiles-evidence-loader-PROVENANCE.json` |
| `evidence/loader/README.md` | `22-literal-sandpiles-evidence-loader-README.md` |
| `evidence/loader/VALIDATION.json` | `data/22-literal-sandpiles-evidence-loader-VALIDATION.json` |
| `evidence/loader/verify_bundle.py` | `code/22-literal-sandpiles-evidence-loader-verify_bundle.py` |
| `INTEGRITY.md` | `22-literal-sandpiles-INTEGRITY.md` |
| `seal_release.py` | `code/22-literal-sandpiles-seal_release.py` |
| `tamper_regression.py` | `code/22-literal-sandpiles-tamper_regression.py` |
| `verification/document-qa.json` | `data/22-literal-sandpiles-verification-document-qa.json` |
| `verification/expected-receipts.json` | `data/22-literal-sandpiles-verification-expected-receipts.json` |
| `verification/primary-references.json` | `data/22-literal-sandpiles-verification-primary-references.json` |
| `verification/replay-plan.json` | `data/22-literal-sandpiles-verification-replay-plan.json` |
| `verification/root-certificate-review.json` | `data/22-literal-sandpiles-verification-root-certificate-review.json` |
| `verification/root-loader-review.json` | `data/22-literal-sandpiles-verification-root-loader-review.json` |
| `verification/source-lineage.json` | `data/22-literal-sandpiles-verification-source-lineage.json` |
| `verify_release.py` | `code/22-literal-sandpiles-verify_release.py` |

**Manuscript 23** (package root `Research_Report36/`)

| Delivered | Shipped |
|---|---|
| `archive_regression.py` | `code/23-real-sandpiles-archive_regression.py` |
| `archive_release.py` | `code/23-real-sandpiles-archive_release.py` |
| `build_pdf.py` | `code/23-real-sandpiles-build_pdf.py` |
| `evidence/real/ENVIRONMENT.json` | `data/23-real-sandpiles-evidence-real-ENVIRONMENT.json` |
| `evidence/real/exact_checks.py` | `code/23-real-sandpiles-evidence-real-exact_checks.py` |
| `evidence/real/freeze_packet.py` | `code/23-real-sandpiles-evidence-real-freeze_packet.py` |
| `evidence/real/independent_coefficient_ledger_checks.py` | `code/23-real-sandpiles-evidence-real-independent_coefficient_ledger_checks.py` |
| `evidence/real/independent_coefficient_ledger_receipt.json` | `data/23-real-sandpiles-evidence-real-independent_coefficient_ledger_receipt.json` |
| `evidence/real/independent_math_review.md` | `23-real-sandpiles-evidence-real-independent_math_review.md` |
| `evidence/real/PROOF.md` | `23-real-sandpiles-evidence-real-PROOF.md` |
| `evidence/real/PUBLIC_PRIOR_ART.md` | `23-real-sandpiles-evidence-real-PUBLIC_PRIOR_ART.md` |
| `evidence/real/README.md` | `23-real-sandpiles-evidence-real-README.md` |
| `evidence/real/real_certificate.py` | `code/23-real-sandpiles-evidence-real-real_certificate.py` |
| `evidence/real/report35_integrity_check.txt` | `data/23-real-sandpiles-evidence-real-report35_integrity_check.txt` |
| `evidence/real/verification.json` | `data/23-real-sandpiles-evidence-real-verification.json` |
| `INTEGRITY.md` | `23-real-sandpiles-INTEGRITY.md` |
| `seal_release.py` | `code/23-real-sandpiles-seal_release.py` |
| `tamper_regression.py` | `code/23-real-sandpiles-tamper_regression.py` |
| `verification/article-quality.json` | `data/23-real-sandpiles-verification-article-quality.json` |
| `verification/expected-receipts.json` | `data/23-real-sandpiles-verification-expected-receipts.json` |
| `verification/pdf-rebuild.json` | `data/23-real-sandpiles-verification-pdf-rebuild.json` |
| `verification/release-review.json` | `data/23-real-sandpiles-verification-release-review.json` |
| `verification/replay-plan.json` | `data/23-real-sandpiles-verification-replay-plan.json` |
| `verification/source-lineage.json` | `data/23-real-sandpiles-verification-source-lineage.json` |
| `verification/tooling-tests.json` | `data/23-real-sandpiles-verification-tooling-tests.json` |
| `verify_release.py` | `code/23-real-sandpiles-verify_release.py` |

Nested delivered paths are flattened with `-` after the prefix (`evidence/loader/ca/lazy_u15.py` is `code/22-literal-sandpiles-evidence-loader-ca-lazy_u15.py`); the recipe in "Rerunning the checks" reverses this. Part XX is Sections 238–260 of the article: 238 its conventions, 239–250 manuscript 22's Sections 2–13 (its Section `N` is Section `237+N`), 251–258 manuscript 23's Sections 2–9 (its Section `N` is Section `249+N`), 259 the research programme's review and 260 the questions; their Sections 1 are Sections 3.22.1 and 3.23.1. Theorem numbers `N.k` become `(237+N).k` and `(249+N).k`: 22's Lemma 9.1 and Theorem 9.2 (the certificate) are 246.1 and 246.2, its Proposition 7.1 (the prism) 244.1, its Remark 9.3 246.3 and its Corollary 10.1 247.1; 23's Lemmas 3.1–3.3 are 252.1–252.3, its Proposition 5.1 254.1 and its Corollary 7.1 256.1. In Section 3, 22's Definition 1.1 and Theorems 1.2–1.3 are Definition 3.3 and Theorems 3.4–3.5, and 23's Theorem 1.1 is Theorem 3.6. Their delivered texts cite no theorem by number; the shipped proofs and audits use their own numbering.

**Manuscript 24** (package root `Research_Report50/`)

| Delivered | Shipped |
|---|---|
| `archive_release.py` | `code/24-fixed-arity-archive_release.py` |
| `audit_replay/evidence/replay-runner-receipt.json` | `data/24-fixed-arity-audit_replay-evidence-replay-runner-receipt.json` |
| `audit_replay/evidence/replay-scientific-receipt.json` | `data/24-fixed-arity-audit_replay-evidence-replay-scientific-receipt.json` |
| `audit_replay/evidence/test-results.json` | `data/24-fixed-arity-audit_replay-evidence-test-results.json` |
| `audit_replay/README.md` | `24-fixed-arity-audit_replay-README.md` |
| `audit_replay/replay-pin-manifest.json` | `data/24-fixed-arity-audit_replay-replay-pin-manifest.json` |
| `audit_replay/replay_independent_audit.py` | `code/24-fixed-arity-audit_replay-replay_independent_audit.py` |
| `audit_replay/test_replay_runner.py` | `code/24-fixed-arity-audit_replay-test_replay_runner.py` |
| `build_pdf.py` | `code/24-fixed-arity-build_pdf.py` |
| `independent_audit/audit-manifest.json` | `data/24-fixed-arity-independent_audit-audit-manifest.json` |
| `independent_audit/AUDIT.md` | `24-fixed-arity-independent_audit-AUDIT.md` |
| `independent_audit/independent_check.py` | `code/24-fixed-arity-independent_audit-independent_check.py` |
| `MANIFEST.json` | `data/24-fixed-arity-MANIFEST.json` |
| `science/build_certificate.py` | `code/24-fixed-arity-science-build_certificate.py` |
| `science/check_exact_degree.py` | `code/24-fixed-arity-science-check_exact_degree.py` |
| `science/check_source.py` | `code/24-fixed-arity-science-check_source.py` |
| `science/evidence/build-receipt.json` | `data/24-fixed-arity-science-evidence-build-receipt.json` |
| `science/evidence/exact-degree-receipt.json` | `data/24-fixed-arity-science-evidence-exact-degree-receipt.json` |
| `science/evidence/polynomial-dag.json` | `data/24-fixed-arity-science-evidence-polynomial-dag.json` |
| `science/evidence/source-check-receipt.json` | `data/24-fixed-arity-science-evidence-source-check-receipt.json` |
| `science/periodic-input/check_periodic_packing.py` | `code/24-fixed-arity-science-periodic-input-check_periodic_packing.py` |
| `science/periodic-input/periodic_packing_lemma.md` | `24-fixed-arity-science-periodic-input-periodic_packing_lemma.md` |
| `science/periodic-input/verification_receipt.json` | `data/24-fixed-arity-science-periodic-input-verification_receipt.json` |
| `science/PROOF.md` | `24-fixed-arity-science-PROOF.md` |
| `science/README.md` | `24-fixed-arity-science-README.md` |
| `science/SCOPE.md` | `24-fixed-arity-science-SCOPE.md` |
| `science/sources/source-pins.json` | `data/24-fixed-arity-science-sources-source-pins.json` |
| `science/stream-products/and-spread-check-receipt.json` | `data/24-fixed-arity-science-stream-products-and-spread-check-receipt.json` |
| `science/stream-products/AND_SPREAD_PROOF.md` | `24-fixed-arity-science-stream-products-AND_SPREAD_PROOF.md` |
| `science/stream-products/mask-check-receipt.json` | `data/24-fixed-arity-science-stream-products-mask-check-receipt.json` |
| `science/stream-products/MASK_SUBSET_PROOF.md` | `24-fixed-arity-science-stream-products-MASK_SUBSET_PROOF.md` |
| `science/stream-products/verify_and_spread.py` | `code/24-fixed-arity-science-stream-products-verify_and_spread.py` |
| `science/stream-products/verify_mask_subset.py` | `code/24-fixed-arity-science-stream-products-verify_mask_subset.py` |
| `verification/coordinating-review.json` | `data/24-fixed-arity-verification-coordinating-review.json` |
| `verification/final-latex.log` | `data/24-fixed-arity-verification-final-latex.log` |
| `verification/helper-path-guards.json` | `data/24-fixed-arity-verification-helper-path-guards.json` |
| `verification/manuscript-review-receipt.json` | `data/24-fixed-arity-verification-manuscript-review-receipt.json` |
| `verification/MANUSCRIPT_REVIEW.md` | `24-fixed-arity-verification-MANUSCRIPT_REVIEW.md` |
| `verification/pdf-reproduction.json` | `data/24-fixed-arity-verification-pdf-reproduction.json` |
| `verification/reference-check.json` | `data/24-fixed-arity-verification-reference-check.json` |
| `verification/release-readiness.json` | `data/24-fixed-arity-verification-release-readiness.json` |
| `verification/science-freeze.json` | `data/24-fixed-arity-verification-science-freeze.json` |
| `verification/science-preservation.json` | `data/24-fixed-arity-verification-science-preservation.json` |
| `verification/toolchain.json` | `data/24-fixed-arity-verification-toolchain.json` |
| `verification/visual-review.json` | `data/24-fixed-arity-verification-visual-review.json` |
| `verify_release.py` | `code/24-fixed-arity-verify_release.py` |

**Manuscript 25** (package root: the archive root)

| Delivered | Shipped |
|---|---|
| `archive_release.py` | `code/25-binary-target-archive_release.py` |
| `audit_replay/evidence/audit-receipt.json` | `data/25-binary-target-audit_replay-evidence-audit-receipt.json` |
| `audit_replay/evidence/replay-receipt.json` | `data/25-binary-target-audit_replay-evidence-replay-receipt.json` |
| `audit_replay/evidence/semantics-receipt.json` | `data/25-binary-target-audit_replay-evidence-semantics-receipt.json` |
| `audit_replay/evidence/test-results.json` | `data/25-binary-target-audit_replay-evidence-test-results.json` |
| `audit_replay/README.md` | `25-binary-target-audit_replay-README.md` |
| `audit_replay/replay-pin-manifest.json` | `data/25-binary-target-audit_replay-replay-pin-manifest.json` |
| `audit_replay/replay_audits.py` | `code/25-binary-target-audit_replay-replay_audits.py` |
| `audit_replay/test_replay_adapter.py` | `code/25-binary-target-audit_replay-test_replay_adapter.py` |
| `build_pdf.py` | `code/25-binary-target-build_pdf.py` |
| `independent_audit/audit-manifest.json` | `data/25-binary-target-independent_audit-audit-manifest.json` |
| `independent_audit/AUDIT.md` | `25-binary-target-independent_audit-AUDIT.md` |
| `independent_audit/independent_check.py` | `code/25-binary-target-independent_audit-independent_check.py` |
| `independent_audit/SEMANTICS.md` | `25-binary-target-independent_audit-SEMANTICS.md` |
| `independent_audit/semantics_check.py` | `code/25-binary-target-independent_audit-semantics_check.py` |
| `MANIFEST.json` | `data/25-binary-target-MANIFEST.json` |
| `science/ARCHITECTURE.md` | `25-binary-target-science-ARCHITECTURE.md` |
| `science/build_target_certificate.py` | `code/25-binary-target-science-build_target_certificate.py` |
| `science/check_target_certificate.py` | `code/25-binary-target-science-check_target_certificate.py` |
| `science/evidence/build-receipt.json` | `data/25-binary-target-science-evidence-build-receipt.json` |
| `science/evidence/check-receipt.json` | `data/25-binary-target-science-evidence-check-receipt.json` |
| `science/evidence/polynomial-dag.json` | `data/25-binary-target-science-evidence-polynomial-dag.json` |
| `science/SOURCE_NOTES.md` | `25-binary-target-science-SOURCE_NOTES.md` |
| `test_release_tools.py` | `code/25-binary-target-test_release_tools.py` |
| `verification/manuscript_review/check_manuscript.py` | `code/25-binary-target-verification-manuscript_review-check_manuscript.py` |
| `verification/manuscript_review/MANUSCRIPT_REVIEW.md` | `25-binary-target-verification-manuscript_review-MANUSCRIPT_REVIEW.md` |
| `verification/manuscript_review/review-summary.json` | `data/25-binary-target-verification-manuscript_review-review-summary.json` |
| `verification/manuscript_review/text-check-receipt.json` | `data/25-binary-target-verification-manuscript_review-text-check-receipt.json` |
| `verification/manuscript_review/visual-review-receipt.json` | `data/25-binary-target-verification-manuscript_review-visual-review-receipt.json` |
| `verification/pdf-build.json` | `data/25-binary-target-verification-pdf-build.json` |
| `verification/pdf-layout-checks.json` | `data/25-binary-target-verification-pdf-layout-checks.json` |
| `verification/release-tool-tests.json` | `data/25-binary-target-verification-release-tool-tests.json` |
| `verification/source-preservation.json` | `data/25-binary-target-verification-source-preservation.json` |
| `verify_release.py` | `code/25-binary-target-verify_release.py` |

**Manuscript 26** (package root: the archive root)

| Delivered | Shipped |
|---|---|
| `audit_replay/independent-review-verification.json` | `data/26-repeated-target-audit_replay-independent-review-verification.json` |
| `audit_replay/portability-receipt.json` | `data/26-repeated-target-audit_replay-portability-receipt.json` |
| `audit_replay/PORTABILITY_REPORT.md` | `26-repeated-target-audit_replay-PORTABILITY_REPORT.md` |
| `audit_replay/README.md` | `26-repeated-target-audit_replay-README.md` |
| `audit_replay/replay-package-manifest.json` | `data/26-repeated-target-audit_replay-replay-package-manifest.json` |
| `audit_replay/replay_audit.py` | `code/26-repeated-target-audit_replay-replay_audit.py` |
| `dependencies/NOTICE.md` | `26-repeated-target-dependencies-NOTICE.md` |
| `independent_audit/arithmetic-audit-receipt.json` | `data/26-repeated-target-independent_audit-arithmetic-audit-receipt.json` |
| `independent_audit/audit-manifest.json` | `data/26-repeated-target-independent_audit-audit-manifest.json` |
| `independent_audit/AUDIT.md` | `26-repeated-target-independent_audit-AUDIT.md` |
| `independent_audit/audit_arithmetic.py` | `code/26-repeated-target-independent_audit-audit_arithmetic.py` |
| `independent_audit/audit_source.py` | `code/26-repeated-target-independent_audit-audit_source.py` |
| `independent_audit/freeze-audit-run.log` | `data/26-repeated-target-independent_audit-freeze-audit-run.log` |
| `independent_audit/freeze_audit.py` | `code/26-repeated-target-independent_audit-freeze_audit.py` |
| `independent_audit/semantic-challenge/independent-check-results.json` | `data/26-repeated-target-independent_audit-semantic-challenge-independent-check-results.json` |
| `independent_audit/semantic-challenge/independent_checks.py` | `code/26-repeated-target-independent_audit-semantic-challenge-independent_checks.py` |
| `independent_audit/semantic-challenge/replay.log` | `data/26-repeated-target-independent_audit-semantic-challenge-replay.log` |
| `independent_audit/semantic-challenge/report.md` | `26-repeated-target-independent_audit-semantic-challenge-report.md` |
| `independent_audit/source-audit-receipt.json` | `data/26-repeated-target-independent_audit-source-audit-receipt.json` |
| `MANIFEST.json` | `data/26-repeated-target-MANIFEST.json` |
| `release.py` | `code/26-repeated-target-release.py` |
| `science/ARCHITECTURE.md` | `26-repeated-target-science-ARCHITECTURE.md` |
| `science/build_repeated_certificate.py` | `code/26-repeated-target-science-build_repeated_certificate.py` |
| `science/check_repeated_semantics.py` | `code/26-repeated-target-science-check_repeated_semantics.py` |
| `science/evidence/build-receipt.json` | `data/26-repeated-target-science-evidence-build-receipt.json` |
| `science/evidence/manifest.json` | `data/26-repeated-target-science-evidence-manifest.json` |
| `science/evidence/semantics-receipt.json` | `data/26-repeated-target-science-evidence-semantics-receipt.json` |
| `science/finalize_manifest.py` | `code/26-repeated-target-science-finalize_manifest.py` |
| `science/recurrence-review/check_recurrence.py` | `code/26-repeated-target-science-recurrence-review-check_recurrence.py` |
| `science/recurrence-review/receipt.json` | `data/26-repeated-target-science-recurrence-review-receipt.json` |
| `science/recurrence-review/REVIEW.md` | `26-repeated-target-science-recurrence-review-REVIEW.md` |
| `science/source-review/check_source.py` | `code/26-repeated-target-science-source-review-check_source.py` |
| `science/source-review/manifest.json` | `data/26-repeated-target-science-source-review-manifest.json` |
| `science/source-review/receipt.json` | `data/26-repeated-target-science-source-review-receipt.json` |
| `science/source-review/REVIEW.md` | `26-repeated-target-science-source-review-REVIEW.md` |
| `science/SOURCE_NOTES.md` | `26-repeated-target-science-SOURCE_NOTES.md` |
| `universality/PRIMARY_SOURCE.md` | `26-repeated-target-universality-PRIMARY_SOURCE.md` |
| `universality/REVIEW.md` | `26-repeated-target-universality-REVIEW.md` |
| `universality/SOURCE_PINS.json` | `data/26-repeated-target-universality-SOURCE_PINS.json` |
| `verification/check_layout.py` | `code/26-repeated-target-verification-check_layout.py` |
| `verification/check_release_tools.py` | `code/26-repeated-target-verification-check_release_tools.py` |
| `verification/final-latex.log` | `data/26-repeated-target-verification-final-latex.log` |
| `verification/manuscript_audit/audit-manifest.json` | `data/26-repeated-target-verification-manuscript_audit-audit-manifest.json` |
| `verification/manuscript_audit/AUDIT.md` | `26-repeated-target-verification-manuscript_audit-AUDIT.md` |
| `verification/manuscript_audit/check_literal_dag.py` | `code/26-repeated-target-verification-manuscript_audit-check_literal_dag.py` |
| `verification/manuscript_audit/literal-dag-check.json` | `data/26-repeated-target-verification-manuscript_audit-literal-dag-check.json` |
| `verification/manuscript_audit/visual-check.json` | `data/26-repeated-target-verification-manuscript_audit-visual-check.json` |
| `verification/pdf-layout-checks.json` | `data/26-repeated-target-verification-pdf-layout-checks.json` |
| `verification/pdf-rebuild-a.json` | `data/26-repeated-target-verification-pdf-rebuild-a.json` |
| `verification/primary-source-accounting.json` | `data/26-repeated-target-verification-primary-source-accounting.json` |
| `verification/release-tool-tests.json` | `data/26-repeated-target-verification-release-tool-tests.json` |
| `verification/scientific-replay.json` | `data/26-repeated-target-verification-scientific-replay.json` |
| `verification/source-preservation.json` | `data/26-repeated-target-verification-source-preservation.json` |
| `verification/visual-review.json` | `data/26-repeated-target-verification-visual-review.json` |

**Manuscript 27** (package root: the archive root)

| Delivered | Shipped |
|---|---|
| `audit_replay/portability-receipt.json` | `data/27-unrestricted-stab-audit_replay-portability-receipt.json` |
| `audit_replay/PORTABILITY_REPORT.md` | `27-unrestricted-stab-audit_replay-PORTABILITY_REPORT.md` |
| `audit_replay/README.md` | `27-unrestricted-stab-audit_replay-README.md` |
| `audit_replay/replay_audit.py` | `code/27-unrestricted-stab-audit_replay-replay_audit.py` |
| `hardness-interface/CORRECTIONS.md` | `27-unrestricted-stab-hardness-interface-CORRECTIONS.md` |
| `hardness-interface/POTENTIAL_COROLLARY.md` | `27-unrestricted-stab-hardness-interface-POTENTIAL_COROLLARY.md` |
| `hardness-interface/PRIMARY_LOCATORS.md` | `27-unrestricted-stab-hardness-interface-PRIMARY_LOCATORS.md` |
| `hardness-interface/REVIEW.md` | `27-unrestricted-stab-hardness-interface-REVIEW.md` |
| `hardness-interface/SOURCE_PINS.json` | `data/27-unrestricted-stab-hardness-interface-SOURCE_PINS.json` |
| `independent_audit/AUDIT.md` | `27-unrestricted-stab-independent_audit-AUDIT.md` |
| `independent_audit/challenge_checker.py` | `code/27-unrestricted-stab-independent_audit-challenge_checker.py` |
| `independent_audit/check_exact.py` | `code/27-unrestricted-stab-independent_audit-check_exact.py` |
| `independent_audit/check_semantics_fresh.py` | `code/27-unrestricted-stab-independent_audit-check_semantics_fresh.py` |
| `independent_audit/exact-normal.log` | `data/27-unrestricted-stab-independent_audit-exact-normal.log` |
| `independent_audit/fresh-semantics-receipt.json` | `data/27-unrestricted-stab-independent_audit-fresh-semantics-receipt.json` |
| `independent_audit/mutation-receipt.json` | `data/27-unrestricted-stab-independent_audit-mutation-receipt.json` |
| `independent_audit/provenance-receipt.json` | `data/27-unrestricted-stab-independent_audit-provenance-receipt.json` |
| `MANIFEST.json` | `data/27-unrestricted-stab-MANIFEST.json` |
| `release.py` | `code/27-unrestricted-stab-release.py` |
| `science/build_stabilization.py` | `code/27-unrestricted-stab-science-build_stabilization.py` |
| `science/check_semantics.py` | `code/27-unrestricted-stab-science-check_semantics.py` |
| `science/evidence/build-receipt.json` | `data/27-unrestricted-stab-science-evidence-build-receipt.json` |
| `science/evidence/manifest.json` | `data/27-unrestricted-stab-science-evidence-manifest.json` |
| `science/evidence/polynomial-dag.json` | `data/27-unrestricted-stab-science-evidence-polynomial-dag.json` |
| `science/evidence/semantics-optimized-run.log` | `data/27-unrestricted-stab-science-evidence-semantics-optimized-run.log` |
| `science/finalize_manifest.py` | `code/27-unrestricted-stab-science-finalize_manifest.py` |
| `science/math-audit/AUDIT.md` | `27-unrestricted-stab-science-math-audit-AUDIT.md` |
| `science/math-audit/check_math.py` | `code/27-unrestricted-stab-science-math-audit-check_math.py` |
| `science/math-audit/finite-check-receipt.json` | `data/27-unrestricted-stab-science-math-audit-finite-check-receipt.json` |
| `science/PROOF.md` | `27-unrestricted-stab-science-PROOF.md` |
| `science/README.md` | `27-unrestricted-stab-science-README.md` |
| `science/source-audit/audit-receipt.json` | `data/27-unrestricted-stab-science-source-audit-audit-receipt.json` |
| `science/source-audit/audit_source.py` | `code/27-unrestricted-stab-science-source-audit-audit_source.py` |
| `science/source-audit/replay-and-mutation-receipt.json` | `data/27-unrestricted-stab-science-source-audit-replay-and-mutation-receipt.json` |
| `science/source-audit/run_replay_checks.py` | `code/27-unrestricted-stab-science-source-audit-run_replay_checks.py` |
| `science/source-audit/SOURCE_AUDIT.md` | `27-unrestricted-stab-science-source-audit-SOURCE_AUDIT.md` |
| `verification/author-isolated-replay-receipt.json` | `data/27-unrestricted-stab-verification-author-isolated-replay-receipt.json` |
| `verification/author-visual-qa.json` | `data/27-unrestricted-stab-verification-author-visual-qa.json` |
| `verification/build-environment.json` | `data/27-unrestricted-stab-verification-build-environment.json` |
| `verification/check_release_guards.py` | `code/27-unrestricted-stab-verification-check_release_guards.py` |
| `verification/dependency-pins.json` | `data/27-unrestricted-stab-verification-dependency-pins.json` |
| `verification/manuscript-review/AUDIT.md` | `27-unrestricted-stab-verification-manuscript-review-AUDIT.md` |
| `verification/manuscript-review/check_manuscript_evidence.py` | `code/27-unrestricted-stab-verification-manuscript-review-check_manuscript_evidence.py` |
| `verification/manuscript-review/COPY_PROVENANCE.json` | `data/27-unrestricted-stab-verification-manuscript-review-COPY_PROVENANCE.json` |
| `verification/manuscript-review/exact-ledger-optimized-receipt.json` | `data/27-unrestricted-stab-verification-manuscript-review-exact-ledger-optimized-receipt.json` |
| `verification/manuscript-review/pdf-fonts.txt` | `data/27-unrestricted-stab-verification-manuscript-review-pdf-fonts.txt` |
| `verification/manuscript-review/pdf-info.txt` | `data/27-unrestricted-stab-verification-manuscript-review-pdf-info.txt` |
| `verification/manuscript-review/visual-review-receipt.json` | `data/27-unrestricted-stab-verification-manuscript-review-visual-review-receipt.json` |
| `verification/pdf-rebuild-receipt.json` | `data/27-unrestricted-stab-verification-pdf-rebuild-receipt.json` |
| `verification/provenance-preservation.json` | `data/27-unrestricted-stab-verification-provenance-preservation.json` |
| `verification/release-negative-guards.json` | `data/27-unrestricted-stab-verification-release-negative-guards.json` |

The same flattening applies to 24–27 (`science/stream-products/verify_and_spread.py` is `code/24-fixed-arity-science-stream-products-verify_and_spread.py`); `.py` files are in `code/`, `.md` files at the root and every other file in `data/`. Manuscript 25's bundled `baseline_report50/` is manuscript 24's delivery byte for byte and has no shipped names of its own; read `baseline_report50/<path>` as manuscript 24's `<path>`. In-package twins that are not shipped are listed under "Not shipped" below with the shipped file they equal. Part XXI is Sections 261–323 (see Labels for the section and theorem numbers).

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
was excluded as heavy and no data need reconstructing. For the batch-79
addition 21: its `eager-tree-certificates.tex`, delivery `README.md` and
30-page PDF survive in the arrival commit `aebfa386e`, as members of
`Eager_Tree_Calculus_Research_Package.zip`
(`git show aebfa386e:docs/incoming/Eager_Tree_Calculus_Research_Package.zip`;
SHA-256 `5c6c1002…04ab4`, 595,430 bytes). Its checksum ledger
`MANIFEST.sha256` (55/55) was verified and retired at placement
(`a7ae02511`), with its checker `verify_manifest.py`, which checks only
that ledger. Its largest file is `shared_symbolic_proofs.json` (88,147
bytes), so nothing was excluded as heavy and no data need reconstructing.
The complete corrected layout of 21 (batch 80) is preferably retrieved from
`git show 4e270aa46:docs/incoming/Eager_Tree_Calculus_Research_Package_corrected.zip`
(SHA-256 `2c053f50…0f3dbd`, 598,941 bytes); its refreshed `MANIFEST.sha256`
(57/57) was verified and retired at the batch-80 placement (`8a4e64732`),
and its delivery `README.md` (with a correction notice) is not shipped.
The `aebfa386e` command above retrieves the original edition.
For the batch-83 additions 22 and 23: their manuscripts
(`Research_Report35.tex`, `Research_Report36.tex`), delivery `README.md`
files and PDFs (23 and 13 pages) survive in the arrival commit `3051d1446`,
as members of `Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip`
(1,645,467 bytes, SHA-256 `3202b1f0…a12d`) and
`Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip` (423,395
bytes, SHA-256 `72cfb3a8…96ac`)
(`git show 3051d1446:docs/incoming/<archive>.zip`). Their checksum
ledgers and release seals were verified against a fresh extraction and
retired at placement (`216bd81e1`): 22's `SHA256SUMS` (78/78),
`MANIFEST.json` (77/77) and `evidence/loader/FROZEN-INPUTS.json` (24/24),
and 23's `SHA256SUMS` (36/36), `MANIFEST.json` (35/35),
`evidence/real/SHA256SUMS` (17/17) and `evidence/real/MANIFEST.json`
(16/16). 22's `evidence/composition/FROZEN-INPUTS.json`,
`evidence/composition/review/AUDIT-FROZEN.json` and both
`verification/source-lineage.json` files carry content besides hashes and
are shipped as data. Not shipped as copies: 22's
`evidence/loader/data/u15_table.json`, byte-identical to
`quadratic-orthant-certificates/data/16-universal-membrane-tm_table.json`
(blob `c4aeb5671`); 22's ten `evidence/composition/review/*.normal.out` and
`*.optimized.out` console outputs and `evidence/composition/verification_optimized.json`,
byte-identical to the receipts they repeat; 23's two optimized-mode
receipts (`evidence/real/verification_optimized.json`,
`independent_coefficient_ledger_receipt_optimized.json`), likewise; and 23's
`evidence/real/approved_base/PROOF.md` and `prism_certificate.py`,
byte-identical to 22's `evidence/composition/PROOF.md` and
`prism_certificate.py` (shipped as `22-literal-sandpiles-evidence-composition-PROOF.md`
and `code/22-literal-sandpiles-evidence-composition-prism_certificate.py`).
Three of the unshipped files are read by delivered programs; the rerun
recipe below restores them. The one file over 1 MB,
`data/22-literal-sandpiles-evidence-loader-ca-rules.jsonl.gz` (1,870,861
bytes), is shipped, not excluded: `lazy_u15.py` regenerates its content in
about 30 s (`py code/lazy_u15.py --manifest m.json --rules-jsonl
rules.jsonl.gz` in a copy with the delivered layout), but not byte for
byte. The gzip header records a modification time and the stored file
name, and on Windows the text-mode writer emits CRLF, so the decompressed
stream differs from the manifest's `canonical_integer_rules_jsonl_sha256`
until carriage returns are removed; after that the 9,711,068-byte stream
equals the delivered one (checked at placement). `.gitattributes` treats
`*.gz` as binary, so the blob is the delivered bytes.
For the batch-91 additions 24–27: their manuscripts
(`Research_Report50.tex`, `Research_Report52.tex`, `Research_Report53.tex`,
`article/Report54.tex`), delivery `README.md` files and PDFs (20, 24, 17 and
20 pages) survive in the arrival commit `0d7f51c44`, as members of
`A_Fixed_Arity_Integer_Certificate_for_Binary_Sandpile_Stabilization_Package.zip`
(593,467 bytes, SHA-256 `298dc832…2508`),
`Finite_Legal_Binary_Target_Firing_in_Periodic_Sandpiles_Package.zip`
(3,038,694 bytes, `2d9da85e…0803`),
`Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package.zip`
(5,890,324 bytes, `f45cabb3…5f47`) and
`Unrestricted_Finite_Global_Sandpile_Stabilization_Package.zip`
(3,717,605 bytes, `c8dd5b47…f545`)
(`git show 0d7f51c44:docs/incoming/<archive>.zip`). Of their 320 regular
members, 185 are shipped (byte-identical, verified at placement
`b0a536b63`) and 135 are not:

- *Release manifests and the checksum file.* The four root `MANIFEST.json`
  files (path, SHA-256, size and mode of every other member; verified 58/58,
  101/101, 83/83 and 74/74, with 25's nested `baseline_report50/MANIFEST.json`
  58/58) carry content besides hashes and are shipped as
  `data/2N-…-MANIFEST.json`; they list delivery paths, including files not
  shipped. 27's `independent_audit/SHA256SUMS` (12/12) is a checksum ledger,
  verified and not shipped.
- *Manuscript 25's `baseline_report50/`* (59 files): manuscript 24's
  delivery byte for byte, shipped once as 24's files.
- *Byte-identical twins inside a package* (34; each equals a shipped file):
  24's `independent_audit/audit-receipt.json`, `independent_audit/audit-run.log`,
  `verification/independent-replay-audit-receipt.json` and
  `…-audit-run.log` (= `data/24-fixed-arity-audit_replay-evidence-replay-scientific-receipt.json`)
  and `verification/independent-replay-replay-receipt.json`
  (= `…-replay-runner-receipt.json`); 25's `audit_replay/evidence/audit-run.log`,
  `independent_audit/audit-receipt.json` and `…/audit-run.log`
  (= `data/25-binary-target-audit_replay-evidence-audit-receipt.json`),
  `audit_replay/evidence/semantics-run.log` and
  `independent_audit/semantics-receipt.json` (= `…-semantics-receipt.json`)
  and `verification/scientific-replay.json` (= `…-replay-receipt.json`);
  26's `independent_audit/arithmetic-audit-run.log` and `source-audit-run.log`
  (= the two receipts), `science/evidence/semantics-replay.log`
  (= `…-evidence-semantics-receipt.json`), `science/source-review/replay.log`
  and `run.log` (= `…-source-review-receipt.json`) and
  `verification/pdf-rebuild-b.json` (= `…-pdf-rebuild-a.json`); 27's
  `independent_audit/exact-optimized.log` and `exact-receipt.json`
  (= `…-exact-normal.log`), `semantics-normal.log` and
  `semantics-optimized.log` (= `…-fresh-semantics-receipt.json`),
  `science/evidence/semantics-receipt.json` and `semantics-run.log`
  (= `…-semantics-optimized-run.log`), the eight files of
  `science/source-audit/replay-normal*` and `replay-optimized*` (two
  926,983-byte copies of the DAG, two build receipts, two stdout receipts and
  two audit receipts, equal to the shipped DAG, build receipt and
  `…-source-audit-audit-receipt.json`) and
  `verification/manuscript-review/exact-ledger-receipt.json`,
  `exact-normal.log` and `exact-optimized.log`
  (= `…-exact-ledger-optimized-receipt.json`).
- *Third-party mathlib files* (6 outside the baseline): `pell-source.lean`
  (24, 26, 27), `pell-pinned-fetch.json` (24's audit, 26) and 26's
  `LICENSE.mathlib-Apache-2.0.txt`: mathlib4 commit
  `ac77769fabe23cb237559e7f56578dbead91499f`,
  `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256
  `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`, Git
  blob `6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e`, Apache-2.0. Not
  redistributed here; `26-repeated-target-dependencies-NOTICE.md`,
  `data/24-fixed-arity-science-sources-source-pins.json` and
  `data/27-unrestricted-stab-verification-dependency-pins.json` record the
  pin, and the file is at the URL in the article's bibliography
  (`mathlib-pell`).
- *Copies of this report's files* (5 outside the baseline): 24's
  `science/sources/report35-composition.md`, `report35-loader.md` and
  `report36-real.md`, and 27's `dependencies/report35-composition.md` and
  `report35-loader.md`, byte-identical to
  `22-literal-sandpiles-evidence-composition-PROOF.md`,
  `22-literal-sandpiles-evidence-loader-LOADER-PROOF.md` and
  `23-real-sandpiles-evidence-real-PROOF.md`.
- *Regenerable files of 26* (18): its polynomial DAG and its 17 page renders;
  see "Reconstructing the excluded data".

**Reconstructing the excluded data (26).** Both reconstructions were run
for this write on Windows (Python 3.14.4, MiKTeX's Poppler 24.04.0) and
reproduce the delivered bytes.

- `science/evidence/polynomial-dag.json` (1,064,332 bytes, SHA-256
  `7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6`),
  the authoritative object of 26's Theorem 1.1, pinned by its replay and
  auditors. In an empty directory outside the repository:

  ```sh
  cp "$REPO"/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/26-repeated-target-science-build_repeated_certificate.py .
  py 26-repeated-target-science-build_repeated_certificate.py
  ```

  It writes `evidence/polynomial-dag.json` (byte-identical; under a second)
  and `evidence/build-receipt.json`, equal to the shipped
  `data/26-repeated-target-science-evidence-build-receipt.json` after removing
  carriage returns (Windows writes CRLF). Alternatively
  `git show 0d7f51c44:docs/incoming/Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package.zip`
  and extract `science/evidence/polynomial-dag.json`.
- `verification/manuscript_audit/render/page-01.png` … `page-17.png`
  (3,958,546 bytes in all), renders of the unshipped PDF whose SHA-256 values
  are in the shipped `data/26-repeated-target-verification-manuscript_audit-visual-check.json`:

  ```sh
  git -C "$REPO" show 0d7f51c44:docs/incoming/Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package.zip > r53.zip
  unzip r53.zip Research_Report53.pdf
  pdftoppm -r 110 -png Research_Report53.pdf page
  ```

  This writes `page-01.png` … `page-17.png` in about 6 s; all 17 match the
  recorded hashes with Poppler 24.04.0 (another Poppler version may render
  different bytes).

## What is claimed and what is not

The report claims the theorems of the twenty-one manuscripts, with the proofs
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
impossibility theorems. For Part XIX: 21's coding bijection and growth
bounds, determinism and canonical costs, the cost-acyclicity lemma and
canonical quotient, the base quartic with its exact counts, degree and
ledger, the strict-abstraction lemma and closure adequacy, the counter and
interpreter correspondences, the universal-tree theorem (conditional on
the classical effective Turing simulation of weak call by value), the
charged fixed-universal corollary, the canonical singleton theorem with
its counts, the binary-sharing and exact-growth theorems for the fixed
program `R` (whose finite symbolic proof is checked by the shipped
programs, not printed in full), and the template-counting proposition. For Part XX: 22's loader theorem (with its automaton, circuit,
primitive, confinement, port, router and composition lemmas, the seed
coordinates, the halting-prism proposition and the coefficient algorithm),
its binary certificate theorem with least action, the exact ledgers and
the total-work corollary, and the worked example as finite data; 23's
real-exactness theorem with its three lemmas, the support and height
invariance, its ledger, the loader corollary and its counterexamples. The
moment identity, the shared schedules and the real-algebraic limit of
Part XX's review section are the research programme's results, cited
there, not claims of the manuscripts. For Part XXI: the four main theorems
(24–27) with their macro lemmas, geometry, recurrences, legality lemmas,
balance and carry bounds, the exact ledgers and the exact degree 18, the
separating examples, and the two conditional r.e.-completeness corollaries
(26, 27) under their stated imported hypotheses. Written in the merge, and
not claims of the manuscripts: the counterexamples to six printed passages
of Cairns's paper (`cdc:us:rem:cairns`, the manuscripts' arguments made
explicit and checked against arXiv:1508.00161v2), and the observation that
by `cdc:ro:rem:qelimit` none of the four accepted sets has a fixed-arity
representation with real/natural agreement. It does not claim the following. Each item is stated by at least the
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
  theorem are Part I's and Part VI's, printed with pointers. Batch 79,
  cluster J2: 21 makes no priority claim and implies no exhaustive novelty
  search (title page, Section 1.3); the Tree Calculus and its eager rules
  are Jay's and the weak call-by-value Turing simulation is Dal Lago and
  Martini's; its coding is Part VII's Cantor-pairing device in another
  alphabet and its inactive-field equations manuscript 04's activation
  device, printed with pointers.
- **Not formal.** No new Lean, Rocq or Coq proof was written or compiled,
  the repository's Lean build and axiom audits were not rerun, and
  repository documentation is not treated as a kernel audit (all twenty-one;
  16's MRDP axiom audit was not rerun, and its formalization route names
  "proposed module boundaries, not names of already implemented files").
  17 and 18 present formalization checklists only (17's Appendix B, 18's
  Section 12.3), and 17's citation of `DPR.lean` is "inspected, not
  rebuilt".
  The formalization sections of 08, 09, 10, 11 and 12 are likewise
  proposals; 12's five-layer Lean plan names no module as existing, and
  "none of these new layers has been kernel-checked".
  21 says that none of its theorems has been checked in a proof assistant
  (Section 12.1, `VERIFICATION.md`), and its question on mechanizing the
  semantic interface is a proposal.
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
  the Skolem or Positivity problems. 21's canonical family has one witness
  only at the exact DAG size and only over `ℕ`; it is "not a fixed-arity
  single-fold Diophantine representation and does not settle a single-fold
  MRDP problem", and the union over all `N` is a union of variable-arity
  formulas, not one polynomial.
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
  neither improves the 75/87 figures. 21's polynomials are families
  indexed by the external bound `N` on distinct calls, which no computable
  function of the input bounds on the universal domain (the article's note
  after its loader section, by `cdc:bd:prop:nobound`); its gate counts are
  unit-cost operations on integers that can be gigabytes long (the code of
  `U` has about 4.5·10¹⁰ bits, that of `R` more than 1.39·10¹²), and it
  claims no universal-polynomial size record.
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
- **21, scope.** The semantics is Jay's original eager Tree Calculus at
  `baa877d91`, not later dialects and not the equational quotient of his
  Coq files; results obtainable only by discarding an unevaluated
  divergent argument are not results. Environments are hereditarily
  finite and acyclic. The base fibres are not unique (padding, row
  permutations, inactive fields), and the canonical fibre is unique only
  over `ℕ` (not over the nonnegative reals) and at the exact size; it
  cannot be padded. Naturality is essential; no positive-only change of
  coordinates is supplied. Input loading (de Bruijn translation, quoting,
  compilation, coding) is a computable reduction, not an uncharged
  polynomial; no raw-integer loader or sequence codec is given. The codes
  of `U` and `R` were not materialized, and no scalar zero of the `R`
  family was evaluated; `R` is a terminating sharing example, not the
  universal interpreter. Gate counts use literal schedules and are not
  bit-operation bounds or optimality claims. Fuel exhaustion in the tests
  is recorded as inconclusive, not as divergence. The template-counting
  proposition counts instantiated template sets, not evaluator call
  sets in general. One evaluator method accepts non-natural inputs
  (found by the research tree's review; see Disclosures); no theorem
  depends on it.
- **22, scope.** Cairns's sandpile universality and the Neary–Woods
  machine are prior results; the construction is an explicit instance, not
  a new undecidability or universality theorem, and the arbitrary
  program-to-tape encoder is imported, not implemented. "Literal" means no
  unspecified choice remains, not that the object was stored: the dense
  period of about `1.9×10²⁷` entries, a universal routed-sandpile evolution
  and a giant-prism polynomial were not materialized, simulated, expanded
  or solved. Global halting means finitely many topplings in total. The
  prism bound holds where the run actually halts; there is no computable
  stopping bound in `n` alone, and candidate `(T,p)` arguments of the
  compiler certify nothing. Uniqueness holds per fixed prism, not across
  padded prisms; nonnegative real zeros can be spurious; the family has
  variable arity, so it is not one fixed-arity universal polynomial and not
  finite-fold MRDP. General nonbinary odometers are excluded (a singleton
  at height 12 needs two topplings). The total-work bound is about legal
  toppling work, not runtime, and is not optimal for all simulators. The
  ledgers count a specified straight-line model, not Python internals,
  memory or runtime; bounded record count is not constant bit space, and a
  collected stream's first record is not cheap. "Literal is not
  efficient." The research programme's review did not reconstruct the
  physical graph, routing seams, automaton tables, encoder or a giant
  prism, and Cairns's paper does not verify this particular graph. The
  composition audit did not re-audit the simulation, one-shotness, routing
  or background queries. Executable evidence is finite; hashes cannot
  authenticate a coordinated replacement; nothing is Lean-verified. 22's
  Theorem 3.5 (the certificate interface in Section 3.22) omits the input
  hypothesis "stable outside `P`", which holds automatically for the loader
  and is stated in a bracket and a note.
- **23, scope.** Exact zeros in the nonnegative real orthant only: not all
  of `ℝ^W`, not approximate zeros, no robustness, quantitative separation
  or numerical conditioning. The binary-odometer hypothesis is essential.
  No fixed-arity unbounded representation and no finite-fold MRDP. The
  rejected linear-programming branches have no independently checked
  Farkas certificates; they are solver-assisted regression evidence, not
  certified real infeasibility, and the theorem rests on the proof (the
  research programme found the searches unnecessary and did not rerun
  them). The independent ledger audit reads the compiler's affine
  summands and does no LP. No literature-wide priority, new general
  real/natural principle, new support-burning theorem, new universality
  theorem or Lean certification; the source comparison is bounded. It does
  not show that arbitrary one-hot encodings have natural magnitudes, and
  the variant `Q♯` does not keep the exact height. The `approved_base/`
  copy is predecessor context, not the full Report 35 archive;
  `evaluate_orthant` is exact only on integer and `Fraction` inputs. The
  prism bounds assume an actual halting run. Its `+2V` ledger is 22's
  convention; in the research programme's paid schedules the upgrade costs
  `V` additions, and the two are different conventions, not a
  contradiction. For positive coordinates `p = w+1` the theorem transfers
  to `p ≥ 1`, not to all `p > 0`. A fixed-arity universal compression
  cannot keep its real/natural existence equivalence (the programme's
  remark `cdc:ro:rem:qelimit`).
- **24–27, scope (all four).** Fixed arity means a fixed number of
  witnesses and gates for every input, box and duration, with witness
  values unbounded; the witness sets are infinite (padding, precision,
  empty layers, Pell quotients), so nothing is single-fold, finite-fold or
  unique, and no fixed-arity universal polynomial in the research
  programme's sense is given. Witnesses are strictly positive integers; the
  integer domain is essential, and nothing is claimed over the reals ("the
  same polynomial over unrestricted reals is not asserted to encode this
  relation"). The only external mathematical dependency is the pinned
  mathlib Pell characterization; Lean was not run and nothing is
  formalized. No count is optimal or minimal, gate ledgers count integer
  literals as free (a convention not comparable with Part XX's or the
  programme's), no literature-wide priority is claimed, finite tests
  corroborate and do not prove, and no full Pell/sandpile witness was
  materialized. No new universal loader, no paid raw-program-to-physical-code
  compiler; Report 35's loader, geometry and encoder stay inherited; not a
  bounded-time decision procedure; no effect on the 84-operation record.
  This is not Part XX's "fixed-arity universal polynomial" either: the
  article's sentence "Nothing here is a fixed-arity universal polynomial"
  in Part XX's setting is scoped to Part XX by a dated note.
- **24, scope.** The supplied stream may be a strictly larger supersolution
  than the odometer, so the certificate does not certify target firing;
  inputs that need repeated topplings (a height-12 singleton) are outside;
  the optional batched AND is not in the ledger; Cairns is cited for
  context, not as an audit of this graph. Its frozen
  `24-fixed-arity-science-PROOF.md` and `…-science-README.md` still say the
  audit is "in progress" (historical; the completed audit is
  `24-fixed-arity-independent_audit-AUDIT.md`).
- **25, scope.** Strictly narrower than unrestricted target firing (the
  `[12,4]` example); the endpoint need not be stable; the final stream is
  the odometer of an actual legal prefix, not maximal or stabilizing;
  applications to a loader need an all-site-one-shot proof and a target
  interpretation, which no loader in this report provides; Report 36's
  real exactness does not transfer. Its frozen architecture and source notes
  say review is "pending" (historical).
- **26, scope.** No novelty assertion; uniqueness of the count stream for
  fixed events is not uniqueness of witnesses; the corollary is an external
  computable composition, not among the 17,275 gates; its two corrections
  of Cairns are its readings ("not an author-issued erratum"; checked in the
  article); the fixed tile is not identified and is not Report 35's loader;
  Cairns's routing separations are not re-audited; the two-site tableaux of
  its tests use `b = 1024` at macro level, not full raw witnesses.
- **27, scope.** Finite global stabilization only (not target firing, not an
  infinite locally finite stabilization); `U` is not claimed least; no
  manageable witness sizes; the corollary is conditional on Report 35's
  loader and the inherited `U₁₅` universality; its Cairns corrections are
  "this review's mathematical readings" (checked in the article); no dense
  tile enumeration was performed.
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

**Reciprocal notes (batch 79, cluster J2).** The same cluster added Parts
III and IV to
[signal-machine-collision-certificates](../signal-machine-collision-certificates/)
(`smc:`, written in `bd8a8afd6` from batch-79 manuscripts 16 and 19, its
sources 12 and 13) and Parts IV–VI to
[quadratic-orthant-certificates](../quadratic-orthant-certificates/)
(written in `11abe5008` from batch-79 manuscripts 08, 09 and 18, its
sources 15, 16 and 17). Six dated notes of 2 October 2026 record the
relations here, without new labels, citing those reports' labels by name:
after the discussion that follows `cdc:of:thm:singlefoldsl` (Part XI; the
signal-machine report's Part III step packet `smc:cs:thm:packet` is an
explicit single-fold quadratic whose existence also follows from that
theorem, and its Part IV quartic `smc:sl:cor:fixedarity` is a degree-four
second route to it); after the example following `cdc:mem:lem:compare`
(Part V; the same Part IV re-derives the comparison gadget and the
two-field case of `cdc:mem:prop:comparator-cost`); after the paragraph that
follows `cdc:ex:gap` (Part II; the quadratic-orthant report's Theorem
`qoc:rn:thm:trace` generalizes `cdc:thm:main` with empty independence to
reset nets and makes every nonnegative real zero natural, where `P₂` is
convex with non-lattice real zeros); after `cdc:rx:thm:threshold` (Part
XIII; its Lemma `qoc:rn:lem:fuel` is the same theorem for reset nets, and
its peak certificate is a degree-two counterpart of `cdc:rx:thm:QL`); after
the question "Substrate-transfer theorems" (Part XIII; its Parts V and VI
are two more substrate instances, a literal membrane translation in the
opposite direction and an exact pump threshold measured in counter mass,
not tape span; the question stays open); and after Part XVI's question
"Local certificates on adaptive support geometry" (the signal-machine
report's Part IV pays the named costs for one-dimensional conservative
automata at size quadratic in the number of records; not answered). The
note on `cdc:q:ski` was written with Part XIX. No question of this report
is answered.

**Reciprocal note (batch 80, cluster K2).** The same cluster added Parts V
and VI to
[signal-machine-collision-certificates](../signal-machine-collision-certificates/)
(written in `ef114b0bb` from batch-80 manuscripts 10, 02, 05 and 03, its
sources 14–17). One dated note of 2 October 2026, without a new label,
follows the batch-78 note after `cdc:of:thm:classification` (Part XI): that
report's source 17 (batch-80 manuscript 03, not this report's manuscript
03) gives a natural-dynamics instance of the step from degree three to
degree four. A binary number-conserving cellular automaton of radius at
most six (`smc:fm:prop:rule`) hits an anchored pattern exactly at the times
`k² + (2d − 11)k` (`smc:fm:prop:hits`, `smc:fm:eq:hits`); with `d = 7 + x`
these are `k² + (2x + 3)k`, so the hit set `{(x, t)}` is not semilinear and,
by `𝒟⁺₃ = SL`, has no orthant-nonnegative representation of degree at most
three, while that report's squared quadratic `[k² + (2x + 3)k − t]²`
(`smc:fm:eq:quartic`) is a single-fold one of degree four. The dynamics,
the formula and the quartic are that source's; this report supplies only
the degree lower bound, as that report already says. No question of this
report is answered.

**Reciprocal note (batch 82, cluster M4).** Cluster M4 added source 18 and
Part VII to
[signal-machine-collision-certificates](../signal-machine-collision-certificates/)
(written in `9b3977008`). One dated note of 3 October 2026, without a new
label, follows the batch-79 note after the discussion of
`cdc:of:thm:singlefoldsl` (Part XI): that report's source 20 gives, in its
appendix section `smc:og:app:quartic` (`smc:og:thm:quartic`), a canonical
membership quartic for the visited set of a fixed input of mass at most
four, a second route at a higher degree to that theorem for those
semilinear sets, which that report credits here. No question of this
report is answered.

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

Manuscript 21 relies on no formal declaration and cites no ProveIt file.
Its compiler theorem borders the formal project
`Computability/CombinatoryLogic` (Lean and Rocq), which proves that
closed weak lambda calculus with context-closed beta reduction compiles
into pure SK, SKI and Iota by an occurs-aware bracket abstraction, the
idea of 21's safe optimization: `CombinatoryLogic.LambdaToSK.Polynomial.abstract`
and `CombinatoryLogic.LambdaToSK.Polynomial.abstract_correct`
(`Lean/CombinatoryLogic/LambdaToSK.lean`), `SKPolynomial.abstract` and
`SKPolynomial.abstract_correct` (`Coq/SKPolynomial.v`), with the headline
compilers `CombinatoryLogic.Universality.ski_turing_complete` and
`CombinatoryLogic.Universality.iota_turing_complete`
(`Lean/CombinatoryLogic/Universality.lean`). Those are forward
simulations, and that project does not claim reduction reflection; 21's
adequacy theorem has another target (Jay's eager Tree Calculus), another
source semantics (weak left-to-right call by value with closures, neither
the project's context-closed beta relation nor the call-by-value calculus
L of its Coq `RecursiveEquivalence`) and reflects termination. The
article's remark 230.3 (`cdc:et:rem:combinatory`) says so. No theorem of
21 is formalized in Lean or Rocq, it ships no Lean or Rocq file, and
placing it beside the formal projects confers no formal status on it.
The separately maintained research tree reviewed the archive:
`review_eager_tree_aebfa.md` (`3b5989da9`, indexed in
`incoming_substrate_review_aebfa386e.md`) finds no theorem-level defect,
checks the five rules against Jay's pinned Rust source, reproduces the
counts, the exact degree, the universal tree's bit interval and the
growth formulas, narrows the bit interval of `R` to
2,501,742,332,141–2,503,889,815,785, and supplies the patch
`eager_tree_exact_application_inputs.patch` for one evaluator input
defect (see Disclosures). That patch was never applied here; since batch 80
the shipped kernel is the archive's corrected edition, which repairs the
same defect in its own, equivalent code, and the tree's correction audit
`review_batch80_corrected.md` (`abfc0cb25`) confirms the repair, the
unchanged mathematics and a byte-for-byte fresh replay of its receipt. Do
not apply the patch to the shipped file: the repair is already there and
the hunk fails. Its review of the
placement (`review_placement_a7ae02511.md`, `653349f6a`) authenticates the
51 files placed by `a7ae02511` against the archive and supplies a portable stager,
`replay_placed_substrates_a7ae02511.py`, that restores the delivered
layout from Git. Four of those 51 files were replaced by corrected bytes in
the batch-80K1 placement. For an original-edition restoration, pass an
unchanged historical checkout (for example, a worktree at `a7ae02511`) as
`--repo`. Invoke the helper from a recent checkout, with its sibling
`placement_a7ae02511_inventory.json` beside it: neither file exists at
`a7ae02511`. A current corrected checkout passed as `--repo` stops with
"Placed source differs". For the corrected layout extract the batch-80 archive.
These launch instructions were corrected on 2 October 2026 from the
programme's README-only patch `batch80_historical_stager_launch.patch`
(applied verbatim), written by its review
`review_batch80_correction_publication_86267b8a3.md` (commit
`fbad71e8c`), which otherwise passes the batch-80K1 corrected-code update
of this README and article (through `c8d3ff5cb`) and leaves the earlier
exact-size and base-case qualifications of Part XIX outside its verdict.

**Relations (batch 79, cluster J2).** Part XIX answers in part, for
another calculus, Source 01 of `cdc:q:ski` (a validity-free coding, a
strategy-specific reflection theorem and a canonical unique-witness
certificate at exact size, for Jay's Tree Calculus rather than SKI or
Iota) and only touches its Source 04 (it avoids schedules); a dated note
after the question records this. Its first question restates the
research target that Part VII names after `cdc:wf:prop:ski-height`, and
its binary-sharing theorem is a partial step towards it for one fixed
program. Notes in the Part point to Part VII's coding and scheduled
compiler, Part V's graph evaluator and sharing remark, manuscript 04's
activation lemma and Part IX. No neighbouring report was edited in this
write.

Manuscripts 22 and 23 rely on no formal declaration and cite no Lean or
Rocq file. Their certificate is a cubic of Part XVI's kind; MRDP
(`Diophantine.mrdp`) is context only, and no theorem of Part XX is
formalized in Lean or Rocq. Placing the Part beside the formal project
confers no formal status on it. The separately maintained research tree
reviewed both archives before placement (`review_sandpile35_36_intake.md`,
`c120b34df`) and added `sandpile_shared_arithmetic35_36.md` with its
independent review `review_sandpile_shared_arithmetic35_36.md`, both in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
and summarized in the project README; the article's Part XX records every
finding (`cdc:sec:b83-review`). Its least universal Diophantine polynomial
stays at 84 operations (`20aafb9a5`); Part XX changes nothing there.

**Relations (batch 83, cluster H1).** Part XX answers in part manuscript
16's question "A verified universal periodic input loader" (a literal,
audited, not formally verified loader for `U₁₅`, with the encoder
imported) and manuscript 19's `cdc:nb:q:formal`, and answers in part
manuscript 16's question on coefficient and operation ledgers; it touches
16's question "Fewer witnesses without losing uniqueness" and 19's
`cdc:nb:q:smaller` (binary odometers only), and bears on 16's question on
fixed-arity compression (the review's real-algebraic limit). Dated notes
after those six questions say so. 23 credits Part VI of
*quadratic-orthant-certificates* (`qoc:rn:lem:gates`, `qoc:rn:thm:trace`)
for the real one-hot principle; the machine is that report's `U_{15,2}`
and that of *group-theoretic-substrates* Part V (written in `134dfc0c8`
after this Part), with the same imported encoder. No neighbouring report
was edited in this write; the batch-83 reciprocal notes (3 October 2026)
are dated notes in those two reports, after `qoc:rn:prop:realobstruction`
and in the relation list of *group-theoretic-substrates*.

**Reciprocal note (batch 83, cluster H2).**
[periodic-turmite-first-revisits](../periodic-turmite-first-revisits/)
(Report 38, labels `ptr:`): its open question 3 asks for the turmite
analogue of Part XX's literal periodic loader and acceptance event, and its
Corollary 12.1 (`ptr:cor:universality`) is the matching lower side for
globally one-visit turmite runs. No shared theorem. A dated item in Part
XX's "Relation to the other Parts" list records it, without a new label.

**Reciprocal notes (batch 88, 3 October 2026).**
[periodic-turmite-first-revisits](../periodic-turmite-first-revisits/)
now answers that question 3 in its Parts II–IV (Research Reports 40, 42, 44,
47, 48; written in `119a1325d`; labels `ptr:la:`, `ptr:ai:`, `ptr:pc:`,
`ptr:sc:`, `ptr:fu:`): a literal periodic Langton ant for the same U15 with
a finite loader, at most two visits per cell and an iff residue-and-heading
port (Theorem 40.1.1, `ptr:la:thm:interface`), the sharp one/two-visit
boundary (Corollary 40.1.2, `ptr:la:cor:boundary`), and one fixed positive
polynomial for the fixed U15 sentinel-pair halting language through the ant
(Theorem 44.1.1, `ptr:pc:thm:complete`; 465 witnesses, exact degree
2,304,000; 14,658,934 operations from the literals 1 and 3, 14,620,711 in
the programme's later packets). It is the turmite analogue of Part XX's
construction, with its own 32-state encoding of U15 rather than Part XX's
34-state lazy CA and with the program-to-tape encoder imported in both; it
is not an ordinary-input loader in the programme's sense, and there is no
shared theorem. A second dated item in Part XX's "Relation to the other
Parts" list records it; the batch-83 item stays as written.
[fixed-universal-polynomials](../fixed-universal-polynomials/) (Parts
VI–VIII, written in `85ea6145d`) tabulates the candidates below the
84-operation record in its Table 3 and prints the refutations of the
first-index deletions (Part VII) and of the free-coefficient 83 and
square/product 82 candidates (Part VIII); a dated note in Part XX's
paragraph "No effect on the universal bound" points there. Neither note
adds a label, macro, package or bibliography entry.

**Formal status and relations (batch 91, cluster A).** Manuscripts 24–27
rely on one external formal statement, mathlib's constructive Pell
characterization (`Pell.matiyasevic`, `Pell.eq_pow_of_pell` at mathlib4
`ac77769f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256
`993760c7…`, blob `6ede8ed6…`), whose Lean proof they did not run; this
repository's Lean development uses the first theorem in
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Cor26.lean`.
Their binary containment `Sub` is the Jones–Matiyasevich masking, which the
project formalizes as `JM1984.mask_iff_choose_odd`
(`Lean/Diophantine/Paper1984/Masking.lean`) and `JM1984.Exp.SFU.mask`
(`Lean/Diophantine/Paper1984/ExpPrim.lean`); the manuscripts' own equation
system for it, their 15-equation `POWER` specialization and every theorem of
Part XXI are not formalized. Placing the Part beside the formal project
confers no formal status on it. The research tree reviewed the four
archives before placement (`review_new_sandpiles_0d7f51c44.md`,
`bc6e1a62c`); its least universal polynomial stays at 84 operations.
Relations: Part XXI answers Part XX's `cdc:ro:q:packing` (24, extended by
27), touches `cdc:lp:q:encoder`, `cdc:q:compression` and manuscript 16's
question on fixed-arity compression (fixed arity without multiplicity
control), and re-proves least action (`cdc:sp:lem:leastaction`,
`cdc:nb:lem:least`, `cdc:lp:lem:leastaction`) as marked second routes; dated
notes after those questions and in Part XX's setting paragraph say so. Its
`POWER` macro is Lemma `ptr:ai:lem:exp` of
[periodic-turmite-first-revisits](../periodic-turmite-first-revisits/)
(Part III, Report 42), credited in a note; the reciprocal note there is
described below. No neighbouring report was edited in this write.

**Reciprocal notes (batch 91, 4 October 2026).** One dated note here, after
the note that follows `cdc:fx:lem:subset`:
[group-theoretic-substrates](../group-theoretic-substrates/), Part VI
(Research Report 55, written in `b93c4a0b5`), uses the same expanded
containment system (three `POWER` calls, the extraction equation and the
two strict slacks) in its fixed-arity certificate for the research
programme's five-register matrix countdown, and proves `cdc:fx:lem:subset`
again as `gts:cm:lem:sub`; neither text cites the other, and its packing
review read the source notes of manuscript 26's packet
`sandpile-repeated-target-20261004` as data. In the other direction,
[periodic-turmite-first-revisits](../periodic-turmite-first-revisits/)
gains a dated note after `ptr:ai:lem:exp` naming the `POWER` macro of
manuscripts 24–27 (and of group-theoretic-substrates Part VI and
signal-machine-collision-certificates Parts X–XIII), and
[fixed-universal-polynomials](../fixed-universal-polynomials/) a dated
paragraph in its Section 0.5 saying that the r.e.-complete polynomials of
`cdc:rp:cor:recomplete` and `cdc:us:cor:hardness` are not ordinary-input
universal polynomials and do not bear on the 84-operation record. No note
adds a label, macro, package or bibliography entry. The note here leaves
the build at 742 pages with the same clean log and the same single
underfull line, and every `.aux` label number unchanged against a build of
the committed text; it moves the material of printed pages 644–659
(Sections 265–284) one page later, and later pages are unchanged.
Its page (printed 644) was rendered and inspected.

## Build

pdfLaTeX, with the packages loaded in `article.tex` (base 05's preamble
plus `float`, and since batch 62 `fancyvrb`, `tikz` and `etoolbox`:
fontenc, inputenc, amsmath, amsthm, mathtools, newtxtext, newtxmath,
geometry, microtype, booktabs, array, longtable, tabularx, float, xcolor,
enumitem, listings, fancyhdr, titlesec, tcolorbox, xurl, hyperref, aliascnt,
cleveref, fancyvrb, tikz and etoolbox; `etoolbox` only widens the section
numbers in the contents, which reach three digits). The two diagrams (Parts XI and XIII) and, since batch 83, three in Part XX are drawn in TikZ in the
source. The bibliography is internal; no BibTeX, external figures or
downloads are needed. Build in a scratch copy, so that no auxiliary file
lands in the collection:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build has 742 pages (196 before batch 62, 306 before batch 63,
338 before batch 78, 419 after Part XV, 449 after Part XVI,
451 after the reciprocal notes, 452 after restoring the XVI organization row,
509 after Part XVII, 571 after manuscripts 19 and 20, 605 after Part XIX, 607 after the batch-79 reciprocal notes, 608 after the batch-80 correction notes, still 608 after the batch-80 reciprocal note, 652 after Part XX, still 652 after the batch-82 reciprocal note and after the batch-83 reciprocal note, 742 after Part XXI, still 742 after the batch-91 reciprocal note),
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

Part XIX (batch 79, cluster J2) adds eight macros (`\Leaf`, `\Stem`,
`\Fork`, `\Apply`, `\FV`, `\ev`, and `\tcode` and `\clos` for 21's
`\code` and `\cl`, which would clash with this report's) and no package
(21's `amssymb`, `lmodern`, `multicol` and `bookmark` are not needed).
Built in a scratch directory with
`latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX,
pdfTeX): 605 pages, no errors, warnings, undefined references or
citations, multiply defined labels, duplicate destinations or overfull
boxes, and the same single underfull line as before. Layout-only change:
the Lean and Rocq declaration names in the written remark print with
`\path` so that they can break. The title page, Section 3.21, the
question `cdc:q:ski` with its note, the opening and conventions of Part
XIX and the universal-tree table were rendered and inspected.

The batch-79 reciprocal notes of cluster J2 (six dated notes, no label, no
macro, no package) add two pages: 607 pages, with the same clean log (no
errors, warnings, undefined references or citations, multiply defined
labels, duplicate destinations or overfull boxes) and the same single
underfull line. Every label and bibliography number is unchanged (the
`.aux` of a build of the previous text compared, 3132 `\newlabel` entries).
The pages with the notes after `cdc:ex:gap` and after the question on
adaptive support geometry were rendered and inspected.

The batch-80 notes of cluster K1 (the corrected code edition of manuscript
21: two dated notes, updated sentences and one bibliography entry; no
label, macro or package) add one page: 608 pages, with no errors,
warnings, undefined references or citations, multiply defined labels,
duplicate destinations or overfull boxes, and the same single underfull
line. Every label and every earlier bibliography number is unchanged (the
`.aux` of a build of the previous text compared, 3132 `\newlabel`
entries; `repo-b80rev` is item 99). The pages with the new note in
`cdc:et:sec:reproduce`, the note after the artifact index, the provenance
table and the bibliography were rendered and inspected.

The batch-80 reciprocal note of cluster K2 (one dated note after
`cdc:of:thm:classification`; no label, macro, package or bibliography
entry) keeps the build at 608 pages; it moves later material in Sections
90–98 one page on (59 `\newlabel` page fields change), and the shift is
absorbed within Part XII. The build has no
errors, warnings, undefined references or citations, multiply defined
labels, duplicate destinations or overfull boxes, the same single
underfull line, and the same thirteen "Infinite glue shrinkage" messages
as a rebuild of the previous text in the same environment. Every label
and bibliography number is unchanged (the `.aux` of that rebuild
compared, 3132 `\newlabel` and 99 `\bibcite` entries). The page of the
note (page 260) was rendered and inspected.

Part XX (batch 83, cluster H1) adds fifteen macros (`\FL`, `\FR`, `\AND`,
`\OR`, `\WIRE`, `\FORK`, `\htcoef`, and `\Ufift`, `\bitset`, `\Qreal`,
`\rlo`, `\rneg`, `\req`, `\rpos`, `\rhi` for 22's `\U` and `\bits` and
23's `\QR`, `\lo`, `\negc`, `\eqc`, `\pos` and `\hi`, of which `\bits` and
`\pos` would clash with this report's) and no package (22's TikZ
libraries `arrows.meta` and `positioning` are already loaded; `lmodern`,
`amssymb` and `tocloft` are not needed). Its three TikZ diagrams are 22's
Figures 1–3, printed as Figures 3–5. Built in a scratch directory with
`latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX,
pdfTeX): 652 pages, no errors, warnings, undefined references or
citations, multiply defined labels, duplicate destinations or overfull
boxes, and the same single underfull line as before; there are fourteen
"Infinite glue shrinkage" messages, one more than in a rebuild of the
previous text, from Part XX's conventions longtable. Every earlier label
keeps its number and type, and every earlier bibliography number is
unchanged (the `.aux` of that rebuild compared, 3132 `\newlabel` and 99
`\bibcite` entries); one entry is retitled (`cdc:sec:manuscripts`, now
"The twenty-three manuscripts"), and the hyperlink anchors of two
unnumbered paragraphs (`cdc:pt:subsec:repo`, `cdc:conv:b62q`) moved,
because the conventions gained the paragraph "Part XX". The eight new
bibliography entries are items 100–107. Layout-only changes: the
horizontal unit of 22's shutdown diagram (Figure 4) is narrowed from
.038 cm to .035 cm so that it fits the text width, and the first-column
entries of the conventions table are split into separate formulas so that
they can break. The title page, Sections 3.21–3.23, the opening and
conventions of Part XX, Figure 4, the review section with its table, the
provenance list and the bibliography were rendered and inspected.

The batch-82 reciprocal note (one dated paragraph in Section 90.4.2, after
the batch-79 note following `cdc:of:thm:singlefoldsl`; no label, macro,
package or bibliography entry) leaves the build at 652 pages, with no
errors, warnings, undefined references or citations, multiply defined
labels, duplicate destinations or overfull boxes and the same single
underfull line; the log has seventeen informational "Infinite glue
shrinkage" messages (fourteen were recorded for the Part XX build; no
rebuild of the previous text was compared). Its page (printed page 271)
was rendered and inspected.

The batch-83 reciprocal note (one dated item in Part XX's "Relation to the
other Parts" list, on `periodic-turmite-first-revisits`; no label, macro,
package or bibliography entry) leaves the build at 652 pages with the same
clean log, the same single underfull line and seventeen "Infinite glue
shrinkage" messages; its page (printed page 587) was rendered and inspected.

The batch-88 reciprocal notes (3 October 2026; a second dated item in Part
XX's "Relation to the other Parts" list, on Parts II–IV of
`periodic-turmite-first-revisits`, and a dated addition to Part XX's
paragraph "No effect on the universal bound", on Table 3 and Parts VII–VIII
of `fixed-universal-polynomials`; no label, macro, package or bibliography
entry) leave the build at 652 pages with the same clean log, the same single
underfull line and seventeen "Infinite glue shrinkage" messages, compared
with a build of the committed text. Every `.aux` label number is unchanged;
the item moves Part XX's material from printed page 588 to 621 by one page,
which the end of Part XX absorbs (40 labels change page). Its pages (printed
pages 587–588) and that of the second note (620) were rendered and
inspected.

Part XXI (batch 91, cluster A) adds nine macros (`\POWER`, `\Sub`,
`\BitAnd`, `\Spread`, `\Geom`, `\Pos`, `\Input`, `\Prestr`, `\Avail`; the
manuscripts' `\Pow`, `\AND` and `\Pre` would clash with this report's) and
no package (27's `seqsplit` and `needspace` are not needed: hashes print
with `\path`, and its one `\Needspace` is dropped; 24's and 25's `xurl`,
`enumitem` and `longtable` are already loaded). Built in a scratch
directory with `latexmk -pdf -interaction=nonstopmode -halt-on-error
article.tex` (MiKTeX, pdfTeX): 742 pages, no errors, warnings, undefined
references or citations, multiply defined labels, duplicate destinations or
overfull boxes, and the same single underfull line; there are 22 "Infinite
glue shrinkage" messages, five more than in a rebuild of the committed
text, from Part XXI's longtables. Compared with that rebuild (3,008
`\newlabel` and 107 `\bibcite` entries), every earlier label keeps its
number and type and every earlier bibliography number is unchanged; one
entry is retitled (`cdc:sec:manuscripts`, now "The twenty-seven
manuscripts"), and the hyperlink anchors of the two unnumbered paragraphs
`cdc:pt:subsec:repo` and `cdc:conv:b62q` moved, because the conventions
gained the paragraph "Part XXI". The thirteen new bibliography entries are
items 108–120. Two `\code{…/PellMatiyasevic.lean}` paths of 26 and 27 print
as breakable `\path` (layout only). Rendered and inspected: the title page
and page 2, Sections 3.23–3.24 (printed pages 75–78), the end of Part XX
with the dated note after `cdc:ro:q:packing` (634–635), the opening of Part
XXI with its table (636–637), the pointer sections of manuscript 25 (657),
24's questions and Appendix A with its table (655), the review section with
its table and the Cairns section (704–705).

## Rerunning the checks

Every suite needs Python 3.10 or later and the standard library only,
except 16's three verifiers, which need SymPy 1.14.0
(`data/16-sandpile-requirements.txt`; the recipe uses `uv`), and the
three optional symbolic stages of 21 (SymPy, `data/21-eager-tree-requirements-optional.txt`). Every
suite rewrites its recorded outputs at fixed paths relative to its own
location, and most scripts import their siblings by delivered name, so run
them **on a copy with the delivered layout**, never in the report
directory. The recipes below build such copies, `r01` … `r21`, beside
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

# 21: rewrites the 26 JSON files and the S-expression in r21/code, and writes r21/replay-output/
mkdir -p r21/code
for f in code/21-eager-tree-*.py; do cp "$f" "r21/code/${f#code/21-eager-tree-}"; done
for f in data/21-eager-tree-*; do cp "$f" "r21/code/${f#data/21-eager-tree-}"; done
mv r21/code/reproduce.py r21/code/build_pdf.py r21/code/sources.json r21/code/requirements-optional.txt r21/
(cd r21 && py reproduce.py)
# optional: also the three SymPy stages
(cd r21 && uv run --no-project --with sympy==1.14.0 python reproduce.py --symbolic)
```

**Part XX (22 and 23).** These need, besides `code/` and `data/`, the
`22-*` and `23-*` files at the report root in the scratch copy, and three
files that are not shipped as such. Save the following as `restore83.py`
in the scratch copy; it rebuilds the delivered layout in `r22` and `r23`:

```python
import pathlib, shutil, sys
DIRS = {'evidence', 'composition', 'review', 'loader', 'ca', 'compiler', 'gates', 'geometry', 'verification', 'real'}
for prefix, out in (('22-literal-sandpiles-', 'r22'), ('23-real-sandpiles-', 'r23')):
    for d in ('.', 'code', 'data'):
        for f in pathlib.Path(d).glob(prefix + '*'):
            parts, rest = [], f.name[len(prefix):]
            while '-' in rest and rest.split('-', 1)[0] in DIRS:
                head, rest = rest.split('-', 1)
                parts.append(head)
            dest = pathlib.Path(out, *parts, rest)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, dest)
pathlib.Path('r22/evidence/loader/data').mkdir()
shutil.copy2(sys.argv[1], 'r22/evidence/loader/data/u15_table.json')
pathlib.Path('r23/evidence/real/approved_base').mkdir()
for n in ('PROOF.md', 'prism_certificate.py'):
    shutil.copy2('r22/evidence/composition/' + n, 'r23/evidence/real/approved_base/' + n)
```

Then, with `REPO` the repository checkout and the scratch copy beside
`quadratic-orthant-certificates` (or pass that report's machine table by
its full path):

```sh
# 22 and 23: run in a scratch copy of the report directory that holds code/, data/ and the 22-*/23-* root files
py restore83.py ../quadratic-orthant-certificates/data/16-universal-membrane-tm_table.json
git -C "$REPO" show 3051d1446:docs/incoming/Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip > r35.zip
unzip -p r35.zip Research_Report35/evidence/loader/FROZEN-INPUTS.json > r22/evidence/loader/FROZEN-INPUTS.json
# 22, composition first: these producers print their receipts and check the hashes of the loader files
(cd r22/evidence/composition && py test_prism_certificate.py > verification.json \
  && py literal_composition.py > example_hypothetical_bound.json \
  && py review/audit_independent.py > review/audit_independent_results.json \
  && py review/audit_polynomial.py > review/audit_ledger.json \
  && py review/audit_crosscheck.py > review/audit_crosscheck_results.json \
  && py review/audit_streaming.py > review/audit_streaming_results.json \
  && py review/audit_adapter.py > review/audit_adapter_results.json)
# 22, loader: rewrites its six receipts in place
(cd r22/evidence/loader && py gates/check_gates.py && py ca/test_lazy_u15.py \
  && py geometry/periodic_router.py --output geometry/router_checks.json \
  && py compiler/literal_loader.py --audit && py compiler/test_coefficients.py && py compiler/make_example.py)
# 23: rewrites its two receipts in place (the first needs SymPy 1.14.0)
(cd r23/evidence/real && uv run --no-project --with sympy==1.14.0 python exact_checks.py --output verification.json \
  && py independent_coefficient_ledger_checks.py --output independent_coefficient_ledger_receipt.json)
```

**Part XX (22 and 23).** The replay plans
`data/22-literal-sandpiles-verification-replay-plan.json` and
`data/23-real-sandpiles-verification-replay-plan.json` list every producer
with its working directory, arguments, receipt and whether the receipt is
a file or captured stdout (the seven composition producers print their
receipts, and the recipe redirects them to the receipt paths). The
preferred route is the delivered one, on a POSIX host: extract both
archives from the arrival commit
(`git show 3051d1446:docs/incoming/<archive>.zip`, outside the repository)
and run, in each extracted `Research_Report35/` or `Research_Report36/`,
`python3 verify_release.py --verify-only` and `python3 verify_release.py
--replay` (23 with `-I -B` and SymPy 1.14.0 installed); the wrapper runs
every producer in disposable copies, normal and optimized, and compares the
receipts. It cannot run in this repository or on a Windows file system:
it needs the unshipped manifests and POSIX modes. The recipe above is the
alternative on any host, without the wrapper: it restores the delivered
layout from the shipped files, adds the three unshipped files the programs
read (the machine table from *quadratic-orthant-certificates*, 23's
`approved_base/` pair from 22's shipped composition files, and 22's
loader `FROZEN-INPUTS.json` from the archive), and runs the producers. In
the write it was run on Windows (Python 3.14.4; SymPy 1.14.0 through `uv`
for 23): every producer passed and every regenerated receipt equals the
shipped one after removing carriage returns (all 15 receipts, under three
minutes in all). **Hazards:** run the composition producers before the loader
producers or on a fresh copy, because on Windows the loader producers
rewrite their receipts with CRLF, after which the composition producers
stop with "frozen loader file changed"; without the restored
`FROZEN-INPUTS.json` they stop at once. Every producer overwrites its
receipt in place, so run them only in `r22` and `r23`. Do not run
`code/22-…-build_pdf.py` or `code/23-…-build_pdf.py` (they compile the
unshipped `Research_Report35.tex`/`Research_Report36.tex`), the
`archive_*.py` and `seal_release.py` tools, or `tamper_regression.py`
here. `lazy_u15.py --rules-jsonl` regenerates the rule stream, not
byte for byte (see Files).

**Part XXI (24–27).** The four packages read and write by their delivered
paths, and their release verifiers (`code/24-fixed-arity-verify_release.py`,
`code/25-binary-target-verify_release.py`, `code/26-repeated-target-release.py`,
`code/27-unrestricted-stab-release.py`) check the release manifests,
including POSIX file modes, so none of them can run in this repository. Run
them on a fresh extraction of the arrival archives, outside the repository
(the preferred route, on a POSIX host, follows the delivered READMEs:
`python3 -I -B verify_release.py --manifest-sha256 "$PIN" --verify-only`
and `--output <new dir>` for 24, `python3 -I verify_release.py
--manifest-sha256 <pin>` and `audit_replay/replay_audits.py` for 25,
`python3 -I release.py verify --manifest-sha256 <pin>` and
`audit_replay/replay_audit.py --output <new dir>` for 26 and 27, with the
trusted manifest digest taken from the archive itself, since this report
ships the manifests but no separate digest). The direct route below was run
for this write on Windows (Python 3.14.4) on fresh extractions:

```sh
# in an empty scratch directory outside the repository
for a in A_Fixed_Arity_Integer_Certificate_for_Binary_Sandpile_Stabilization_Package \
         Finite_Legal_Binary_Target_Firing_in_Periodic_Sandpiles_Package \
         Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package \
         Unrestricted_Finite_Global_Sandpile_Stabilization_Package; do
  git -C "$REPO" show 0d7f51c44:docs/incoming/$a.zip > $a.zip && unzip -q $a.zip -d $a
done
# 24 (its files are under Research_Report50/)
(cd A_Fixed_*/Research_Report50 && py -I -X utf8 science/build_certificate.py --output science/evidence \
  && py -I -X utf8 science/check_source.py && py -I -X utf8 science/check_exact_degree.py \
  && py -I -X utf8 science/periodic-input/check_periodic_packing.py \
  && py -I -X utf8 science/stream-products/verify_and_spread.py \
  && py -I -X utf8 science/stream-products/verify_mask_subset.py \
  && py -I -X utf8 audit_replay/replay_independent_audit.py --source-root science \
       --audit-root independent_audit --output "$PWD/../../out24")
# 25
(cd Finite_* && py -I -X utf8 science/build_target_certificate.py && py -I -X utf8 science/check_target_certificate.py \
  && py -I -X utf8 audit_replay/replay_audits.py --source-root science --audit-root independent_audit --output "$PWD/../out25")
# 26 (the semantic probes take about 16 s)
(cd Repeated_* && py -I -X utf8 science/build_repeated_certificate.py && py -I -X utf8 science/check_repeated_semantics.py \
  && py -I -X utf8 science/recurrence-review/check_recurrence.py)
# 27
(cd Unrestricted_* && py -I -X utf8 science/build_stabilization.py && py -I -X utf8 science/check_semantics.py \
  && py -I -X utf8 science/math-audit/check_math.py)
```

Results: every builder rewrites its polynomial DAG byte for byte (24, 25,
26 and 27; 26's is the one this report does not ship), and every program
passes; each rewritten receipt equals the shipped one after removing
carriage returns, which the Windows text-mode writers add. The two audit
replays (24's `replay_independent_audit.py`, 25's `replay_audits.py`)
regenerate their receipts and logs equal, up to CRLF, to
`data/24-fixed-arity-audit_replay-evidence-replay-scientific-receipt.json`
and to `data/25-binary-target-audit_replay-evidence-audit-receipt.json` and
`…-semantics-receipt.json`; on Windows they then stop with "receipt differs
from the frozen receipt" or "Main scientific receipt changed", because they
compare bytes, and 25's refuses to run without `python -I`. 26's and 27's
`audit_replay/replay_audit.py` match their historical POSIX paths by
string and stop on Windows ("Unapproved checker read"); the placement
session ran them through a path-normalizing shim (not shipped) and got all
three receipts of each byte for byte, and on a POSIX host they run as
delivered. Not run: the release verifiers and archive and PDF tools (POSIX
modes, TeX Live byte identity), the replay safety harnesses
(`code/24-fixed-arity-audit_replay-test_replay_runner.py`, whose isolated
children hit Python's cp1252 default on Windows, and 25's
`test_replay_adapter.py`), and
`code/26-repeated-target-science-source-review-check_source.py`, which reads
hard-coded `/workspace/shared/…` paths. **Hazards:** every builder and
checker overwrites its receipt in place, so run them only in an
extraction, never in this directory; `-X utf8` avoids the cp1252 failures
of child processes on Windows.

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
patch applied. The recipe for 21 was run the same way in the batch-79
cluster-J2 write (Python 3.14.4, Windows; about 20 seconds, and 34 with
the symbolic stages and `uv` start-up): all 16 stages (19 with
`--symbolic`) pass, "All requested checks passed". All 27 regenerated files
equal the shipped ones after removing carriage returns, except six
receipts (`audit_exact_count_receipt`, `constant_bit_bound`,
`exact_growth_receipt`, `independent_growth_receipt`,
`independent_shared_receipt`, `packet_assumptions_receipt`), which differ
only in `*_sha256` fields that hash `shared_symbolic_proofs.json`,
`shared_compression_program.json` or `literal_universal_tree.json` as
rewritten on Windows with CRLF line endings; the shipped values
(`0341fdac…`, `f136280b…`, `c6b64709…`) are the hashes of the LF files.
On POSIX, or with Python writing LF, those fields agree too. Alternatively,
extract the delivered archive into a scratch directory
(`git show aebfa386e:docs/incoming/Eager_Tree_Calculus_Research_Package.zip > et.zip`,
unzip, `cd eager-tree-certificates`) and run `py verify_manifest.py` (55
entries) **before** `py reproduce.py`; this was also tested (about 33
seconds, all 16 stages pass). The research tree's review reports the same
outcome, with all 19 stages, for the original and for its patched copy.
Batch 80 (corrected edition): the `r21` recipe, run unchanged on a scratch
copy of the shipped files after the replacement (Python 3.14.4, Windows;
about 20 seconds), runs 17 stages, the regression suite first, and prints
"All requested checks passed"; of the 27 regenerated files, 21 equal the
shipped ones after removing carriage returns, including `receipt.json` and
`independent_receipt.json` with the corrected kernel's hash `636ce7fe…`,
and the same six receipts as above differ only in their CRLF hashes. In
the batch-80 placement check, `reproduce.py --symbolic` under Python
writing LF ran all 20 stages and regenerated all 27 files byte for byte.
`py code/test_application_domain.py --kernel <file>` passes on the shipped
kernel and on the batch-79 kernel with the review's patch, and fails on
the batch-79 kernel (`git show a7ae02511:<path of code/21-eager-tree-tree_kernel.py>`)
with 29 failures and 36 errors, as `21-eager-tree-CORRECTION.md` states.
The archive route for the corrected edition (`4e270aa46`) is the same;
there `verify_manifest.py` checks 57 entries.

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
- Batch 79, cluster J2: 21's `reproduce.py` runs every stage with
  `code/` as working directory, and the stages rewrite their fixtures and
  receipts there; it also writes `replay-output/` beside itself. Run it
  only inside `r21` (or in an extracted archive). The shipped
  `code/21-eager-tree-*` programs that import a sibling (`tree_kernel`,
  `eager_compiler` and others) fail at that import, because the siblings
  carry prefixes, and `code/21-eager-tree-reproduce.py` finds no
  `code/` below itself. On Windows the regenerated files have CRLF line
  endings, so six receipts record different self-hashes (see above), and
  `verify_manifest.py` then reports a digest mismatch: run it before the
  replay. Do not run `code/21-eager-tree-build_pdf.py`: it creates
  `build/` beside itself and runs `pdflatex` three times on
  `eager-tree-certificates.tex`, which is not shipped. The delivered
  texts write `python3`, which may not resolve on Windows; use `py`.
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
- **Batch 79, cluster J2 (manuscript 21): shipped text that uses delivery
  names or names unshipped files.** `21-eager-tree-VERIFICATION.md`
  describes "the release", runs `python3 reproduce.py --symbolic`, says
  that the LaTeX source builds and that all 30 rendered pages were
  inspected (the source and PDF are not shipped; they survive in
  `aebfa386e`), and says that receipts are written beside the scripts and
  logs into `replay-output/`. `code/21-eager-tree-reproduce.py` runs
  `code/<stage>.py` by delivered name; `code/21-eager-tree-build_pdf.py`
  compiles `eager-tree-certificates.tex`. The programs import each other
  and read and write their fixtures by delivered names in their working
  directory. `data/21-eager-tree-sources.json` says that no upstream code
  is bundled. Six receipts record SHA-256 hashes of the delivered LF
  files `shared_symbolic_proofs.json`, `shared_compression_program.json`
  and `literal_universal_tree.json` (shipped with prefixes;
  byte-identical). The article prints the shipped names in notes where 21
  names its files and keeps its artifact index in the delivered names.
  Batch 80: `21-eager-tree-CORRECTION.md` uses the delivered names
  (`code/tree_kernel.py`, `code/test_application_domain.py`,
  `code/receipt.json`, `MANIFEST.sha256`), runs `python3` from the
  extracted `eager-tree-certificates/` directory, and names the
  unshipped `verify_manifest.py` and ledger;
  `code/21-eager-tree-test_application_domain.py` imports the sibling
  `tree_kernel.py` by delivered name unless `--kernel` is given; the new
  `reproduce.py` stage runs `code/test_application_domain.py`.
- **Batch 79, cluster J2: renamings and notes in the printed text.** 21's
  `\code` (the coding map) is typeset with `\tcode` and its `\cl` (a
  closure) with `\clos`, with unchanged glyphs; its `\file` is this
  report's `\code` (the same definition) and its `\eqtag` is written
  out; "Appendix A" references carry the section number (236); its
  numbered research directions are question environments. Its closing
  remark alludes to "earlier canonical and scheduled SKI certificate
  constructions" without a reference; a note names Part VII's
  `cdc:wf:thm:ski` and Part V's `cdc:mem:cor:graph`. Its interval
  1,390,419,544,301–4,688,954,427,625 for the bit length of `code(R)`
  (and so the constant `B_*`) is valid but loose: the research tree's
  review obtains 2,501,742,332,141–2,503,889,815,785 with exact codes up
  to 4096 bits, and the placement dossier's own propagation (exact up to
  4096 bits, then the cruder fork rule) gives 2,501,742,332,141–2,506,037,299,433; a
  note prints the review's interval beside the manuscript's unchanged
  numbers, and every bound that uses `B_*` stays valid. Its interval for
  `code(U)` is reproduced by the review.
- **Batch 79, cluster J2: review of 21.** The review
  `review_eager_tree_aebfa.md` (`3b5989da9`) of the Hilbert's-tenth-problem
  research tree finds no theorem-level defect. Its finding P3 concerns
  `Evaluation.app` in `tree_kernel.py` (shipped as
  `code/21-eager-tree-tree_kernel.py`; the review cites line 65 of the original, where its
  patch hunk begins, and the method starts at line 67): the first code is
  checked only when it is decomposed and the second is not validated
  before the cache lookup, so `Evaluation().app(0,-1)` returns −1, and
  `app(0,True)` stores a record with a Boolean argument that a later
  valid `app(0,1)` reuses, after which the generated certificate fails the
  natural-coordinate checker. The polynomial checker rejects such a
  certificate, so this is not a false arithmetic zero. The tested patch
  `eager_tree_exact_application_inputs.patch` (SHA-256 `bb669fe7…cdfe`,
  beside the review in
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`)
  adds exact natural-integer validation of both codes; it was **not
  applied**, and at the batch-79 write the shipped program was the
  delivered original. The review reran
  all 19 author stages on the original and the repaired copies, reproduced
  the 26 saved JSON objects (normalizing only the changed source digest),
  and added 774 independent assertions. No theorem of Part XIX depends on
  the defect. Batch 80: the authors' corrected code edition (arrival
  `4e270aa46`, placement `8a4e64732`) makes `Evaluation.app` reject any
  code that is not an exact nonnegative `int` (so Booleans, floats and
  subclasses) with `ValueError`, before the cache lookup, active-call and
  budget checks and any state change; it is now the shipped
  `code/21-eager-tree-tree_kernel.py`. Its guard is written independently
  (one condition on both codes, the same message) and is equivalent to the
  patch: the patched original passes the new suite
  `code/21-eager-tree-test_application_domain.py`, the unpatched original
  fails it. **Do not apply the patch to the shipped file**: the repair is
  already present and the hunk fails (`patch --dry-run`). The tree's
  correction audit `review_batch80_corrected.md` (`abfc0cb25`) confirms the
  repair and that the rest of the kernel's AST is unchanged.
- **Batch 83, cluster H1 (manuscripts 22 and 23): shipped text that uses
  delivery names or names unshipped files.** Both `INTEGRITY.md` files
  (shipped as `22-literal-sandpiles-INTEGRITY.md` and
  `23-real-sandpiles-INTEGRITY.md`) describe the delivered release: the
  unshipped `MANIFEST.json` and `SHA256SUMS`, `verify_release.py`,
  `seal_release.py` and the other entry points by delivered name, POSIX
  file modes and modification times, and commands run from the release
  directory. The evidence READMEs, proofs and audits name their files by
  paths relative to their packet (`ca/lazy_u15.py`, `compiler/…`,
  `gates/…`, `geometry/…`, `review/audit_*.py`, `data/u15_table.json`,
  `FROZEN-INPUTS.json`, `approved_base/`, `PROOF.md`); the loader's audit
  and README name the unshipped `data/u15_table.json` and
  `FROZEN-INPUTS.json`, and 23's README, PROOF and review name the
  unshipped `approved_base/` pair, its `SHA256SUMS` and `MANIFEST.json` and
  the optimized receipts; 23's `PROOF.md` also names the predecessor packet
  as `sandpile-certificate-composition-20261003/PROOF.md`, which is 22's
  composition `PROOF.md`. Every program reads and writes by delivered
  paths: `test_lazy_u15.py` and `verify_bundle.py` read
  `data/u15_table.json`; `test_prism_certificate.py`,
  `literal_composition.py` and `review/audit_adapter.py` read
  `evidence/loader/FROZEN-INPUTS.json` and check the hash of every loader
  file it lists; 23's `real_certificate.py`, `freeze_packet.py` and
  `independent_coefficient_ledger_checks.py` import or hash
  `approved_base/prism_certificate.py`. The receipts in `data/` record
  delivered paths and hashes; `data/22-literal-sandpiles-verification-source-lineage.json`
  and `data/23-…-source-lineage.json` map original to packaged paths of the
  delivery, not to shipped names; the replay plans give delivered working
  directories. `data/23-real-sandpiles-evidence-real-report35_integrity_check.txt`
  records that "all 78 frozen-release SHA256 checks" of 22's archive pass
  (verified again at placement). The article prints shipped names where 23
  names its files, and a note where 22 names its unshipped table.
- **Batch 83, cluster H1: corrections, renamings and notes in the printed
  text.** 22's certificate-interface theorem (its Theorem 1.3, in Section
  3.22) states no hypothesis on the input outside the prism; a `[write]`
  bracket in the statement and a note supply its Section 9's standing
  hypothesis (natural `η` stable outside `P`, every finite addition in
  `P`), automatic for the loader. Renamed: 22's `\bits` (`{0,1}`) and `\U`
  print as `\bitset` and `\Ufift` with the same glyphs; 23's `\QR`, printed
  `Q_R` there, is `Q^real` here, because Part XVI's `Q_R` is a box; 23's
  selector macros print with the same glyphs under new names. 22's Figure 1
  is printed at the opening of Part XX, so that no figure number moved.
  Notes mark 22's certificate theorem and least-action lemma as second
  routes to Part XVI and manuscript 19, record that its bundled machine
  table is the neighbouring report's, and point 23's Section 4 to 22's
  proof. A written conventions table resolves the clashes with Part XVI
  (`Q_R`, `Q`, `H`, `L`, `R`, `ρ`, `λ`, `B`, `M`, `N`, `b`, `δ`, `T`) and
  between the two manuscripts' names, and prints the two arithmetic
  conventions as two labelled rows.
- **Batch 83, cluster H1: the research programme's review.**
  `review_sandpile35_36_intake.md` (`c120b34df`, 3 October 2026, before
  placement) authenticates both archives (SHA-256 above), executes no
  archived code, and passes the certificate argument and the real-orthant
  upgrade within a stated scope: it read 22's README, composition proof,
  vertex and edge formulas and loader proof, and 23's README, real proof,
  independent review and source; it did not reconstruct the physical
  graph, routing seams, automaton or machine tables, the encoder or a giant
  prism. Its findings, all printed in the article's `cdc:sec:b83-review`:
  the restatement of 22's theorem with its hypotheses and the exclusion of
  nonbinary odometers; the loader's scope (total topplings, one-shot also
  when nonhalting, the conditional and noncomputable prism bound, the
  imported encoder, Cairns's paper not verifying this graph, a family of
  cubics rather than a fixed finite list of witnesses and operations);
  23's argument confirmed without integral ranks, the LP searches
  unnecessary and not rerun, `5/36` reproduced; a moment identity for the
  five weighted edge squares and two paid shared schedules saving exactly
  `V+4E` multiplications and `E` additions (55→54, 145→138, 839→771 for the
  real variants of three fixtures), independently reviewed
  (`review_sandpile_shared_arithmetic35_36.md`, PASS); the real upgrade
  costing `V` additions in those schedules against `+2V` per count in 23's
  convention, printed as two conventions; the positive-coordinate shift
  valid only on `p ≥ 1`; the real-algebraic limit on fixed-arity
  compression with its stated exceptions; no effect on the 84-operation
  bound; and the next step, a paid integer-only packing interface. It
  supplies no patch; nothing shipped was changed.
- **Batch 83, cluster H1: reruns.** The delivered release verifiers
  (`code/22-literal-sandpiles-verify_release.py`,
  `code/23-real-sandpiles-verify_release.py`) check the unshipped
  `MANIFEST.json` with POSIX file modes and refuse to run on NTFS
  ("Identity gate: payload mode mismatch"); `tamper_regression.py`,
  `archive_*.py`, `seal_release.py` and `build_pdf.py` are release tools
  that need the delivered tree. The placement session ran the full replay
  on a copy of the extracted archives through a shim that substitutes only
  the manifest-declared modes: 22 26/26 producer runs (13 producers, normal
  and `-O`, 9 min) and 23 4/4 (SymPy 1.14.0, 4 min), every regenerated
  receipt equal to the expected one up to CRLF. The write reran every
  producer directly (normal Python) on a copy restored from the shipped
  files by the recipe below: all pass, with receipts equal up to CRLF; see
  "Rerunning the checks".
- **Batch 91, cluster A (manuscripts 24–27): shipped text that uses
  delivery names, names unshipped files or is stale.** Every shipped guide,
  proof, audit and review names files by delivered paths relative to its
  package (`science/…`, `independent_audit/…`, `audit_replay/…`,
  `verification/…`, `hardness-interface/…`, `universality/…`,
  `dependencies/…`); the four `data/2N-…-MANIFEST.json` files, the freeze,
  preservation and replay records list delivered paths, including the
  unshipped manuscripts, PDFs, READMEs, twins, mathlib copies, Part XX
  copies, 26's DAG and renders, 27's `SHA256SUMS` and 25's whole
  `baseline_report50/`. 25's notes and receipts name `baseline_report50/…`,
  which is 24's delivery. 26's `data/26-repeated-target-science-evidence-manifest.json`
  and `code/26-repeated-target-science-source-review-check_source.py`, and
  several audits of 24–27, name historical working directories
  (`/workspace/shared/sandpile-…-20261004/…`, `sandpile-target-firing-20261004/…`),
  the authors' historical working directories; the hashes in 26's manifest
  resolve to 25's shipped files (checked at placement), and the programs
  that read such paths do not run as shipped. Stale status: 24's
  `24-fixed-arity-science-PROOF.md` and `…-science-README.md` say the
  independent audit is "in progress", and 25's
  `25-binary-target-science-ARCHITECTURE.md` and `…-SOURCE_NOTES.md` say
  review is "pending"; they are frozen construction-stage notes, the
  completed audits are shipped, and 25's own manuscript says so.
  `data/24-fixed-arity-verification-coordinating-review.json` records a
  title-only amendment after review (one bibliography title), so its
  reviewed TeX and PDF hashes are of an earlier edition. 26 states no ProveIt
  pin of its own. The article prints shipped names where a manuscript
  names its files and a note where it names an unshipped one.
- **Batch 91, cluster A: corrections, renamings and notes in the printed
  text.** Renamed macros: `\Pow` → `\POWER` (this report's `\Pow` is
  manuscripts 17–18's power graph), 24's and 25's `\AND` → `\BitAnd` (this
  report's `\AND` is 22's lattice primitive), 26's `\Pre` → `\Prestr`; the
  spreading operator printed `Spread` in 24 and 25 and the geometric-sum
  operator printed `G` in 27 are printed `SPREAD` and `Geom`; unused
  `\Pack`, `\NatVar` and `\eqdef` dropped; `\file` and `\sha` print as
  `\code` and `\path`. A conventions table resolves the clashes with Parts
  XVI and XX and between the four manuscripts (`I`, `b`, `L`, `R`, `E`,
  `V`, `T`, `Q`, `J`, `h`, `τ`, `ℓ`, `P`, `π`, the gate convention). Notes
  credit `POWER` to `ptr:ai:lem:exp` and `Sub` to Jones–Matiyasevich and
  `JM1984.Exp.SFU.mask`, mark the least-action lemmas and the macro
  presentations of 26 and 27 as second routes, map "Report 35/36/50/52/53"
  to their places here, and print 25's Sections 2–5 as pointers quoting the
  three passages in which they differ from 24's Sections 3–6.
- **Batch 91, cluster A: Cairns's paper.** 26 and 27 call six printed
  passages of Cairns's arXiv:1508.00161v2 misprints (26: Sections 3.2.4 and
  3.2.5; 27: the pattern test and the halting definition of Section 5.1,
  the cutoff and front placement of Section 6.2.5 and Figure 12, and the
  shutdown delay of Section 6.2.6). At placement three printed forms were
  checked against the arXiv HTML; for this write all six were checked
  against the text of the version-2 PDF (the operator of the sixth is lost
  in the extraction), and the article's `cdc:sec:b91-cairns` gives an
  explicit failure of each printed form, the manuscripts' arguments made
  explicit (for example: the printed one-chip initializer of Section 3.2.5
  sets the cube `c(x+x₁,t)` both to blank and directly, so it malfunctions
  for every tape). These are readings of a third-party paper, not an
  erratum issued by its author; whether the corrected constructions prove
  Cairns's Theorems 2 and 3 is left open as `cdc:us:q:cairns`. Two short
  quotations (14 words) of the paper are in the shipped
  `26-repeated-target-universality-PRIMARY_SOURCE.md`.
- **Batch 91, cluster A: the research programme's review.**
  `review_new_sandpiles_0d7f51c44.md` (`bc6e1a62c`, 4 October 2026, before
  placement) authenticates the four archives (320 members, 30 read spans),
  executes no archived code, finds no concrete defect in the text it read,
  and confirms with a fresh checker (normal and `-O` receipts identical) the
  totals 11,469/14,778/17,275/14,571 gates, 2,566/3,308/3,865/3,262
  witnesses, closure, liveness, the residual-square suffixes and exact
  degree 18 (coefficient 48 on one univariate line). It does not reconstruct
  residuals against the macro specifications, did not reread the mathlib
  proof, treats the Cairns corrections as disclosed dependencies, and finds
  no effect on the 84-operation polynomial. All of it is printed in the
  article's `cdc:sec:b91-review`; it supplies no patch, and nothing shipped
  was changed.
- **Batch 91, cluster A: reruns.** See "Rerunning the checks": on Windows
  the builders and checkers reproduce every DAG byte for byte and every
  receipt up to CRLF; 24's and 25's audit replays reproduce their receipts
  up to CRLF but report failure because they compare bytes; 26's and 27's
  replays need a POSIX host; the release verifiers need POSIX modes. 26's
  DAG and page renders are excluded and reconstructed byte for byte (see
  "Reconstructing the excluded data").
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
  `verification.json`). Batch 79, cluster J2: 21 has no in-archive copy.
  No two files of different manuscripts are identical.
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
  21's receipts record no elapsed time or Python version, but six of them
  record SHA-256 hashes of files that a rerun rewrites, which depend on
  the platform's line endings.
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
  integration note) became the new entry `repo-qcint`. 21 inspected no
  ProveIt commit; its four keys `jaykernel`, `jayreflective`, `jaytree`
  and `dallago` are new entries, with its `\href` links printed as URLs.

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
- **Batch 79, cluster J2 (Part XIX).** 21 duplicates no printed theorem,
  so it is appended whole as Part XIX after Part XVIII and before the
  appendices, in its own order (Sections 2–12 and Appendices A–B), so
  that no existing section, theorem, equation or table number moved; its
  title-page box and status lines, abstract and Section 1 are Section
  3.21, and the Section 3 heading became "The twenty-one manuscripts".
  Written: the Part's opening (source and scope, relation to the other
  Parts, the review, setting and hypotheses) and a conventions section
  with a table of letters and their clashes (K, I and the stem `𝖲` are
  not Part VII's combinators; `f` is not Part VII's `App`; `H` is a call
  cost, not Part VII's context depth); notes at 21's coding (Part VII's
  pairing, `f = 2π+2`), growth bound (`cdc:wf:prop:ski-height`),
  inactive-field equations (`cdc:wf:lem:activation`), sharing example
  (the remark after `cdc:mem:cor:graph`) and closing allusion (naming
  `cdc:wf:thm:ski` and `cdc:mem:cor:graph`); a note that no computable
  function bounds the external `N` on the universal domain (by
  `cdc:bd:prop:nobound`); a remark on ProveIt's combinatory-logic
  development naming its formalized declarations and claiming no formal
  status; four review notes; and lines after four of the six questions.
  Dated `[write]` note: after `cdc:q:ski` (Source 01 answered in part for
  another calculus; Source 04 only touched). Renamed: 21's `\code` is
  `\tcode`, its `\cl` is `\clos`, its `\file` is this report's
  `\code`. The review's patch is not applied; its tighter interval for
  `R` is printed beside 21's numbers, which are unchanged. Bibliography:
  five new entries (`jaykernel`, `jayreflective`, `jaytree`, `dallago`
  and the review `repo-etrev`; 98 distinct works in all, 99 since the
  batch-80 entry `repo-b80rev`), and `repo-cl`
  is cited by the written remark. 21's author line and PDF metadata name
  no AI assistant.
- **Batch-79 reciprocal notes (cluster J2).** Six dated `[write]` notes of
  2 October 2026 point to Parts III–IV of `signal-machine-collision-certificates`
  and Parts IV–VI of `quadratic-orthant-certificates`: in Part XI after the
  discussion following `cdc:of:thm:singlefoldsl`, in Part V after the example
  following `cdc:mem:lem:compare`, in Part II after the paragraph following
  `cdc:ex:gap`, in Part XIII after `cdc:rx:thm:threshold` and after the
  question "Substrate-transfer theorems", and in Part XVI after the question
  "Local certificates on adaptive support geometry" (see "Reciprocal notes
  (batch 79, cluster J2)" above). They cite those reports' labels by name;
  no label was added, renamed or renumbered, and no printed text was
  changed.
- **Batch-80 reciprocal note (cluster K2).** One dated `[write]` note of
  2 October 2026, in Part XI after the batch-78 note that follows
  `cdc:of:thm:classification`, points to source 17 of Part VI of
  `signal-machine-collision-certificates` (written in `ef114b0bb`): a
  non-semilinear hit set of a binary number-conserving automaton, outside
  `𝒟⁺₃` by that theorem, with a single-fold quartic (see "Reciprocal note
  (batch 80, cluster K2)" above). It cites that report's labels by name;
  no label was added, renamed or renumbered, and no printed text was
  changed.
- **Batch-82 reciprocal note (cluster M4).** One dated `[write]` note of
  3 October 2026, in Part XI after the batch-79 note that follows the
  discussion of `cdc:of:thm:singlefoldsl`, points to source 20 of Part VII
  of `signal-machine-collision-certificates` (written in `9b3977008`): a
  canonical membership quartic, a second route at a higher degree (see
  "Reciprocal note (batch 82, cluster M4)" above). It cites that report's
  labels by name; no label was added, renamed or renumbered, and no
  printed text was changed.
- **Batch 80, cluster K1 (corrected code edition of 21).** A dated
  `[write]` note "Added 2 October 2026 (batch 80): corrected code edition"
  after the batch-79 review note in `cdc:et:sec:reproduce`; a `[write]`
  note after the artifact index (`cdc:et:app:artifacts`) naming the two
  new files; sentences updated in the Part's opening, in the package note
  of Section 3.21, in the provenance table (row 21) and its list, and in
  the bibliography entry `repo-etrev`; one new bibliography entry,
  `repo-b80rev`, for the correction audit. The batch-79 statements that the
  shipped kernel was the original and the patch not applied are kept as
  history. No statement, label, number or manuscript text changed (the
  corrected archive's `.tex` is byte-identical); no label was added.
- **Batch 83, cluster H1 (Part XX).** 22 and 23 continue Part XVI, 23
  depends on 22, and 22 delivers the loader that Part XVI's question names,
  so they form one addition: Part XX after Part XIX and before the
  appendices, 22's Sections 2–13 and then 23's Sections 2–9, with their
  abstracts and Sections 1 as Sections 3.22–3.23; no existing section,
  theorem, equation, table or figure number moved. Not a new report (both
  state that they continue Part XVI), not inside Part XVI (the loader,
  automaton, router and primitives are a new subject, and Parts are
  appended), and not *fixed-universal-polynomials* or
  *quadratic-orthant-certificates* (they share only the machine and the
  credited real-gate principle). Printed once: the binary certificate
  theorem (22's, with 23's Section 4 as a pointer keeping its two extra
  remarks). Kept as marked second routes, with no novelty claim: 22's
  certificate theorem and least-action lemma against `cdc:sp:thm:compact`,
  `cdc:sp:thm:collar`, `cdc:sp:lem:leastaction`, `cdc:nb:thm:halo` and
  `cdc:nb:lem:least`. The fractional singleton zero is printed in both
  manuscripts' places. Written: the Part's opening (source and scope,
  relation to other Parts, the review, setting and hypotheses), a
  conventions table, notes at the re-proofs, the input-hypothesis bracket,
  the review section `cdc:sec:b83-review`, nine labelled questions
  `cdc:sec:b83-questions` (restating the manuscripts' closing prose and the
  programme's next step) and dated notes after six questions of Part XVI
  (16's fewer-witnesses, ledger, loader and fixed-arity questions, 19's
  `cdc:nb:q:smaller` and `cdc:nb:q:formal`). The provenance appendix
  counted "twenty manuscripts" since batch 79; it now says twenty-three,
  as does the bibliography's opening note. Bibliography: eight new entries
  (`neary-woods-fi`, `repo-cdc83`, `repo-qoc83`, `lp-loaderpacket`,
  `lp-certpacket`, `ro-report35`, `repo-b83rev`, `repo-b83arith`);
  `cairns` and `basu` extended. Neither manuscript names an AI assistant.
- **Batch 91, cluster A (Part XXI).** 24–27 are four events over one
  construction, 24 answers Part XX's last question and 27 extends it, so
  they form one addition: Part XXI after Part XX and before the appendices,
  in the order 24, 25, 26, 27, each in its own order, with abstracts and
  Sections 1 as Sections 3.24–3.27; no existing section, theorem, equation,
  table or figure number moved (the `.aux` comparison in Build). Not four
  Parts (one spine, shared macros and geometry), not a new report (24
  continues Part XX by name and answers its question), not inside Part XX
  (Parts are appended). Base: 24, the common construction. Printed once:
  25's Sections 2–5, near-verbatim copies of 24's Sections 3–6, as four
  pointer sections quoting the three differing passages. Printed in full as
  marked second routes: 26's and 27's own presentations of the macros
  (independently worded, adding positivity details and a counterexample),
  and 24's and 27's least-action lemmas against Parts XVI and XX. The shared
  separating examples are printed in each manuscript's place. Credited
  without a novelty claim: `POWER` (= `ptr:ai:lem:exp`) and `Sub`
  (Jones–Matiyasevich, formalized as `JM1984.Exp.SFU.mask`). Written: the
  Part's opening (sources, a table of the four theorems, relations, the
  review, setting), a conventions table, notes at the re-proofs and at every
  unshipped file, the review section `cdc:sec:b91-review`, the Cairns
  section `cdc:sec:b91-cairns` with the remark `cdc:us:rem:cairns` (six
  counterexamples) and the open question `cdc:us:q:cairns`, 21 labelled
  questions `cdc:sec:b91-questions` restating the manuscripts' closing lists
  (with lines on which are answered inside the Part), and dated notes after
  `cdc:ro:q:packing`, `cdc:lp:q:encoder`, `cdc:q:compression` and manuscript
  16's question on fixed-arity compression, and in Part XX's setting
  paragraph, whose "Nothing here is a fixed-arity universal polynomial" is
  scoped to Part XX (not retracted: Part XXI's polynomials are not universal
  in the programme's sense). Claims of the sources that are unproved here
  are kept as open questions with their sketches and what is missing
  (`cdc:us:q:cairns`: the corrected Cairns constructions, 26's bounded-seed
  normalization and fixed tile, the partial-gate accounting of 27's
  corrections); the six printed Cairns passages the manuscripts call wrong
  are refuted as printed in `cdc:us:rem:cairns`. The provenance appendix and
  the bibliography's note now say twenty-seven manuscripts. Bibliography:
  thirteen new entries (`mathlib-pell`, `r35-composition`, `r35-loader`,
  `r36-real`, `bt-report50`, `bt-audit`, `rp-packet`, `rp-audit`,
  `rp-interface`, `us-science`, `us-audit`, `us-interface`, `repo-b91rev`);
  `cairns` extended. No manuscript names an AI assistant.
- **Macros.** One `\code` (01's `\texttt{\detokenize{#1}}`); 02's `\_`
  escapes inside `\code` removed; the pin macros `\repoSHA` (01 and 07,
  different commits), `\repoCommit` (02) and `\reposha` (04) printed as
  literal identifiers; 04's unused `\repo` URL macro dropped (03's `\repo`
  kept); 06's unused `\word` dropped in favour of 07's. No mathematical
  symbol was renamed; letters that change meaning between Parts are listed
  in the conventions.

## Reciprocal-note review correction

The [scoped review of `1fdcaf5a6`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_reciprocal_1fdcaf5a6.md) found that the exhaustive
shared-result summaries omitted the common fifteen-equation POWER theorem.
The current comparison names both POWER and binary containment, without
claiming an exhaustive count. Group-theoretic-substrates Remark 1.1
(`gts:rem:shared-power-containment-correction`) retains and refutes the former
“No other theorem is shared”, containment-only and one-result claims; the
CDC note retains its original sentence and points to that numbered remark.

Three direct `pdflatex -no-shell-escape` passes rebuilt this edited article
to 742 pages. All 1940 labels (including optional-type labels) are unique and local references/citations
resolve, with no overfull boxes. The final log has 1 underfull-box
message in untouched text; the only warning reports intentionally disabled shell escape.
PDF page 646 was visually checked for the correction. The immutable review
records its exact source-read limits; no packaged or frozen program ran.
