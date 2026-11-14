U218: a 218-state machine for Con(PA)
===================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

RESULT
------
The primary machine has 218 working states and 436 binary transitions:
four fewer states than the supplied U222 candidate. Its complete blank-tape
initialization is included. It is deterministic, has one two-way infinite
tape, one head, alphabet {0,1}, blank symbol 0, and only left/right moves.
The dense table uses working states 0,...,217, initial state 0, and the
separate halt label 218. The head initially scans position 0 of an all-zero
tape. The native table uses the inherited names, with halt label 254.

Using the supplied U222 correctness and unary-power-covering interpretation
arguments as mathematical dependencies, the report proves

  PA |- not Halt(U218, blank) <-> Con(U) <-> Con(PA).

The new work consists of an equivalent numerical axiom-emitter source,
checked physical compilation, two local state-reduction proofs, and exact
executable verification. This is ordinary mathematical proof formalizable
in PA, with executable finite certificates and symbolic induction checks.
It is not a newly compiled MM0, Rocq, or Lean proof of the complete endpoint.
The inherited K215 theorem concerns its own fixed ZFC machine and does not
automatically certify this changed source or table. No unconditional
consistency, actual non-halting, absolute minimality, or priority is claimed.

START HERE
----------
  paper/report.pdf             Full paper, proofs, comparison, and table.
  paper/report.tex             Editable TeX source.
  paper/transition_table.tex   Exact 218-row table appendix.
  machine/u218.tm              Complete dense transition table.
  machine/u218.native.tm       Same machine in inherited native labels.
  machine/sites.json          Exact 202-subtree register source.
  machine/state_map.json      Checked bijection between the two labelings.
  machine/machine_summary.json Counts, hashes, and intermediate identities.

Each transition-table line is

  state  read_symbol  write_symbol  direction  next_state

There are exactly two lines for each working state and no outgoing halt
rows. The separate halt is not included in the working-state count.

REPRODUCE OFFLINE
----------------
Python 3.10 or later, standard library only; no network or solver required.
Run from this directory:

  python3 -B reproduce.py
  python3 -B reproduce.py --full
  python3 -B reproduce.py --full --report /chosen/path/replay.json

The default audit takes a few seconds. It checks SHA256SUMS, reconstructs
the exact source, all intermediate native tables, the dense table and state
bijection, and replays source/CFG, routing, local simulation, fault-injection,
and blank-startup checks. It validates complete coverage and exact bindings
of the saved symbolic runtime records. The --full option additionally
rederives all 5,060 arbitrary-register symbolic cases and all four traversal
schemas, and exactly compares the case records and startup trace.

The full packaged replay took about 128 seconds in the research environment;
runtime depends on the machine used. Work files are temporary. An explicitly
requested --report is the only persistent verification output.

To regenerate the document (requires a normal pdfLaTeX installation):

  python3 -B code/build_paper_data.py
  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes may vary with TeX versions and timestamps. Rebuilding or editing
release files changes the release manifest; keep an untouched copy for
the exact-byte audit.

WHAT SAVES THE STATES
--------------------
1. Two antecedent exchanges A -> (B -> C) <-> B -> (A -> C), followed by
   closed-macro reassociation, reduce the emitter from 204 to 202 distinct
   subtrees without changing its 3,891 primitive occurrences. The proof
   works in the retained numerical logical core, uniformly for all selectors,
   including 0 and 1. The independent source audit checks all 737 replacement
   primitives, all 3,154 exterior primitives, and their resolved control edges.

2. The first physical allocation was rejected. Its CI1 entries at sites
   3004, 3232, 3305, and 3435 confused an arithmetic context with an internal
   decoder context. Redirecting exactly three incoming rows to temporary
   native state 507 repairs these four cases while retaining 135 intentional
   decoder uses. A concrete 534-step trace demonstrates the original
   arbitrary-input primitive-contract failure.

3. State 200 is always entered scanning zero. Its zero row is identical
   to state 209's. Redirecting its sole incoming edge to 209 removes state
   200 with exact step-for-step preservation of tape, head, and halting.

4. States 182 and 507 are entered after a predecessor wrote, respectively,
   1 or 0 immediately to their left. Identifying them and changing 182/0 to
   (0,L,209) reuses existing paths that inspect this tag and restore the tape.
   One old step is simulated in 1, 3, or 5 new steps. A PA-formalizable
   bounded-stuttering proof establishes halting equivalence both ways.

There is no asserted running-time identity between U218 and U222. Only the
zero fold preserves every step. The factor-five bound applies to the final
tag fold relative to the verified intermediate implementing the same source.

KEEP THE INTERMEDIATES DISTINCT
------------------------------
The inputs directory contains three differently named 219-state tables:

  provisional219.native.tm   REJECTED: the original routing error.
  untagged219.native.tm      VERIFIED: repaired220 followed by the zero fold.
  tagged219.native.tm        VERIFIED: repaired220 followed by the tag fold.

The report takes repaired220 -> untagged219 -> U218. The fixed builder
records repaired220 -> tagged219 -> U218. Both routes are checked and
produce exactly the same U218. The rejected table is retained solely as
a diagnostic; its failure is not evidence against either corrected table.
The untagged219 intermediate also has its own successful full runtime receipt.

VERIFICATION AND EVIDENCE
-------------------------
  evidence/runtime.json          Final universal runtime summary.
  evidence/runtime_cases.json    All 5,060 symbolic case derivations.
  evidence/startup.json          Complete literal blank-startup trace.
  evidence/bootstrap_independent.json
                                 Independent startup and table census.
  evidence/source_audit.json     Syntax, source factors, and control flow.
  evidence/routing_split.json    Exact repair at all 3,891 prefixes.
  evidence/tagged_fold_independent.json
                                 All 6,976 admissible five-cell frames.
  evidence/zero_fold_*.json       Independent known-zero certificates.
  evidence/*controls.json        Fault checks; 25 rejected mutations in all.
  evidence/provisional219_counterexample.json
                                 Concrete 534-step failed primitive trace.
  evidence/package218_full_replay.json
                                 Full deterministic packaged replay.
  evidence/package218_replay.json
                                 Final fast audit including added controls.
  evidence/verification_summary.json
                                 Exact relationship between those receipts.

The 5,060 cases cover 3,891 source sites, with both zero and positive cases
for 1,169 decrements. Their symbolic induction rules quantify over arbitrary
natural register values, admissible gaps, and finite spare-register tails;
this is not a bounded test over sampled register values. The four traversal
schemas are rederived from the literal table.

Blank startup takes 95,726 steps and reaches native state 84, head -8, gap 1,
register vector (4,0,0,0,0,0,0,0,0), and forty spare registers each equal to 1.
Every nonzero tape cell and the zero exterior match U222's calibrated frame.
The extra twelve startup steps are included in the literal table.

The first full replay began before ten additional tag-mutation controls and
the explicit rejected-table counterexample were added. The subsequent fast
audit checks those additions. The final table, source, builder semantics,
and symbolic runtime were unchanged; both receipts bind the same identities.
Those historical assembly receipts predate the final release manifest. A
fresh default run checks the complete release manifest as well.

REFERENCES AND PROVENANCE
------------------------
The exact parent U222 archive is included under inputs/. It preserves the
runtime checker, original theory report, logical proof sources, source data,
and original notices. The fixed construction patches and source recipe
make reconstruction independent of the heuristic allocation search.

references/U221_ConPA_2026-10-28.zip is the complete simpler 221-state result:
one redirected U222 edge, one deleted state, exact step preservation, its
own TeX/PDF, machine, proofs, checkers, and parent dependency. Its historical
202-subtree supplement records the source-only research stage before the
final physical U218 integration; the current paper is the combined result.

references/source202/ preserves the precise source recipe, search summary,
independent proof and audit, and numerical proof-translation argument.
references/local_proofs/ contains supplementary local proofs.
reviews/ identifies the six larger proposals and their structural census.
They were compared for counts and construction ideas; their complete
end-to-end correctness developments were not all rerun.

All supplied incoming archives are pinned to ProveIt commit
340b96f75c64de58948509a12eec78baa9b5663e. PROVENANCE.json gives exact source
URLs and hashes. NOTICE.txt and licenses/ preserve attribution and terms.
Independent checks in this package were written within the same assistant
research collaboration; they are not represented as external human review.

EXACT MACHINE IDENTITIES (SHA-256)
---------------------------------
Native U218:
366cf96800bd4299de831355a80092394462278f0b62db1e19c167ca5f8b2a30
Dense U218:
225709a399367b5b1683ec0dc35994929184e4c9c1dcd638771a8a5c3efda953
202-subtree source:
bc70b28ff4628db5b9b0c9bd87f560697223e4887f2568b0ece801906713db8f

The complete release is covered by SHA256SUMS. The report ends with concrete
further research questions; no global state lower bound is established.
