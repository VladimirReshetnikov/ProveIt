RANKED CONTINUATION COMPRESSION: OFFLINE EXPERIMENT PACKET

Outcome: no new machine below the retained 252 working states was certified.
This packet supplies a general simulation criterion with a decreasing rank,
a finite certificate for the literal program, and two completed bounded
state-deletion diagnostics. A failed diagnostic is not a state lower bound.

Run from this directory, using Python 3.10 or later and the standard library:

  python continuation_search.py --mode uniform --output continuation-uniform.json
  python continuation_search.py --mode incoming_actions --output continuation-actions.json
  python audit_continuations.py
  python residue_phase.py

The first two commands repeat 55,471 uniform-fold and 132,048 full incoming-
action recipes. In the recorded runs they took about 40 and 117 seconds.
All 8,391 baseline guarded cases and the exact 82,552-step whole blank
bootstrap are checked before each search. There were no survivors.
The independent audit checks the finite control certificate, rank obligations,
acceptance boundary, and the completeness/uniqueness of the saved ledgers;
it does not independently repeat every affine candidate check.

The residue experiments use exact values below M and residue classes modulo m
above M, for (M,m)=(2,1),(8,4),(32,8),(128,32). Each final invariant is checked
against all source transitions. They exclude the same six guards as the older
three-value analysis and add no exclusion.

NEW RESEARCH CODE
  control_bisim.py
  continuation_search.py
  audit_continuations.py
  residue_phase.py

PINNED INPUTS AND PROVENANCE
  ProveIt snapshot: fab89c5d26b81cd2ccab2ee5d213ff23725c7726.
  The exact old-label table is candidate-permutation252_zfc_permutation252_old.tm,
  copied from Computability/BusyBeaver/Research/ZFC/candidate-permutation252/.
  SHA-256: 939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713.
  Prog254.v is copied unchanged from
  lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v.
  SHA-256: 1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746.
  The strict affine checker is copied unchanged from
  SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/
  27-variant-experiments-machine_search-grammar_search-strict_affine.py.
  SHA-256: da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce.

  candidate252_independent_audit.py and permutation252_phase_analysis.py
  supply imported parsing/simulation utilities from that ProveIt snapshot.
  For shallow standalone extraction, their unused-at-import ROOT assignment
  is changed from .parents[4] to .parent. Every function and class AST remains
  identical, as recorded in packaging-adaptation.json. The complete baseline
  and the independent certificate audit passed again after this packaging
  adaptation. The large searches were not repeated: their algorithms and
  all imported function bodies are unchanged. Do not run those helper files'
  original repository-oriented main commands from this packet.

ATTRIBUTION AND LICENSE BOUNDARY
  Mira-Cult designed the original machine; Jeff supplies its original Coq
  verification, with Wade's compiler framework acknowledged in the sources.
  The vendored historical upstream snapshot is
  297ab8df7e5de329605c3875b4934643b371a5e3.
  The public 253 reduction is attributed to mira-emmy's PR20, head
  0d544f2a2e3c18f12278441a74b7879f31cbe856.
  ProveIt's permutation [0,3,4,5,8,1,6,2,7] makes the runtime252 table a clean
  blank-start machine. This packet does not claim authorship of that result.
  UPSTREAM_ATTRIBUTION.md preserves the imported snapshot's own notice.
  In particular, no blanket relicensing of the upstream source is intended.

FILES
  artifact-manifest.json gives the selected files' hashes.
  continuation-certificate.json contains all site classes, ranks and targets.
  continuation-audit.json records independent audit scope and results.
  continuation-uniform.json and continuation-actions.json retain every recipe,
  its first rejected guarded case, and its diagnostic stop category.
  residue-phase-*.json retain the four final abstract invariants.
  continuation_section.tex is a preamble-free report section and proof.
