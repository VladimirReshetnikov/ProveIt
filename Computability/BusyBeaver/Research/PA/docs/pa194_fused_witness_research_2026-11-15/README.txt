PA CONSISTENCY MACHINES: A FUSED WITNESS CONSTRUCTION
===================================================

Result
------
No accepted machine below 194 working states was obtained. The principal
new design is PA194FW, a complete 194-state binary one-tape machine whose
axiom emitter combines two formerly separate heads into N(I(h4,V)). Its
AX command has ten stack entries. Three further literal 194-state physical
variants are included: PA194FW_MF, PA194H5XS_MF and PA194JH5XS_MF.

The written proofs establish the new preservation steps in iPRA and
compose them with the precisely identified, revised written AX11H
calibration to Con(PA). The retained absolute dependency is explicit.
This package does not claim a completed end-to-end Lean or Rocq proof,
a 193-state construction, or a 194-state lower bound.

Start with report/pa194_fused_witness.pdf. Its complete TeX sources are
beside it. The report includes all four complete transition tables, a
104-design comparison appendix, proofs, verification details, exact
counterexamples to rejected reductions, and bounded-search limitations.

Machine convention
------------------
The four dense tables have working controls 0..193, initial control 0,
and separate halt label 194. The head starts at coordinate 0 on an
entirely zero, two-way unbounded binary tape. Every transition writes
one bit, moves exactly one cell L or R, and enters the named control.
Entry into 194 halts. There is no uncounted initializer or external data.

Each line in machine.tm has five fields:
  current_state read_bit write_bit L_or_R next_state

PA194FW:
  primary/machines/PA194FW/machine.tm
  SHA256 8bc9eb53be619a30b37fbd40f47484045245b40fd04aa5f79763848c1ebc1224
PA194FW_MF:
  companions/machines/PA194FW_MF/machine.tm
  SHA256 ea777e7d339394a6de12f01ebf3c6e9e913cffdee909f6b0f63f81a7ea62f52f
PA194H5XS_MF:
  companions/machines/PA194H5XS_MF/machine.tm
  SHA256 628ddeaab91662d352ab807e5f5ec61bf84d4c18a12fa5a98bf14a55f705f484
PA194JH5XS_MF:
  companions/machines/PA194JH5XS_MF/machine.tm
  SHA256 02f53fd4acac7ed2f0d0a635c7548aac5292f06cc5da5389f44b80dcfc2f05af

Reproduction
------------
Python 3.10+ and the standard library, assertions enabled:

  python3 -B verify_release.py
  python3 -B verify_release.py --full

The default verifies all frozen file hashes, table conventions and cross-
package bindings, finite formula certificates with two checkers, symbolic
AX10 identities, a separate free-term emitter check, and every companion
guard/local identity and complete startup. The full command reconstructs
the main machine and replays every literal source/tape certificate, then
recomputes the 193/194 corpus comparison. It may take several minutes.
New logs and receipts go into replay/. Neither command uses the network.

To regenerate the report:

  python3 report/make_inputs.py
  cd report
  pdflatex -interaction=nonstopmode -halt-on-error pa194_fused_witness.tex
  pdflatex -interaction=nonstopmode -halt-on-error pa194_fused_witness.tex

Artifacts
---------
primary/       Fused source, literal machine, compiler, physical/source
               certificates, proof, exact inherited dependencies.
companions/    Three physical variants, parents, relative proof, exact
               original symmetric witness archive and upstream licenses.
comparison/    Complete recognized-format census at the pinned revision;
               104 named claims, 106 packets, 44 overlapping mechanism
               classes, 609 spanning 193/194 representatives, diagnostics.
research/      Failed reduction searches and exact rejection witnesses;
               independent emitter and mathematical audits.
verification/  Final assembled release verification receipts/transcripts.
report/        Main TeX/PDF, generated listings and build input script.

Source and limits
-----------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 883da8d55452ea097910ed2509a1eefc833ce292
Foundation gitlink: 32e1a0956a8622fad067328ca1959729a7634428

The recognized census reads every selected TM/JSON/ZIP Git blob under PA
and docs/incoming, including nested archives, with zero missing selected
files. It does not infer tables from generators, prose, Lean or opaque
encodings. Counts include historical experiments and rejected candidates;
the named positive-claim roster is recorded separately. Old descriptions
are attributed reported mechanisms, not 104 newly audited calibrations.

The four new graphs are absent from the recognized pinned corpus under
all spanning roots, state renaming, reflection, bit exchange, and ignored
halt-entry actions. This is a precise structural comparison. It does not
claim worldwide priority or that all mathematically equivalent machines
have been excluded.

Research/physical and research/scanner use the ORIGINAL PA194 input from
pa194_conpa_2026-11-13, not PA194FW. The former records exact rejection
certificates and bounded searches. None of its rejected 193-state files
is offered as a PA consistency machine. Search limits and unresolved
bounded runs are explicit. The fusion and parameter searches are in
primary/research/ and primary/proof/logical_search.tex.

Attribution
-----------
The project and retained proof/calibration manuscripts are attributed
to their original sources. Existing runtime code, list-lemma machinery,
restricted-implication derivations and physical MF transformation are
reused with their original notices and licenses. See each component's
PROVENANCE/NOTICE/ATTRIBUTION files. No permission to relicense inherited
material is implied. This report identifies the new source
fusion, ten-entry interface/compiler and exact new implementations.
