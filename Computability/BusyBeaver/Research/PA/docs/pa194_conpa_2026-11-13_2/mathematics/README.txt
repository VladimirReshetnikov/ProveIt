Mathematical proof and independent symbolic checks
=================================================

pa194_calibration.tex is the PA194 consistency-equivalence proof included
in the main paper. Its dependencies are the exact separate190 emitter,
the original ten-entry command compiler proved there, the preserved PA195
syntactic calibration, and the finite source/physical certificates.

check_emitter_and_words.py independently expands the PA194 and historical
separate196 grammars without importing either compiler. It checks the exact
symbolic output stack and top, then checks the original command words using
explicit Cantor identities and constructor residue facts. Run it from any
working directory. emitter_and_words_receipt.json records its successful
result and pinned grammar/table digests. This is an executable algebra audit,
not a newly checked proof-assistant theorem.

proof_and_comparison_audit.txt reviews the supplied PA195 proof and the pinned
input archive corpus. Its input census intentionally excludes the new PA194
outputs of this task and carries no lower-bound interpretation.

Optional alternative-emitter investigations
--------------------------------------------
h1_transfer_proof.tex and h2_h6_transfer_proof.tex are ordinary mathematical
notes on other possible ways to relocate the diagonal-vacuity clause. They
are exploratory alternatives and are NOT dependencies of PA194. The delivered
PA194 machine retains the original separate190 head order and parameters.
The finite search records for these alternatives are under comparison/searches;
their matching estimates are not certified full-machine state counts.
