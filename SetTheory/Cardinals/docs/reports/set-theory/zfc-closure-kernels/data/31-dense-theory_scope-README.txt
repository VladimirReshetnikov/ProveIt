DEFAULT VARIABLE INDICES FOR THE FIXED-FOUR-SLOT EPSC2 CHECKER

This directory contains one isolated, tested reference change. Every raw matrix
formula is interpreted with out-of-range variable indices selecting the final
matrix-local environment value. The checker no longer traverses an entire
matrix to reject it for poor scope. Matrix-local scope begins with the four
original projected values, and each matrix binder prepends one value.

No binary Turing machine is generated and no state saving is claimed. The proof
engine, primitive Bottom, fresh-name allocator, proof-reference checks, and the
three fixed matrix projections are retained. No actual EPSC2 refutation is
known or claimed. Accepted demonstrations are ordinary logical contradictions
formed from A and not-A; the public interface does not accept such assumptions.

FILES

  epsc2_original.py         byte-preserved incoming reference
  epsc2_default_indices.py  changed executing checker
  check_default_indices.py independent finite differential audit
  default_indices_results.json generated audit evidence
  LICENSE.ProveIt           license from the source repository

REPRODUCE

  python check_default_indices.py

Python's standard library suffices. Assertions must be enabled. Host resource
exceptions are not interpreted as acceptance or mathematical halting.

PROVENANCE

  Repository: https://github.com/VladimirReshetnikov/ProveIt
  Commit inspected: 4747142d5d15213eb711bdadfa3cc7e769fcb7a7
  Archive: docs/incoming/zfc_epsc2_proposal.zip
  Archive SHA-256:
    580d712866a4999194c9dc7130ddfa052b8b6db7c94c2cf20ec46a8f722f1ce7
  Member: zfc_epsc2_proposal/checker/epsc2_tableau.py
  Preserved-member SHA-256:
    efca519f170224a3a3efcb514616c793834e3bbcbc83640d287b1260a7db1c7f

The fixed EPSC2 theory, its ordinary consistency calibration, the three-hole
template, and the complete original tableau are inherited from that incoming
report. The new contribution is the fixed-scope default-index interpretation,
its explicit same-certificate transport, and this isolated executable delta.
The accompanying main research report contains the ordinary mathematical
proofs and precise limits; this directory provides finite reproducibility.
