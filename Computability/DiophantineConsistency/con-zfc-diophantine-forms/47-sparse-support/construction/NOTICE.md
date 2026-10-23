# Provenance and attribution

New contribution: sparse supported-monomial source coding, two concrete
weight vectors, and the scaled quadratic source for the nine-variable
branch; associated generators, audits and proofs were prepared with AI
assistance for Vladimir Reshetnikov's ProveIt project on 23 October 2026.
No external human review or new proof-assistant build is asserted.

The exact source snapshot is
`https://github.com/VladimirReshetnikov/ProveIt/tree/124c07c0b77a9e20e84676514d8b1ff78536ea3f/Computability/DiophantineConsistency/con-zfc-diophantine-forms`.

- `build_sparse_nine.py` and `circuit.py` derive from package 45's
  `nine/build_multitarget_nine.py` and `nine/circuit.py`. The source packing,
  coefficient parser, fixed-leaf scaling and weight certificates change;
  the numerical Jones bridge and finalizer retain their source provenance.
- `build_sparse_ten.py` derives from package 40's `code/build.py`.
  Sparse supported-monomial weights replace its full B2 vector. Its Sun
  arithmetic bridge, quintic merger and norm finalizer are inherited.
- `parent_system.json`, the four original compressed ports and their
  semantic calibration come from package 31. They remain one coherent
  tuple, with the already shifted MF_source as the fourth port.
- `targets_original.json` is package 45's original
  `quartic/QUADRATIC_TARGETS.json`, Git blob
  `7a2133ea122cb3f06fcac8b891fc16a5fbefd368`. It is kept for the audited
  comparison and source-support transcription.

The general nine-variable arithmetic reduction is credited to
Matiyasevich and Jones. The ten-integer arithmetic reduction and
intersective quintic merger are credited to Zhi-Wei Sun and their cited
sources, as in the inherited notices. They are not new results of this
package. No use is made of an unpublished lower variable-count theorem.

Inherited license and attribution texts are retained under `licenses/`.
Newly authored material is supplied for incorporation into ProveIt; no
third-party license terms are overridden. The new finite search is a
discovery procedure, not a minimality certificate. The literal vectors and
exact audits are authoritative.
