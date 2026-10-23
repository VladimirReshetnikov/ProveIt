# Round7 sparse quadratic packing deliverables

Main new results:
- `CERTIFICATE_174_regular.json`: padding0,W174,Dmax7678,Kcode8026.
- `CERTIFICATE_174_packed.json`: padding0,W174,Dmax5074,Kcode5422.
- `CERTIFICATE_174_interior_regular.json`: padding81,W174,Dmax7516,Kcode7864.
- `CERTIFICATE_174_interior_packed.json`: padding81,W174,Dmax4728,Kcode5076.

These are frozen certificates, not mutable search results. The two W200
certificates are earlier independently verified comparison points.

`SPARSE_PACKING_PROOF.md` proves the exact sparse-active separation theorem,
coefficient bound without a row-count penalty, overlapping-band validity,
and the interior-padding generalization. `section.tex` is a report-ready
concise mathematical section. `data/source_system60.json` is inert pinned
source data, byte-identical to the31-variable parent in the latest snapshot.
The fixed coherent coefficient binding lives in the archive's coefficients
folder; no port is an extra unknown.

Run `python3 verify_certificate.py` using only the Python standard library.
It reads each delivered certificate, reconstructs the shifted source in a
35-variable polynomial ring, checks136 symbolic coefficient records and
71808 source-term/expansion pairs per certificate, and writes VERIFICATION.json.
It does not trust or run any upstream script, search program, or generator.

Search programs are not proof dependencies and are omitted from this release.
The frozen finite certificates contain all required vectors and coefficient
records; the independent verifier reconstructs them from the parent circuit.
No optimality or new end-to-end kernel formalization is claimed.

Additional frozen operation-oriented tradeoff:
`CERTIFICATE_174_interior_packed_shifted.json` uniformly shifts the interior
packed targets by186, yielding minimum target348=2W,Dmax4914,Kcode5262.
This allows common degree-two homogeneous evaluation without negative powers.
It is included in the same independent verifier replay.
