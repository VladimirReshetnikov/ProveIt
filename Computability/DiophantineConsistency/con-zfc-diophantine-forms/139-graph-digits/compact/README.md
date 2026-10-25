# A lower center for the doubled product square

This portable component defines a fixed polynomial in ten strictly positive
integer variables with **87 binary arithmetic operations and exact degree
323**, and a sharp-center sibling with **88 operations and degree 318**.
These are new operation/degree tradeoffs relative to the retained
85/328 and 89/288 points. The ordinary proof establishes positive-zero
equivalence to the package-133 parent, including a constructive positive
converse and an explicit bijection of the positive zero sets. Its Con(ZFC)
meaning inherits the parent's identified native and
refutation calibration.

The authoritative equations are `equation_87_degree323.json` and
`equation_88_degree318.json`; the complete
ordinary new proof is `PROOF.md`. Every fixed coefficient is included in
`coefficients/` and independently tied by its raw hash and bit length to the
whole retained parent tuple. `construct_coefficients.py` computes those four
integers from the full finite printed recipe, including the 436-character
machine numeral and all 943 indexed tiles. No extra input coefficient port
remains unspecified.

Run with Python 3.10 or newer, standard library only:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B build.py
python3 -B verify.py
```

The first two commands verify the delivered circuit, pinned source bytes,
fixed numerals, four exact polynomial identities, liveness, cost and exact
degree, and reject three changed-gate controls. The last two rebuild all
four compressed coefficient payloads and the circuit, then check the result.
Gzip bytes may depend on the Python/zlib version; rebuilt files carry their
correct new compressed hashes. Their raw integers, graph, and mathematics
are identical across versions. No network or original checkout is needed.

`upstream133/` contains the exact pinned parent circuit, ordinary new and
inherited kernel proofs, printed constant recipe, source ledger and audit
text. `provenance/SOURCE_PINS.json` authenticates every copied byte by its
original Git blob ID and SHA-256. Historical references inside the copied
texts retain their original scope. This component does not claim to ship or
rebuild every transitive native/compiler proof file or a new object-ZFC
proof term; it preserves those mathematical dependencies explicitly.

The new code, proof and checks were produced with AI assistance. Independent
review means a separately tasked agent audit in this workflow, not external
human endorsement. No proof of consistency or global minimality is claimed.
