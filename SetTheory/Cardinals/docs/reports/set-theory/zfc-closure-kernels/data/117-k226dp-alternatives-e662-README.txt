E662: conservative fresh-query constant, separate from the K-based machine
=======================================================================

Run with Python 3 and only the standard library:

    python build_e662.py

The exact retained baseline_E663.json is recovered from the formalisms/e663
companion in ZFC235_Construction_2026-10-19.zip at ProveIt commit 0128d662fd.
The builder checks the inherited packet's bit-character SHA-256 before any
change. ATTRIBUTION.baseline.txt is copied unchanged from that delivery and
describes its predecessor work, not the new fresh-constant observation.

New result: append one fresh nullary operation e, unchanged axioms, query e=d.
The explicit finite-proof transformation in proof.tex proves equivalence to
the inherited Q(d)=d query. The complete packet has 662 bits rather than 663.
The generated directory contains the exact equation ASTs, readable equations,
ASCII bits, packed bytes with a separate bit-length file, and a check receipt.

The seven original equations, their ordinary raw-EPSC/ZFC interpretation,
and the codec remain inherited and retain their attribution. This companion
does not instantiate or alter K230 and does not claim a Turing-machine bound.
It is a useful target for a future equational interpreter experiment.
