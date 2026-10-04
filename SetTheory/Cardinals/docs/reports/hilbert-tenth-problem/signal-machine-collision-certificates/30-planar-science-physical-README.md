# Five-live-signal planar realization packet

The mathematical result is in `PROOF.md`: every rational 2 by 2 matrix of positive determinant is realized by an exact complete rational-speed number-preserving word with exactly five live signals. Its normalized chamber is a bounded rational open polygon containing the center. Full messenger phase closure, zero pivots, negative diagonal entries, the identity target, and a finite rational centered-dilation decomposition are included.

`static_planar.py` is newly authored standard-library exact/static algebra. It was read before execution. It constructs endpoint rows, a word grammar and rules; it never chooses or simulates a collision and imports no earlier program. Run `python static_planar.py` to reproduce the 75 fixture outputs in `evidence/`. The script also runs with Python optimization because validation uses explicit exceptions rather than removable assert statements.

`evidence/summary.json` lists each output and its hash, the checks performed, and limits. The checks are supporting finite evidence rather than an all-input proof, formal certificate, arithmetic frontend, or empirical chronology simulation.

`PACKET_MANIFEST.json` pins the proof, source and evidence bytes. The manifest excludes itself. The spectral corollary in proof Section 8.1 is explicitly conditional on the separately authored companion classification; it is not needed by the physical theorem and is not silently pinned as part of this packet.

This packet leaves all prior reports unchanged. No priority, minimality, uniform unchanged-machine, singular-matrix, or negative-determinant realization claim is made.
