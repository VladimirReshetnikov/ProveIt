# Sources and provenance

## Exact predecessor

The predecessor supplied by the parent task was:

* `ZFC_Diophantine_Centered_Compression/certificates/PROOF.md`
* `ZFC_Diophantine_Centered_Compression/certificates/core.py`
* `ZFC_Diophantine_Centered_Compression/certificates/build_dag.py`

This packet changes the orientation of two residuals, doubles A0, adds the top guard, recovers geometry from boundary identities, and develops two new exact graph-fusion interfaces. It does not alter the predecessor's tile compiler or its claimed source calibration. The direct evaluator and fixed-power DAG builder are derived from the predecessor; the new proof and tests accompany their changes. Source hashes are recorded in PROVENANCE.json.

The parent task identified public ProveIt revision `7e533c33819ee1f703b69f2778a767cdc069940d` and the `Computability/DiophantineConsistency/con-zfc-diophantine-forms` collection as its comparison baseline. This packet's arithmetic theorems need only the explicit predecessor definition, not any unverified assertion about that repository's latest status.

## Primary mathematical background consulted

* Yuri Matiyasevich, *A new proof of the theorem on exponential Diophantine representation of enumerable sets*, 1976 (English translation 1980): https://www.mathnet.ru/eng/znsl2072 . This is historical background on direct computational arithmetization, not a source for a numerical witness budget here.
* Yuri Matiyasevich, commentary to Chapter 5 of *Hilbert's Tenth Problem*: https://logic.pdmi.ras.ru/~yumat/H10Pbook/commch_5.htm . The author distinguishes computational encodings and elimination of bounded quantifiers.
* Jonas Bayer, Marco David, Malte Haßler, Yuri Matiyasevich, Dierk Schleicher, *Diophantine equations over Z: universal bounds and parallel formalization*, version 2: https://arxiv.org/html/2506.20909v2 . This provides primary-source context for masking, binomial divisibility and explicit accounting of special-function elimination. None of its asserted universal pairs is silently substituted for a literal graph implementation in this packet.

Binary Lucas parity and both synchronization lemmas are proved directly in PROOF.md. The new positional guard and fusion theorems are established there independently; no claim of literature-wide originality is made.
