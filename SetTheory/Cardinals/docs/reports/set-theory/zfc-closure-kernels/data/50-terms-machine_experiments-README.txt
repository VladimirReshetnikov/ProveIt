Entry-action resynthesis and continuation obstruction
=====================================================

Baseline repository: VladimirReshetnikov/ProveIt
Pinned commit: fab89c5d26b81cd2ccab2ee5d213ff23725c7726
Old-label permutation252 table SHA256:
939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713

This packet contains no certified new 251-state consistency machine.
It supplies a new finite local-search family on the pinned 252 machine,
complete/partial records, independent search-space partition replays,
a literal 34-transition decoder identity, and a precise limitation of one
proposed continuation encoding. The LaTeX research_notes.tex is a section
intended for incorporation into the comprehensive report.

Search results
--------------
* Degree 1: all 132048 complete incoming-action rewrites rejected;
  203162 affine checks, 82.95 seconds; no survivor.
* Degree 2: 10845350 of 46738944 assignments pruned in 600.32 seconds;
  1094649 partial nodes, 1458444 affine checks; 35893594 assignments remain
  in 1093 disjoint frontier nodes; no survivor.
* Both independent whole-journal partition audits pass.

The permanent JSON and journal define the exact tested scope. Elapsed wall
limits are not reproducible counts. Fuel exhaustion and unsupported rules
are finite diagnostic failures, not semantic impossibility certificates.
No candidate reached the mandatory full 8391-case recheck or blank run.

Offline replay using the bundled minimal reference
-------------------------------------------------
Run these commands from this packet directory. They use only the Python
standard library, the supplied records, and the five files under ../reference/proveit/:

python3 -B replay_entry_partition.py --result entry_degree1.json \
  --table ../reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm \
  --output /tmp/entry-degree1-partition-audit.json
python3 -B replay_entry_partition.py --result entry_degree2.json \
  --table ../reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm \
  --output /tmp/entry-degree2-partition-audit.json
python3 -B continuation_obstruction.py --repo ../reference/proveit \
  --output /tmp/continuation-obstruction.json

The two partition replays check bookkeeping and coverage, not the reported
symbolic failures. The continuation replay checks the saved finite-window
trace, original residual collisions, and separate bounded mutant prefixes.
No network, git checkout, Coq, Lean, or nonstandard Python package is needed.

Optional fresh searches
-----------------------
The bundled reference is also sufficient for a new search; substitute
--repo ../reference/proveit in the following commands. A full local ProveIt checkout
at the pinned commit may be used instead:

python3 -B entry_resynthesis.py --repo /path/to/ProveIt --degree 1 \
  --output /tmp/entry-degree1.json --seconds 450
python3 -B entry_resynthesis.py --repo /path/to/ProveIt --degree 2 \
  --output /tmp/entry-degree2.json --seconds 600
python3 -B continuation_obstruction.py --repo /path/to/ProveIt \
  --output /tmp/continuation-obstruction.json

To audit a supplied record:

python3 -B replay_entry_partition.py --result entry_degree1.json \
  --table /path/to/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm \
  --output /tmp/entry-degree1-partition-audit.json

Replace degree1 by degree2 for the second audit. The auditor reads the
compressed .jsonl.gz journal automatically when raw .jsonl is absent.
The journals are 175184824 and 19251270 bytes after decompression; their
uncompressed SHA256 values are retained in the records. The compressed
forms keep the versioned artifact compact.

The scripts load the attributed strict affine executor and original
program decoder from the pinned repository. They never change the baseline
TM. A trailing transport newline, if present, is ignored only after
canonical re-encoding proves the table matches the exact pinned SHA256.
The original degree1 record predates removal of one transport-added LF
from each of its four source files. transport_normalization.json verifies
every original recorded SHA256 as the canonical bundled bytes plus exactly
one LF, and preserves the original record unchanged. Degree2 uses canonical
source hashes. reference_manifest.json identifies every bundled source.

LaTeX integration
-----------------
research_notes.tex has no preamble and may be included with
\input{research_notes.tex} in a standard article document. It defines its
own section and subsections, requires no additional LaTeX packages, and
does not introduce labels, bibliography keys, or global macro definitions.

Continuation results
--------------------
The 204-to-252 fold has a 34-move finite-window identity: with the prescribed
bits on [-11,6], it returns to 96/head 0 and clears only cell 6, regardless of
tape contents outside that window. The full literal trace is recorded.

Two ORIGINAL register-program residuals have effects
F(t,n,k)=(t,n+k,0) and G(t,n,k)=(t+n,n+k,0). On fibers n+k=s, any history
representation that deterministically reconstructs G from F requires at
least s distinct history labels, or ceil(log2(s)) bits in a fixed-width
binary encoding. Thus fixed finitely
many phase tags alone cannot repair that identification for all inputs.
One unbounded natural ghost n suffices. Spare tape, an entry recoding,
stronger invariants, or a nonfunctional relation are not excluded.

Actual mutated-table prefixes are recorded separately. They do not simply
follow the original alternate residual. The functional obstruction is not
a state lower bound and does not prove any global behavior of the mutant.

Attribution: Mira-Cult's original machine/calculus; Jeff's verification;
Wade's compiler framework; mira-emmy's public 253 reduction; ProveIt's
physical-register permutation and existing affine/continuation tools.
