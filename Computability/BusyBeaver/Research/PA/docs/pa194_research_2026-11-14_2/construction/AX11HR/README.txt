PA194AX11HR -- an alternative physical register representation
============================================================

machine/machine.tm is the exact dense binary table: 194 working states,
start 0, terminal 194, 388 rows. The tape extends infinitely in both
directions, is initially entirely zero, and the head starts at position 0.
Each row has state, read symbol, write symbol, L/R, next state. The halt
state has no rows and is not counted.

Dense SHA-256:
b3c07bf7a750e1e9529929ef392fc0543645ccc34a7a39c3360ec41201f0e980
Native SHA-256:
22015a7d643f69711b7f5948afd99e9fa2282d754a3a36d95b5f755c3e4f5e39

The native table starts at 74 and halts at 254. labels.json gives the exact
dense/native conjugacy. The construction is based on the pinned AX11H
table in inputs/base; it is not based on the QGH candidate.

What changes
------------
The logical register order is (N,T,W,A,D,H,X,Y,L). Its old physical
positions [6,2,0,4,3,7,8,5,1] become [6,1,5,7,4,8,2,0,3]. The induced
physical permutation is [5,3,1,4,7,0,6,8,2]. Ten non-box routing rows change;
every changed row is used during the exact blank initialization.
The arithmetic-box rows and the complete 3,671-site source graph remain
unchanged. Both primitive source resolvers independently reconstruct it.

The whole initial frame is reached after 48,320 transitions, compared with
57,922 for the base AX11H table: a reduction of 9,602 (about 16.58 percent).
This is an initialization result, not a claim about total proof-search
speed or about global optimality of the physical layout.

Verification and proof status
-----------------------------
From this directory, using Python 3.10+ with assertions enabled:

  python3 -B verify_all.py

The full mode reconstructs all literal and source files in a temporary
directory, checks the complete blank startup, reruns every independent
literal source contract, compares all fresh contracts with the supplied
ones, and checks full endpoint closure and positive affine durations.

  python3 -B verify_all.py --quick

Quick mode explicitly skips the per-site literal replay. It still checks
input identities, the entire reconstruction, the whole blank startup,
and the recorded endpoint and duration bindings. It is not the full replay.

Individual commands:

  python3 -B build.py --output /tmp/pa194ax11hr-built
  python3 -B verification/check_literal.py --output /tmp/pa194ax11hr-literal
  python3 -B verification/audit_closure.py --bundle . --output /tmp/pa194ax11hr-closure.json

The independent interpreter derives four generic list lemmas from the
literal rows and checks 4,778 outcomes with arbitrary nine natural-number
registers, arbitrary nonempty spare lists, and arbitrary extra header gap.
No arithmetic-box oracle is used. The separate closure audit checks all
4,777 nonhalting source endpoints and all affine duration coefficients;
each duration has constant at least 3. The one halt duration is exactly 3.

The full written representation and iPRA clock proof is in the main report,
Section 'PA194AX11HR: a different physical register representation'. Its
logical calibration is the latest incoming AX11H written proof, preserved
unchanged in ../../reference/ax11h_written_calibration.zip. This research
does not claim a newly completed Lean theorem or a lower bound of 194.

Provenance
----------
ProveIt snapshot 1e1a41f799d4658b829cdd0eabae3775a0c8c4a0.
The base table and source graph come from the incoming
pa194_ax11h_research_2026-11-14.zip. Input identities are retained in
INPUT_SHA256.json and the top-level provenance records. The original
ProveIt, James Chang, and Wade notices are in licenses/.

verification/reference retains the inherited independent literal engine.
check_literal.py is adapted for the new physical positions and startup;
audit_closure.py is adapted only for layout and paths. The new work is the
physical allocation, active routing transformation, exact startup,
candidate-specific literal replay, and written representation proof.
