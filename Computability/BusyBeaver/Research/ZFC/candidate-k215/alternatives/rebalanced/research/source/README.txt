SOURCE-SIDE RESEARCH SUPPLEMENT
===============================

This folder records useful bounded searches and two side constructions. Neither
side construction is an additional accepted ZFC-consistency machine. The main
successful 215-state candidate is in ../../machine/.

Contents
--------
SOURCE_FINDINGS.txt gives the successful source result, ordinary proof chain,
ten-rotation recipe, and precise search boundaries. It includes the independent
runtime comparison: shorter addresses do not make every primitive case faster.

zero5/sites.json is a concrete source equivalent to the packet baseline, with
maximum zero run 5, 205 distinct subtrees, 4,751 primitive occurrences and depth
45. zero5/audit.json verifies the exact ordered primitive word and both complete
guarded control-flow graphs. Its restricted physical allocation failed; there
is no binary state-count improvement attached to this source.

register-swap08/ contains a direct exchange of N and L, registers 0 and 8. Its
source is an exact register permutation and its 215-state interpreter passed
all 6,176 symbolic cases. The original exploratory run retained only the summary,
not the complete ordered case records. The literal blank machine halts after
15,607 steps, so this is excluded as a consistency machine. The separately
replayable startup-halt.json records that failure. No consistency claim is made
for this table.

The C++ all-start scanner checked all 215 existing states as possible blank-tape
starts, with one million transitions per start. It found 210 exact outward rays,
three halts, and two bounded unresolved runs (states 66 and 94), and no safe root
seed. all-starts-control.json records the same scan of the accepted primary
machine, including its exact known 95,714-step seed. all-starts-review.json
states whether the portable Python audit replayed every recorded run. The two
bounded runs remain unresolved; this is not a theorem excluding all starts.

search-summaries.json preserves search caps, frontier sizes, best source metrics,
and restricted allocator failures without the large frontiers or every table.
The records are bounded empirical searches, not global minimality proofs.

Portable finite verification
----------------------------
Run from the packet root. Python 3.10 or later and the included vendor utilities
are sufficient; no network or optimizer is needed:

  python3 -B research/source/verify.py

That checks zero5 source equivalence, reconstructs the N/L table and source from
the exact packet baseline, replays the blank halt, checks all-start record
metadata, and replays the primary start-0 positive control. To independently
replay all 430 stored runs, including the bounded endpoints:

  python3 -B research/source/verify.py --replay-all-starts

The saved verification.json and verification.log come from that stronger mode.
The audit does not rerun the full symbolic N/L interpreter derivation.

Optional full N/L interpreter recheck
------------------------------------
The packet includes the unchanged symbolic runtime checker. Choose a fresh
output directory and run, from the packet root:

  python3 -B runtime/validate_native.py research/source/register-swap08/candidate.native.tm research/source/register-swap08/sites.json nl-runtime-recheck

The expected runtime result is UNIVERSAL_MATHEMATICAL_PASS with 6,176 cases and
215 working states. That result is still insufficient for a consistency machine:
the initialization halts. This inherited checker's startup routine may label
state 254 UNDEFINED because the halt state has no outgoing rows; verify.py
recognizes it explicitly as HALT and checks the exact 15,607-step execution.
The recheck emits full ordered case records and takes roughly a few minutes.
It is an ordinary mathematical checker, not a proof-assistant kernel theorem.

Optional C++ scanner reproduction
---------------------------------
From the packet root, with a C++17 compiler:

  c++ -O2 -std=c++17 research/source/scan_swap_starts.cpp -o scan-swap-starts
  ./scan-swap-starts research/source/register-swap08/candidate.native.tm 1000000 > swap-starts-repeat.json
  ./scan-swap-starts baseline/k215.native.tm 1000000 > starts-control-repeat.json

The scanner emits summaries and safe-seed tapes, not giant raw traces.

Attribution
-----------
The source-search agent authored the supplement's new search, reconstruction,
and verification code. The source language, machine architecture, calculus,
baseline source/table and symbolic runtime retain their upstream ancestry.
See the main packet's licenses and notices. The selected rebalanced table is
audited independently elsewhere in the packet.
