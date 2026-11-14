U208: A CONDITIONAL TAPE-CONTEXT REDUCTION FOR CON(PA)
Research prepared for Vladimir Reshetnikov, 29 October 2026.

RESULT
======
machine/u208.tm is an explicit deterministic binary single-tape machine
with 208 working states, labels 0 through 207, and separate halt label 208.
Start state 0, head 0, blank tape; the initializer is included. All 416 rows
move L or R. Native labels are only names: native 211 is working, native 254
is halt. machine/state_map.json gives the exact native-to-dense bijection.

Dense SHA-256:
a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1
Native SHA-256:
b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135

Relative to the Joint U209 parent, the entire change is:
  delete state 172 (both rows)
  change 116/0 from 0 R 172 to 0 R 211
  change 211/0 from 0 R 157 to 0 L 217
Every other retained row and the complete source program remain unchanged.

The parent has two different reachable contexts: state 172 has preceding
bits 10, and state 211 reading 0 has preceding bit 1. A five-state inductive
invariant proves these facts on every initial tape from state 0. Four exact
local blocks of lengths 7, 1, 3, 1 and 414 ordinary row identities prove the
all-tape halting equivalence. The old/new first-halting clocks obey
  T208 = T209 + 6*N209(172,0) + 2*N209(211,0),
so T209 <= T208 <= 7*T209.

COMPARISON
==========
Six supplied U209 submissions give only TWO rooted labeled graph classes.
Plain, Compatible Folds, Composed, full Joint, and PDF-only Joint are class A.
Compatibility is class B. Compatible Folds and full Joint are byte-identical.
The PDF-only Joint table equals Plain, not full Joint byte-for-byte.
Both classes admit the new reduction. alternative/ contains the second,
nonisomorphic 208-state variant, using helper 214 instead of 217.

PROOF STATUS
============
The new local reduction has a complete ordinary mathematical proof and
small independent executable certificates. It is formalizable in PA.
Composing it with the retained source, numerical-calculus, startup, and
unary-theory arguments gives the PA-provable consistency equivalence:
  PA |- not Halt(U208,blank) <-> Con(U) <-> Con(PA).
There is no consistency assumption in this biconditional. Actual
nonhalting requires Con(PA). This release supplies no newly exported
end-to-end Lean, Rocq, or MM0 certificate for that endpoint and makes no
global minimality or independently ratified priority claim.

FRESH VERIFICATION
==================
* All five executable U209 packages' quick replays passed in separate copies.
* Independent comparison verifies all six tables and the same 3,909 primitives
  and 5,083 ordinal source control edges.
* Independent new invariant audit: 104 applicable Boolean implications;
  all 414 ordinary quotient rows; all 4 opaque-exterior macros.
* Exact 208-state/416-row table and dense relabeling; 12 damaged controls
  rejected; independent audit agrees byte-for-byte under normal Python/-O.
* Full fresh PRIMARY U208 symbolic replay: 5,084 arbitrary-natural primitive
  contracts, 1,251,865 symbolic inference applications,all 416 rows covered.
* Exact 48,140-step blank startup, full trace and complete tape unchanged.
* Independent C++ finite regression: 15,252 cases, 6,778,830 literal primitive steps.
  The finite cases and 2,000,000-step blank prefix are NOT proofs of nonhalting.
* Alternative 208 has exact local/history construction checks. A separate
  universal runtime replay for the alternative is not claimed.

OFFLINE REPRODUCTION
====================
Python 3.10+ and its standard library suffice. Run with assertions enabled:
  python3 -B reproduce.py
This verifies hashes and parent bindings, replays the selected parent's
quick checks, rebuilds both 208 tables, checks local proofs and startup,
compares the proposals, and rederives the 5,084 primary runtime contracts.
Temporary files are outside the sealed release.

For an external receipt:
  python3 -B reproduce.py --report /tmp/u208-replay.json

For a deliberately limited run:
  python3 -B reproduce.py --quick
The quick mode explicitly skips fresh universal runtime derivation.

Optional independent finite executor (C++17):
  g++ -std=c++17 -O3 code/check_finite_runtime.cpp -o /tmp/check_u208
  /tmp/check_u208 machine/u208.native.tm machine/sites.tsv

Rebuild PDF in a COPY to keep the sealed release unchanged:
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

CONTENTS
========
report.pdf/report.tex/paper/   Report, proofs, comparison, complete dense table
machine/                     Primary 208 table, state map, unchanged source
alternative/                 Nonisomorphic208 variant and corresponding parent
machine_parent/              Selected 209 table and legacy runtime-label map
code/,reproduce.py           Deterministic builds and executable checks
comparison/                  Six exact table presentations and fresh quick logs
evidence/                    Local, startup, runtime, finite, and replay receipts
reference/                   Full selected Joint ZIP with nested mathematical
                             ancestry and exact unary theory; source inventory
research/                    Discovery programs and bounded search receipts
licenses/,NOTICE.txt         Retained upstream attribution and terms
SHA256SUMS                   Every other sealed release payload

SOURCE SNAPSHOT
===============
VladimirReshetnikov/ProveIt, docs/incoming, at commit
343da82d7384d10ec9fd1c17361fc923b2d1d117.
All retrieved outer ZIPs were verified against their Git blob hashes.
Full URLs, names, sizes, and IDs are in reference/source_inventory.json.

The selected original Joint ZIP preserves the complete nested U212/U213/
U214/U218/U222 mathematical lineage and the user-specified unary-theory
archive. Its retained logical reference files have unbundled imports;
they are not advertised as a runnable new proof-assistant project.
