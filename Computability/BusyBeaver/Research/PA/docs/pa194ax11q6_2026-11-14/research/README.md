SCOPED MERGER SEARCHES AND A REJECTED STARTUP COMPOSITION
=======================================================

This directory packages six newly completed finite searches, their original
logs and empty hit files, exact input tables, context envelopes, provenance,
and portable replay programs. None of the six searches found an accepted
one-state reduction. These are results for a specified sufficient local
simulation criterion, not a lower bound on consistency Turing machines.

Recorded searches
-----------------
All passes use fuel 120 for each local old-transition simulation.

```text
Name             Machine          Context method             K   Pairs   Hits
even_cyclic      PA195EvenHX       all-tape abstraction        5   18721      0
even_blank       PA195EvenHX       blank-start abstraction     7   18721      0
even_source      PA195EvenHX       source + exact bootstrap    6   18721      0
primary_source   primary PA194     source + exact bootstrap    6   18528      0
ax11q6_blank     PA194AX11Q6       blank-start abstraction     7   18528      0
ax11q6_source    PA194AX11Q6       source + exact bootstrap    6   18528      0
```

There are 111,747 pair instances across the six passes. Repeated pairs in
different envelopes are counted separately. The logs' partial count records
replacement zero-rows surviving the first screening phase; it is not a count
of accepted reductions. search_manifest.json retains every final DONE count.

Reproduction
------------
From the enclosing release directory, the quick integrity/replay command is:

    python3 research/replay_search.py --verify-only

It checks the bound file hashes, complete table structure, recorded DONE
counts, empty hits, exact source/bootstrap set unions, and the complete
93-step diagnostic trace followed by its outward-ray invariant. It does not
repeat the six searches or the symbolic source collectors.

Compile the three engines and run a four-state positive fixture:

    python3 research/replay_search.py --smoke

This fixture has an explicitly known valid identification. Each compiled
engine must find the exact corresponding pair of replacement rows.

Rerun the six complete searches:

    python3 research/replay_search.py --all

Or rerun a named pass, for example:

    python3 research/replay_search.py --case ax11q6_source

The full replay requires g++ with C++17 and the usual libstdc++ headers;
Python requires only its standard library. CXX or --cxx can select the
compiler command. All paths are derived from the script location, so no
Git checkout or network access is needed. Temporary compiled executables
are removed after use. Output defaults to research/replay-output/; --out
selects another destination. Recorded files are preserved by default.
Do not use Python -O: assertions are verification checks.

Regenerate all three source envelopes, then augment and compare them:

    python3 research/reproduce_contexts.py

For just the short literal-bootstrap reconstruction, use:

    python3 research/reproduce_contexts.py --bootstrap-only

Each program also accepts --case and --out. The complete source collection
replays approximately 1.5 million symbolic operations per input. It retains
the inherited arithmetic-box abstraction. It is separate from the new
candidate's independent literal physical audit in candidate/verification/.

Exact family searched
---------------------
The search enumerates every unordered pair of NONINITIAL working controls.
It identifies the earlier listed control with the later one and synthesizes
both rows of the survivor. It redirects all incoming targets of the removed
control. Each replacement row may write zero or one, move left or right,
and target any surviving working control. The generated replacement rows
do not target halt directly. No other original row is edited.

For each original control in the pair and each supplied tape context,
the original one-step effect must be reproduced in 1 through 120 steps
of the FINAL modified table. At the match, the entire local tape window,
head position, and successor after state identification must agree exactly.
Repeated intermediate visits to the survivor execute the same synthesized
rows, so cyclic local paths are evaluated jointly. A repeated local
configuration, departure from the window, or exhausted fuel rejects that
candidate simulation. Positive time is required for every old step.

Radius K denotes tape positions -K through K relative to the original head.
The abstract window transition relation permits either value of every newly
entering boundary cell. The all-tape pass starts with every possible window
at the original start control. Blank passes start with its all-zero window.
Both take the finite abstract forward closure. The source passes begin with
the all-tape envelope and replace only explicitly represented non-box
controls by their source/bootstrap windows. Other controls retain the
original abstraction; the arithmetic engine is not narrowed by source
oracle endpoints.

These restrictions exclude initial-state identifications, larger quotients,
coordinated edits elsewhere, new helper states, direct halt-target synthesis,
longer detours, head-displaced match relations, and redesigned source
languages. Overapproximated contexts can also reject a valid reduction that
does not satisfy this stronger local criterion. No completeness statement
outside this exact family is made.

Source contexts and finite initialization
----------------------------------------
The source collectors enumerate both decrement outcomes at every source
site. They include the interiors of accelerated constant-symbol self-loops,
not just symbolic endpoints. The two collectors differ only in the physical
H/X register placement needed by the even-candidate machine. Original source
envelopes intentionally omit startup; augment_bootstrap.py then adds every
window of the exact finite blank initialization, INCLUDING its final endpoint.
Only controls already narrowed by the source collector are augmented.

```text
Machine       Source contexts  Added  Augmented contexts  Bootstrap transitions
PA195EvenHX            29426     23               29449                  44094
primary PA194          29400     44               29444                  58154
PA194AX11Q6            30928     45               30973                  58320
```

All three prefixes end at native control 84 with head -2. The exact complete
finite tape support is retained in recorded/*_bootstrap_receipt.json. Those
receipts are freshly reproducible from the supplied literal tables. An exact
finite prefix is not, by itself, an argument for infinite behavior.

Rejected even/runtime combination
--------------------------------
diagnostics/even_runtime194.native.tm combines the supplied even scheduler
with the initialized-runtime identification 301 -> 88. In addition to target
redirection, it sets (88,0)=(0,L,51) and (51,0)=(0,R,122). The result has 194
working states but fails the intended blank initialization. After 93 steps
from native start 74, it is at control 35, head 15, with ones at -3 and 1.
The zero transition returns to the same control and moves right. Every
future scanned cell is zero, and the finite support remains behind the head.
The quick replay checks the exact full trace, the mutation relative to the
even parent, and this inductive ray condition. This table is a rejected
diagnostic, not another delivered consistency construction.

Files and provenance
--------------------
src/ contains the exact C++ sources used for the recorded searches.
recorded/ contains the unchanged six progress logs, six empty hit files,
original source-collector receipts, new bootstrap receipts, and packaging
smoke/integrity receipts. contexts/ retains both unaugmented and augmented
tables. inputs/ contains the supplied even and primary inputs. The AX11Q6
inputs are referenced by portable ../candidate/ paths in the manifest.

reference/haz/ is an unchanged compact historical dependency set, including
its original provenance, mathematical references, runtime, compiler, and
license notices. Its internal provenance names earlier snapshots; the outer
PROVENANCE.json binds every copied member to the current audited commit
4be5c6e3a10292a7466f5d3687e3b39615ff049b. Copied files were compared byte for
byte with their pinned archive members. The primary collector is likewise
unchanged. The even collector changes only the physical H/X placement.

The six C++ searches, bootstrap augmentation, literal diagnostic replay,
portable wrappers, and packaging receipts are new work for this release.
The original source language, numerical calculus, tape engine, symbolic
runtime, earlier machines, and inherited context collector remain credited
to ProveIt and their upstream authors. Historical notices/licenses are
retained in reference/haz/licenses/. Nothing here is presented as an
independent Lean or Rocq kernel theorem.
