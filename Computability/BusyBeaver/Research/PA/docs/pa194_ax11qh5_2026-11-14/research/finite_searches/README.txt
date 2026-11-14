Finite physical-reduction experiments
====================================

Outcome
-------
No new machine below 194 states was established by these experiments. The
194-state AX11QH5 input is the parent task's accepted fallback candidate;
this directory only records attempts to reduce it and an existing runtime
core. It does not claim a state-count lower bound.

The work is pinned to ProveIt commit
4be5c6e3a10292a7466f5d3687e3b39615ff049b and the exact local AX11QH5 inputs
recorded in manifest.json. All paths in the commands below are relative to
this directory. Python 3 and a C++17 compiler are sufficient; no network,
repository checkout, Lean installation, or external library is required.

1. Four edits to the existing 193-state runtime core
--------------------------------------------------

The starting table is an inherited 193-state core. It correctly implements
the primary source program on represented runtime frames, but its original
blank startup runs into an outward ray. It is not an accepted consistency
machine. Its q301/q88 quotient and changed q51 marker rule were already
present in the incoming research, and are not new contributions here.

The fixed pool contains 346 alternate row actions: 327 outside the arithmetic
boxes and 19 speculative arithmetic-box edits. A member's presence in this
pool is not a theorem that arbitrary combinations preserve the runtime.
This search looks for a complete startup frame first; any hit would still
require fresh joint runtime and logical verification.

The new search allows up to FOUR edits at distinct transition rows, starting
from native control 74 on a completely zero tape. It branches on the first
encounter of each editable row. Thus it avoids enumerating edits which the
selected startup never executes. The current row table is static throughout
each run. Rows assigned the unchanged action are not reconsidered later in
that run. Each changed branch is restored before a sibling is explored.

A frame hit must match the entire finite one-support, at native q84, for
one of the source paths 25..44. All nine work-register values may be arbitrary;
there must be at least one spare register. The left marker, the padded
address (padding 48+n, n>=0), the right marker, every unary register block,
and the zero exterior are checked. These intentionally generous frames
would only nominate a machine for further semantic analysis.

A run stops after 100,000 literal transitions, at absolute head position
above 20,000, or with more than 20,000 one-cells. It can stop earlier at halt,
at a proved outward blank ray, or at an EXACT repeated configuration.

Recorded result:

  Dynamic branch runs                247,094
  Literal transitions            172,579,287
  Complete source frames                   0
  Certified outward rays             181,281
  Exact configuration cycles          63,943
  Literal halts                            0
  Bounded/unresolved runs              1,870

The last four classifications sum to 247,094. The 2,000,000-branch cap was not
reached. Earlier triple runs are not included: the latest AX11 incoming
packet already explored triples. These counts are not to be added to its
counts as though the domains were disjoint.

Reproduce:

  mkdir -p replay
  g++ -O3 -std=c++17 code/search_multi_startup.cpp -o replay/search_multi_startup
  replay/search_multi_startup inputs/runtime193.native.tm inputs/edits.tsv inputs/startup_any_frame_templates.tsv 4 100000 74 2000000 > replay/multi4.jsonl 2> replay/multi4.log

A successful replay reproduces the counters above; elapsed time varies.
The hit file is empty. Every bounded case remains unresolved beyond the
stated cutoff, and this search excludes other edits, other starts, other
source-entry conventions, and different tape encodings.

Why the early classifications are proofs
---------------------------------------

Outward rays: the detector follows read-zero transitions through a finite
control path and cycle. It requires all their moves to have the same
direction and the current head to be strictly beyond every one-cell in
that direction. The successive head cells are therefore fresh zeros.
Induction on the number of steps proves that the head continues outward
and the finite control cycle repeats. The written bits are left behind and
cannot affect a future read. The detector refuses to rely on an editable
zero row whose choice has not yet been fixed. Its ray test can consequently
miss a ray, but a reported ray has the stated sufficient condition.

Exact cycles: a 64-bit hash only locates a possible repeated configuration.
On a hash match the checker replays the run to the earlier time and compares
the state, head, and WHOLE finite one-set. A hash collision is not accepted
as equality. Determinism then proves periodic nonhalting. The replay uses
the fixed currently selected row table; changes explored in child branches
have already been restored. Again these proofs concern the particular
rejected startup run; they do not prove the desired Con(PA) equivalence.

2. All-pair local contractions of the new AX11QH5 candidate
---------------------------------------------------------

This input has 194 working controls and 388 rows. Its source has 3,732 primitive
sites and 4,839 branch-sensitive outcomes. Its exact blank startup takes
58,088 transitions. These facts and the startup tape are in the input
receipt; the parent construction supplies the correctness argument.

The context collector expands every symbolic source outcome. It includes
all positions inside accelerated constant-symbol sweeps, so scan interiors
are not lost. Correlations between independent segment lengths are dropped,
which enlarges the context set. It also adds the exact blank-prefix windows.
For each of the 23 arithmetic-engine controls it uses ALL 8,192 possible
13-cell windows; none of their interiors is constrained by a trusted oracle.
The complete input consists of 219,298 control/window pairs, at radius 6.

For every pair of controls, the search tries a simultaneous two-row quotient.
The new representative can revisit itself while executing either read case.
First-action targets include every working control and the external halt
label 254. Each prospective replacement must catch up with the old one-step
outcome
within 250 literal transitions while staying inside its 13-cell window. It
must reach the same head and whole window, with only the deleted control
renamed to the representative. Writes or moves outside the window are
rejected. Halting states are handled as external labels.

Recorded result:

  Control pairs                       18,721 = 194*193/2
  Provisional single-row actions  24,904,168
  Joint action combinations          172,403
  Contractions                             0

Reproduce the prepared context search:

  g++ -O3 -std=c++17 code/merge_even.cpp -o replay/local_quotient
  replay/local_quotient inputs/ax11qh5.machine.native.tm 6 250 inputs/ax11qh5.safe_patterns6.txt > replay/ax11_merges6.jsonl 2> replay/ax11_merges6.log

The historical source filename merge_even.cpp reflects its first use on
the parity scheduler; the implementation accepts any table on the command
line. The exact source and output in this directory are the AX11QH5 run.

To regenerate the contexts independently from the source instructions:

  python3 -B code/collect_ax11_contexts.py inputs/ax11qh5.machine.native.tm inputs/ax11qh5.sites.json inputs/ax11qh5.instructions.json replay/ax11_contexts.txt 6

The regenerated file may order its lines differently from the preserved
input, but its set of control/window pairs must be identical. The search
sorts the relevant test cases, so its numerical counters are unaffected.

Why a passing local test would have been sufficient
---------------------------------------------------

The unchanged exterior of each window is arbitrary. Local success is exact
configuration equality, so the finite trace can be inserted at every old
visit whose window belongs to the cover. A cover of the full startup and
all represented source outcomes gives the required induction invariant.
Positive replacement durations allow old finite runs to be expanded into
new finite runs. Determinism fixes the intervening computation. This is a
proof method for a proposed quotient; because no quotient passed here,
there is no new simulation theorem or machine to promote.

The test space is restricted to this deletion/renaming construction, this
context cover, and the 250-transition local cutoff. It says nothing about
all possible 193-state implementations, alternative register encodings,
or new source calculi.

3. One extra helper-row rewrite for a history-sensitive fold
----------------------------------------------------------

The second new synthesis stage allows a further non-arithmetic row change.
For each pair of non-arithmetic controls it examines the known preceding
bit separately for each current bit. If a previous bit distinguishes the
two controls, a leftward detour may recover that distinction through an
existing provider. One provider branch may be replaced by a preserving
rightward action to another existing control. Both quotient branches and
the one helper rewrite must be compatible simultaneously.

Every affected old configuration is then simulated against the old
one-step target on the COMPLETE final patched table, including recursive
visits to the representative and helper. The helper is tested first,
followed by the two merged controls. Arithmetic boxes are not modified.

Recorded result:

  Non-arithmetic control pairs        14,535 = 171*170/2
  Compatible provider proposals           54
  Local window tests                      54
  Contractions                             0

All 54 proposals failed on their first helper-window test. This search is
broader than pure two-row quotienting, but is only one specific provider
construction; it is not an exhaustive search over all three-row changes.

Reproduce:

  g++ -O3 -std=c++17 code/merge_with_helper.cpp -o replay/merge_with_helper
  replay/merge_with_helper inputs/ax11qh5.machine.native.tm inputs/ax11qh5.safe_patterns6.txt 6 250 > replay/ax11_helper_merges6.jsonl 2> replay/ax11_helper_merges6.log

4. The sparse-scheduler combination
----------------------------------

The incoming H5 packet contains a 195-state parity scheduler PA195EvenHX.
The quotient deletes native control 301, redirects every target 301 to 88,
and sets (88,0) to (0,L,51) and (51,0) to (0,R,122). Applying this known
193-core quotient to that 195-state table would give 194 controls, but the
literal blank execution rejects the combination: after
93 transitions it is at q35, head 15, with one-support {-3,1}. Its q35/0 row is
1R35. The new parity-scheduler control 3000 has not been visited. The outward
ray proof above therefore applies immediately. This does not reduce the
parity scheduler to an accepted 194-state blank-start machine.

Reproduce the exact short rejection:

  python3 -B code/check_parity_rejection.py

Attribution
-----------

The runtime core, edit pool and frame templates come from the QN6 incoming
packet's physical_search inputs, ultimately from James Chang's PA196 work
and later ProveIt research. merge_even.cpp adapts its joint_return_merge.cpp;
the context collector adapts collect_source_contexts.py and uses the supplied
symbolic executor. The four-edit dynamic search and the helper-row synthesis
were prepared in the present task. Preserve the included licenses when
redistributing these materials. Original imported inputs are unchanged.
