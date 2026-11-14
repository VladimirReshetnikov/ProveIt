Additional bounded PA state-reduction searches
=============================================

Outcome: these searches did not produce a validated machine with fewer than
195 working states. They are evidence about the explicitly described search
families, not a lower bound for PA-consistency machines. The two reference
tables are the supplied PA195 and the separately validated scanner-eight
195-state alternative. No speculative grammar tie is advertised as a
standalone source-calibrated or consistency-equivalent machine.

All Python programs use the standard library and resolve their input paths
relative to this directory. Run Python without -O. The C++ programs require
a C++17 compiler. Programs write regenerated receipts into this directory;
the original recorded receipts and logs are preserved in recorded/.
Commands below assume the current directory is this packet, although the
Python file paths themselves may be invoked from any working directory.

References and provenance
-------------------------
reference_pa195/ contains the unmodified original PA195 checker and inputs,
including PROVENANCE.json, vendor_hashes.json, and both upstream licenses.
pa195_scanner8/ contains the validated alternative table, grammar, eight
folds, complete local certificate, source, startup, and verification record.
Its verifier uses the shared reference_pa195/ directory immediately above it.

One or two additional contextual routers
----------------------------------------
A router h has rows (0,R,u0) and (1,R,u1), where its two targets are controls
of the original raw table. It may be used as a helper inside replacement
fold detours. A net saving requires more additional folds than new routers.

added_router.py explicitly inserts each useful router and recomputes fold
opportunities and maximum matching. Both variants are recorded: conservative
incoming histories that include the new helper's two edges, and a broader
mode that omits those artificial edges from the raw simulation premises.
In the broader mode the helper is absent from the simulated raw machine;
every use in the quotient lies inside an explicitly checked local detour.

router_fast.py implements the same optimistic filter by recording missing
read-bit requirements on candidate fold edges. For two routers it combines
their enabled bit masks before constructing the edges, so two complementary
partial providers are included. A maximum matching is only a discovery
bound: any promising result must also pass the simultaneous local trace
certificate, full source binding, quantified runtime, and exact startup.

For the fixed original grammar, 1,147 useful one-router implementations were
screened; for the fixed scanner-eight grammar, 1,287 were screened. Neither
conservative nor broader mode achieved an optimistic count below 195.
After dropping signatures that supply no missing edge bit, the corresponding
fast screens have 1,107 and 1,258 routers. The fixed two-router screens also
have optimistic minimum 195: 625/761 signature groups produce 533/969
distinct combined edge sets for the two reference grammars, respectively.

Commands:
  python added_router.py
  python added_router.py --ignore-new-incoming
  python added_router.py --scanner8
  python added_router.py --scanner8 --ignore-new-incoming
  python router_fast.py
  python two_routers.py

The 200 retained scanner-eight grammar records in scanner821101.ndjson and
scanner_cross21202.ndjson represent 141 distinct trees. One- and two-router
screens over these 141 trees found no optimistic count below 195. These
records preserve the macro word as part of their discovery construction;
they were not all independently calibrated against complete source/runtime
contracts. Only a survivor would enter that expensive validation pipeline.

Command:
  python scanner8_router_ties.py

router_filter.cpp supplies a faster optimistic C++ filter for the same
old-target router family, also usable with all original controls as candidate
fold states. Native start74 is excluded by this filter and checked separately
below. Its repeated whitespace input format is:
  state_count shape_count helper_count desired_state_count
  q write0 direction0 next0 write1 direction1 next1    (one row per q)
  shape_state_1 shape_state_2 ...                     (shape_count entries)
Directions in this interface are 0=L and 1=R. helper_count is 1 or 2.
The JSON output gives groups of router target pairs and optimistic hit pairs
of group indices. For a one-router hit the two indices are equal. An exact
checker must test all relevant implementations, since different members of
one signature group may have different local trace compatibility.

Command:
  g++ -O3 -std=c++17 router_filter.cpp -o router_filter

Mixed transition-row merges and pure aliases
--------------------------------------------
mixed_merge.py attempts to identify two eligible controls and retain one row
from each parent. It preserves protected register-block oracle rows and
their target labels. Every contract whose old trace visits either modified
control is checked; an unchanged trace cannot notice the edit. Any survivor
must then pass every contract and the exact blank startup. There were
28,249 attempts on original PA195 and 28,254 on scanner-eight PA195, with no
survivor of the quantified runtime screen.

full_alias.py and scanner8_alias.py perform the simpler global h-to-u
identification with the keeper's two rows unchanged. Each tested 32,786
eligible aliases; none survived the same contract screen. The register
oracle protection and 1,024-inference fuel of the inherited checker are part
of these bounded search families. Failure is not a proof that an arbitrary
slower implementation, or its eventual blank behavior, is inequivalent.

Commands (the mixed-row runs may take several minutes):
  python mixed_merge.py
  python mixed_merge.py --scanner8
  python full_alias.py
  python scanner8_alias.py

Finite abstract source invariant
--------------------------------
abstract_reachable.py computes a product-domain register invariant from the
exact source seed at ordinal25, using values 0,1,2,3 and the interval [4,infinity).
It separately checks the resulting table's seed inclusion and every abstract
CFG successor. Thus the claimed branch exclusions come from an inductive
finite certificate, not from bounded concrete executions or Con(PA).
The invariant retains 3,697 of the 3,700 source sites and 4,810 of the 4,815
primitive cases. The five removed cases do not expose an unused transition
row in either reference table after accounting for all retained contracts,
the exact startup, and conservative register-block oracle coverage.

Commands:
  python abstract_reachable.py
  python abstract_reachable.py --scanner8

The earlier unrestricted row census and incoming-bit rerouting census are
also included as unused_rows.py and context_reroute.py. The full contract
family uses all 390 transition rows after startup and oracle coverage.

Projected-start contextual folds
-------------------------------
The native start74 has only incoming (0,R) edges. Its initial blank left
neighbor is also zero, so a contextual fold could legitimately project the
start into another keeper control. The standard quotient utility prohibits
changing start74, so this possibility was searched separately.

start74_pairs.cpp enumerates arbitrary replacement actions for the keeper's
two rows, allows repeated visits to the keeper inside a detour, and uses exact
cycle detection on the finite two-cell configuration space. Both current
bits and both stipulated neighbor bits are checked; therefore the blank
start case is included. It finds no survivor among 52 eligible pairs in the
original table and 51 in the scanner-eight table. Its scope is two-cell
detours with opposite known neighbor bits and uniform incoming direction.
It does not exclude broader initial-state rewrites.

Commands:
  g++ -O3 -std=c++17 start74_pairs.cpp -o start74_pairs
  ./start74_pairs reference_pa195/pa195.native.tm replay_start74_original
  ./start74_pairs pa195_scanner8/pa195_scanner8.native.tm replay_start74_scanner8

Seeded grammar crossover discovery
----------------------------------
scanner8_crossover.cpp starts from the locally certified effective-cost60
grammar used in the scanner-eight alternative. The effective score is the
number of allocated AX readers minus the compatible contextual folds, before
adding 135 fixed controls. Rotations preserve the token word, and crossover
replaces a subtree by another tree with the same flattened token word.
The added scanner permits the relaxed seven-zero address condition in this
discovery scorer; that condition by itself is insufficient to establish
source/runtime correctness. Full validation remains necessary for any hit.

The recorded run used seed21202, three million proposal slots, and obtained
no cost59 candidate (which would correspond to 194 states after the scanner
addition). Its final100 retained tie records are included. The companion
root run used seed21101 and five million proposal slots, also with no cost59
candidate. Discovery replay can depend on C++ implementation details; the
retained grammar records are explicit inputs to the finite router screens.

Commands:
  g++ -O3 -std=c++17 scanner8_crossover.cpp -o scanner8_crossover
  ./scanner8_crossover 3000000 21202 replay_crossover

What this packet establishes
---------------------------
It records unsuccessful attempts in several concrete reduction families and
supplies their code and finite input records. It does not certify the optimality
of 195, does not claim a new proof-assistant theorem, and does not promote an
unvalidated low state count to a consistency-equivalent Turing machine.
