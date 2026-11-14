LOGICAL AND SOURCE RESEARCH: SCOPE, RESULTS, AND REPLAY
====================================================

This directory records additional research performed after reading the supplied
U209 and U208 packets. It does not contain an accepted machine with at most 207
working states. Source DAG sizes below count distinct syntactic subtrees,
including primitive leaves; they must never be read as physical state counts.

Run, using Python 3 and the standard library only:

    python3 run.py --output /tmp/conpa_logic_replay

The complete replay takes roughly half a minute on the research machine. Input
files and retained evidence are not modified. The output directory receives
fresh receipts, regenerated candidate source maps, and per-check text logs.
The complete portable replay passed all six checks in 30.08 seconds; its
retained receipt is evidence/portable_replay.json, with logs in
evidence/replay_logs/.

1. COLLISION-ONLY COVERING: A FINITE-MODEL OBSTRUCTION
---------------------------------------------------

The implemented role-a cover permits equality of the matrix/output label a and
source label b as an exceptional case. Forcing this equality in EVERY emitted
cover would be a different theory. Under global irreflexivity its cover schema
reduces to

  exists b forall x [ (E(x,b) -> phi(x,p))
                      and (Emp(x) -> (phi(x,p) -> E(x,b))) ],

where Emp(x) means forall z not E(z,x), and b is fresh in the matrix. Call this
theory T_col, together with global irreflexivity. Arbitrary extra matrix
parameters do not affect the following argument.

Take two objects e,u, with the single membership edge E(e,u). Only e is empty.
For any predicate extension P on these two objects, choose output u if e is in
P, and choose e otherwise. In the first case the output's only member is e and
it contains every empty object satisfying P. In the second case the output is
empty and there is no empty object satisfying P. Thus every instance of the
entire collision-only schema holds, and irreflexivity holds.

collision_only.py checks all four predicate extensions. This is stronger than
testing a finite selection of first-order matrices: every matrix and parameter
assignment induces one of those four extensions. The unbounded conclusion
still uses this mathematical observation and ordinary finite-model soundness;
the script is not a first-order proof-assistant certificate.

PA can arithmetize truth in this fixed finite structure and prove its soundness
for finite T_col proofs. Consequently PA proves Con(T_col). If PA is consistent,
the desired PA-provable equivalence Con(T_col)<->Con(PA) is therefore impossible
by the second incompleteness theorem. This statement concerns the required
INTERNAL consistency calibration; it is not a claim that one of two externally
consistent theories must be inconsistent.

The full true-matrix weak cover at source u fails in the same structure: both e
and u are subsets of u, but no object contains both. The collapse therefore
does not merely provide another presentation of the original cover schema.

The examined later U208 submissions contain the already-known failed detector
shortening and hidden-helper rotation, but do not contain this collision-only
finite-model obstruction. No independent historical-priority claim is made.

2. INDUCTIVE SOURCE INVARIANTS
-----------------------------

The input sites.json is the exact 3,909-site Joint source used unchanged by the
principal contextual U208. The starting source ordinal is 136 and the nine
counter values are (1,0,13,0,0,1,0,0,1). The supplied blank initialization and
141-source-step bridge justify this starting point; the present finite abstract
analyses assume that exact established frame.

source_invariant.py first computes the independent zero/positive abstraction.
It checks every source edge against the final fixed point, independently of the
worklist traversal. Sites 3848 and 3849 are unreachable; the decrement at 3847 is
forced zero. The resulting symbolic source interface has 5,081 reachable cases.

source_relational_invariant.py retains the FULL relation of zero/nonzero bits
among all nine counters, represented as subsets of the 512 Boolean patterns.
Positive decrement has both zero and positive abstract outputs, and all actual
counter runs are included. The complete closure has 278,384 abstract
configurations, with at most 256 patterns at a source site. Conditioning on the
decrement outcome strengthens 1,649 case interfaces beyond the product domain.
The same two source sites remain unreachable.

source_intervals.py also computes exact small constants and lower/upper bounds.
Endpoint 16 denotes at least 16 for a lower bound and infinity for an upper bound.
The finite interval transfer is an overapproximation and its final inductivity
is checked on every edge. Combining these intervals with the conditional Boolean
facts gives 413 case interfaces with a useful exact positive constant or lower
bound greater than one, and removes two additional impossible branch cases.

The separate runtime researcher replayed these restrictions on the original
U208, with all spare values fixed to 1, obtaining 5,079 contracts and 1,243,924
symbolic inferences covering all 416 rows. That runtime artifact is elsewhere in
the enclosing packet. A list lemma specialized to a block of value 1 means three
steps per block; the arbitrary finite tail remains symbolic and is NOT replaced
by a sampled list. The spare-value-1 invariant follows from the initial 43 ones, CI
appending 1, and preservation by the other primitives.

These facts did not rescue the attempted aliases. Evidence here records 18
failed restricted U209 aliases and 16 applicable failed aliases on U208 after
the existing 172/211 fold. A symbolic-check failure is an unproved interface,
not by itself a concrete reachable counterexample or a general impossibility.

3. INDEPENDENT PARAMETER RENAMINGS OF THE SEVEN LOGICAL ROWS
---------------------------------------------------------

Each unrestricted logical row can be independently reparameterized by a
permutation of a,b,c. Because the permutation is a bijection of N^3, its SET of
numerical axiom instances remains exactly the same. This changes the tuplewise
AX bundle but preserves soundness and completeness of the enumerated axiom set.
The dominated rho8 row and the gated cover are held fixed in this experiment.

The seven intervals, in primitive ordinal coordinates, are
G[478,887), rho6[887,1170), rho5[1170,1466), rho4[1466,1765),
rho3[1765,2061), rho2[2061,2411), rho1[2411,2642).

exhaust_axiom_permutations.py exhausts all 6^7=279,936 combinations with the
existing source association fixed. Its exact minimum is 197 distinct source
subtrees, achieved by precisely four choices. They are the original source,
swapping b/c only in rho6, swapping b/c simultaneously in rho2 and rho4, and
combining those changes. The exact decomposition has 146 fixed nodes, 39
uncontested dynamic nodes, and 49 potentially colliding templates; the latter
each depend on one row only. The script checks the decomposition against 343
independently expanded source trees and checks every minimum explicitly.

The underlying arithmetic macro bindings are retained in inputs/k215_sites.json
and inputs/axiom_tokens.json. model.py and axiom_model.py reconstruct the actual
closed source subtrees. No identification of macro names with physical register
numbers is assumed: in the current native table the a,c,b pushes are respectively
the closed subtrees represented by states 98, 166, 12.

An exploratory protected allocator could not place the three changed minima in
208 states under the strict filter. Relaxing the extra filter produced one
208-state prefix-valid allocation for the rho6-only change. It is rejected:
the fresh universal runtime check fails at source site 23 (CD 3, zero branch)
after 31 successful cases. A prefix certificate is therefore insufficient.
The allocation receipts are retained as negative research evidence, not as a
new accepted 208 construction or a 207 candidate.

4. REORDERING THE LOGICAL ROWS
----------------------------

Permuting the seven whole expression builders is also sound at the source
contract level: each pushes the previous current formula, builds one theorem
from unchanged parameters, and restores scratch counters. The protected startup
suffix still produces nine theorem heads. Proof compilation must select the
appropriately permuted stack index; any physical compilation needs a new runtime
and startup bridge.

row_order_search.py evaluates every 7!=5,040 order with a specified bounded
association heuristic. It preserves five closed source slots and distributes
the ordered atomic factors with slot counts (1,6,6,1,16). Within each slot a
deterministic beam-1 substring dynamic program minimizes the union of nonfixed
source nodes, with zero-run/depth tie breaks. All emitted best maps pass two
independent CFG resolvers and whole-program boundary checks.

This heuristic's best output has 199 source nodes; the original association has
197. Thus the experiment yields no improvement. The order enumeration is
exhaustive, but the association choices are NOT exhaustive; the result is not
a lower bound on all reorderings, associations, compilers, or physical machines.

5. PROVENANCE AND PROOF STATUS
----------------------------

source_language.py is retained from the Joint U209 packet; source_splice.py is
the credited ProveIt source-splice utility pinned at commit
fe8b3a2d1db0033113e986590f79ecba3e5ef500. Their existing attribution comments are
preserved. The source utilities in turn credit the K225/K226 construction and
Wade's MIT-0 framework. INPUT_MANIFEST.json binds all local input bytes.

The local 208 fold proofs in the five subsequently supplied packages use the
same old-state guards and 1/3/7-step whole-tape simulation, with state renamings
and the two U209 parent classes. Their ordinary arithmetic proof is separate
from the inherited U/PA proof-search calibration. None supplies a newly compiled
end-to-end Lean, Rocq, MM0, or PA endpoint for this U machine, and the K215/ZFC
endpoint cannot substitute for that obligation.
