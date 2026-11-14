PINNED CORPUS COMPARISON AND OFFLINE REPLAY
========================================

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 4be5c6e3a10292a7466f5d3687e3b39615ff049b
Audit date: 14 November 2026

RESULT AND EXACT SCOPE
----------------------

The fresh literal census covers every one of the 548 direct .tm files below
Computability/BusyBeaver/Research/PA/ at the pinned commit, and complete
numeric binary tables in .tm/.txt/.tsv/.csv members of all eleven incoming
ZIPs under docs/incoming. It additionally covers all six historical ZIP paths
under PA, representing four distinct top-level payloads, recursively through
all their nested dependencies. ZIP payloads with identical bytes are expanded
once and every container reference is retained. All 548 direct files were
bound to the current Git tree using the Git blob SHA-1: 540 were recovered
from byte-identical archive copies and eight were fetched individually.

The narrative packet ledger has 72 entries: 61 placed packets and eleven
incoming deliveries. A packet is a delivery, not necessarily a new machine
or a proved consistency theorem. The historical MACHINES.tsv catalogue is
retained as additional attribution metadata, not substituted for the fresh
literal census.

Fresh counts:

  direct current PA .tm files                         548
  bytes in those direct files                  2,820,359
  current incoming ZIP payloads                        11
  historical top-level ZIP paths / unique payloads     6 / 4
  recursively expanded unique ZIP payloads              25
  archive references, including repeated payloads        37
  recognized literal table occurrences              3,334
  recognized literal byte identities                  762
  distinct spanning action-graph classes              638
  nonspanning recognized byte identities                6
  spanning 193-control graph classes                   53
  spanning 194-control graph classes                   82
  additional nonspanning 194-control byte forms          2

The 82 spanning 194-control classes remain pairwise distinct under the broad
equivalence below. The two nonspanning 194-control fixtures are also distinct
from one another under that equivalence. Hence the recognized literal scope
contains 84 complete 194-control graph classes: 82 spanning classes plus two
nonspanning diagnostic fixtures. Calling the 82 classes all 194-state graphs
without the spanning qualification would omit those fixtures.

The candidate PA194P5 is different from every one of these 84 classes. Its
exact delivered table has SHA-256
cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026.

The comparison allows arbitrary control renaming, arbitrary spanning-root
choice, global tape reflection, global interchange of read/write bits, and
erasure of the write/movement actions on edges entering the terminal halt.
Exact canonical tuples are compared; SHA-256 values are supplementary
identifiers. This is broader than equivalence preserving the designated
blank-zero start. The result is corpus-relative graph distinction, not
global priority and not a consistency-equivalence proof.

REPLAY
------

From the package root, using Python 3 and its standard library:

  python3 -B comparison/verify_novelty.py
  python3 -B comparison/verify_census.py

The first command re-parses the delivered candidate, validates all 82
frontier representative byte hashes, recomputes exact and broad canonical
classes, checks all six nonspanning identities, and writes
candidate_novelty.json. It also distinguishes the two nonspanning 194
fixtures using nonterminal action-count invariants under all four global
symmetries. Every control of PA194P5 is graph-reachable from its start 0;
no root of either fixture reaches more than three controls.

The second command re-parses all 762 bundled literal byte forms, recomputes
their exact spanning graph classes, checks the eight excluded fragment byte
forms, validates every retained occurrence reference, and binds all 548
direct-file paths to the pinned Git hashes. It writes census_replay.json.
This is a full offline replay of the retained literal data, not a new remote
crawl or a fresh re-expansion of the original ZIP payloads.

FILE GUIDE
----------

  candidate_novelty.json       Exact delivered-table comparison receipt.
  verify_novelty.py            Portable exact graph comparison.
  verify_census.py             Portable replay of retained census data.
  table_tools.py               Literal parser and rooted BFS encoding.
  census.json                 Every recognized identity, occurrence and class.
  census_summary.json          Compact fresh census counts.
  identities.csv              Machine-readable literal byte catalogue.
  census_tables/              All 762 recognized byte identities.
  pinned_direct_tm_manifest.json
                              All 548 pinned direct .tm paths and Git hashes.
  incoming_snapshot.json      Repository incoming-file metadata.
  historical_archive_manifest.json
                              Six historical ZIP paths, exact Git/SHA256 bindings.
  historical_archive_members.json
                              Complete recursive historical member inventory.
  historical_delta.json       Added occurrences/byte forms; no new graph class.
  frontier194.json/.csv        All 82 spanning194 classes and source locators.
  frontier194/                One exact literal representative per class.
  rejected193.json/.csv        All 53 distinct193 graphs and rejection status.
  rejected193/                Their 53 exact literal representatives.
  nonspanning_diagnostics.json
                              Named provenance and reachability of six fixtures.
  diagnostics/                Their six exact byte identities.
  nonspanning194_distinction.json
                              Explicit invariant separating the two 194 fixtures.
  unparsed_diagnostics.json    All 22 excluded literal-fragment occurrences.
  excluded_literal_fragments/ Their eight exact byte identities.
  packet_ledger.json/.csv/.tex All 61 placed and eleven incoming deliveries.
  incoming_readmes/           Principal README of each incoming delivery.
  evidence/                  Credited historical status receipts and all 49
                              transplant startup logs; provenance.json binds them.
  MACHINES.tsv               Repository's historical placed-machine catalogue.

WHAT THE 194-CONTROL FRONTIER CONTAINS
------------------------------------

The attributed evidence categories are:

  reported principal construction                     40
  supplementary construction                           7
  source-validated research rotation                    5
  research auxiliary                                  25
  rejected                                             5

These labels report the supplied packet evidence. They do not mean that
every historical logical calibration, source compiler, literal runtime
certificate, and proof-assistant development was freshly rebuilt here.
Rejected or auxiliary tables have deliberately not been promoted to
consistency constructions. The table names, mechanisms, exact hashes and
all occurrence paths are in frontier194.json.

The main families change different layers of the common numerical proof
enumerator: decoder association and history-dependent folds; physical A/D
layout; no-push or cached-result modus ponens; cached-only or symmetric
Shift; swapped quantifier-premise order; coefficient-five/six constructor
encodings; known-zero return instructions; independent diagonal-emitter
seeds; and the eleven-entry AX/MP fall-through introduced by AX11.

The newest six spanning classes beyond the retained76-class frontier are
AX11, QH5, H5, QHS, QN5 and QN6. Some incoming deliveries repeat a graph
already present in another incoming delivery. This is why file or packet
counts cannot be used as machine-class counts. Older names also contain
aliases: QN/NQ and repeated N6/C families, and ambiguous NS spellings.

PA194P5 changes the register routing by a nontrivial five-register physical
permutation while retaining the logical source. Its proof therefore needs
the new physical representation map and a separate blank initialization
check. The corpus comparison establishes that this delivered transition
graph is absent from the listed corpus; the main report supplies the
simulation and calibration argument.

ALL 53 DISTINCT 193-CONTROL GRAPHS
---------------------------------

None of the retained packets supplies a positive blank-start PA consistency
calibration for any of these 53 graphs. They divide as follows:

  1 coefficient-three calculus: logical refutation. The constructor collision
    E3(1,0)=I3(0,1)=6 allows derivation of contradiction code one. The retained
    packet supplies both a short 14-line certificate with derived K/S and an
    expanded 73,393-step primitive certificate; this audit attributes those
    certificates and does not claim a new proof-assistant compilation.

  1 original runtime193 marker quotient: the valid-frame source contracts
    pass, but the unchanged blank startups fail. A runtime certificate alone
    is not a blank-start consistency construction.

  1 append-zero runtime193 core: another failed initialization experiment.

  1 AX11/runtime193 composition: its 193 unedited starts yield two halts and
    191 outward blank rays, with no accepted whole frame and no cutoff.

  1 QN6/runtime193 composition: native start 74 reaches the outward q35 ray
    after 92 transitions.

  1 ZFC-style relay193: nine conditional source-contract failures and an
    outward blank ray after 116 transitions.

  47 additional marker-quotient transplants: the QN6 physical-search packet
    contains 49 exact transplant tables; two duplicate the original and
    append-zero cores above. All49 tables were screened from each of their
    193 existing controls. The historical logs record 9,457 runs, 100 halts,
    9,357 outward rays, zero whole frames and zero bounded runs. Every class
    has its exact originating table, source locator and log in rejected193.json.

The same QN6 packet also records all 9!=362,880 register-selector permutations
of runtime193 from native start 74. All entered certified outward blank rays;
none exhausted a bound. Other two-row and triple-rewrite searches do have
unresolved bounded runs. These restricted negative searches are not a lower
bound on the state complexity of a PA consistency machine, and they do not
exclude a different encoding, invariant, source program or initialization.

DIAGNOSTICS AND EXCLUSIONS
--------------------------

Six complete one-halt byte identities have no spanning root. Four are small
control fixtures with 5, 5, 6 and 9 controls. The other two have 194 controls but
maximal reachable components of size 3; they are padded encoding controls
from the combined/phase and shift experiments. Historical catalogues that
identified only their maximal rooted component placed these under one key.
That key is not a full-graph isomorphism certificate: the two literal graphs
are distinct, as the retained action-count invariant demonstrates.

The strict parser excludes eight other complete-row fragments, occurring 22
times, because they have either no undefined halt target or multiple external
targets. Their control counts are 2, 2, 4, 4, 23, 133, 137 and 139. Their rows are not
malformed. They are closed control fixtures or open compiler/arithmetic
fragments; none is a 194-control graph. Exact bytes, state counts, all external
targets, and source paths are retained for independent inspection.

This fresh census does not claim to enumerate arbitrary JSON transition
encodings, source programs capable of generating further machines, or every
direct .txt/.tsv/.csv file under PA. The current 194 literal frontier includes
the 76 earlier annotated classes and all six newly added principal graphs.
The broader narrative comparison uses the 72-packet ledger and reported
source mechanisms in addition to the literal census.

All six historical ZIP paths under PA have now been fetched, bound to their
pinned Git blob hashes, and recursively expanded. Four distinct top-level
payloads total 34,720,480 bytes; the three references to the same U209 joint
archive are deduplicated. Their nested dependencies add 14 unique ZIP bodies
to the 11 incoming bodies, for 25 total unique payloads and 37 archive references.
The historical expansion contributes 127 literal table occurrences and 21 byte
identities, but zero new spanning graph classes. Its newly encountered byte
forms have 209--222 controls. In particular, it adds no 193/194-control class
and leaves the delivered-table novelty result unchanged. See the historical
manifest, member inventory and delta receipts for the exact source bindings.
