Pinned comparison corpus and structural novelty audit
====================================================

Repository:
  https://github.com/VladimirReshetnikov/ProveIt
Revision:
  2337ce611a26e308697ccbddb2a1636f989f01c3
Areas:
  Computability/BusyBeaver/Research/PA
  docs/incoming

The comparison covers all 61 filed deliveries listed by the PA packet index
and all five ZIP deliveries actually present in docs/incoming at this revision.
Their individual contributions, source URLs, evidence limitations, and incoming
Git-blob identities are in packet_ledger66.csv and packet_ledger66.json. A stale
README statement that incoming contains no archives is not used as an inventory.

Counts and their meaning
-----------------------

The repository's historical filing inventory reports 7,130 original .tm
occurrences, 786 byte identities and 535 retained table fingerprints. The fresh
scan of the current deduplicated tree plus distinct nested ZIP bodies recognizes
1,594 occurrences and 670 byte forms. These are different inventories, not a
contradiction and not counts of independent consistency constructions.

All 535 retained catalogue representatives were freshly parsed and their
fingerprints and catalogue counts recomputed: 535 match. The full fresh corpus
contains 576 maximal-reachable-component fingerprints. Of these, 563 admit a
spanning root and exactly one terminal halt label, so the fingerprint is a
whole-graph classification. Thirteen remaining fixtures do not have this
property and are not treated as whole-graph isomorphism classes.

There are 76 spanning one-halt graphs with exactly 194 working controls:
  34 packet-reported constructions;
   7 supplementary constructions;
  30 auxiliary/research inputs;
   5 explicitly rejected candidates.

The additional 194-label nonspanning fixture has a maximal reachable component
of only three controls and is excluded from the frontier count of 76. The
frontier categories classify the supplied evidence; they do not assert that
this audit newly proved 41 complete PA calibrations. Source/command/calculus
proofs cannot be inferred from a table's count, file name or graph fingerprint.

Both recognized 193-state tables are rejected as complete blank-input Con(PA)
machines for different reasons. The coefficient-three table fails logically
because the retained formula constructors collide; the other table implements
the intended runtime but fails its blank initialization. rejected193.json gives
exact identities and source locations. Neither proves 193 impossible.

Recognized formats and coverage boundary
---------------------------------------

audit_inventory.py scans complete numeric five-column binary tables in .tm,
.txt, .csv and .tsv files. Rows are whitespace-separated q read write L/R next.
Both read symbols must occur for each working state; native state labels may
be sparse. It also recognizes entire table strings and five-column row arrays
inside JSON. It recursively scans ZIPs and scans each distinct ZIP byte payload
once. A repeated archive reference is retained as provenance, not recounted as
a separate archive payload. Its recorded run examined 10,165 filesystem inputs
and 19 distinct ZIP bodies; no .tm parse failures or JSON parse errors occurred.

The supplementary attributed JSON recognizer handles five-column row arrays
(including signed +/-1 directions), paired dense action triples, flat dense
action triples, numeric-state dictionaries of paired actions, row-record
objects, transition-key dictionaries, and embedded whole textual tables. It
uses the lexical prefilter documented in scanners/json_inventory.py; it is not
an interpreter for arbitrary JSON schemas. Its recorded run examined 8,563 JSON
files/members, with 955 satisfying that filter, and recognized 85 occurrences
with 73 normalized byte identities. It excluded 35 one-state fragments and
reported no parse errors. All recognized tables were compared under the main
fingerprint convention and added zero classes to the 576 representatives.

Neither scanner executes generators or treats source grammars, prose, TeX,
PDF-rendered tables, compressed opaque encodings, or arbitrary JSON as machine
definitions. The packet-level ledger also reads the manuscripts' stated
contributions and limitations; that semantic comparison is distinct from the
explicit literal-table census. No claim is made about undisclosed designs or
the repository after the pinned revision.

Canonicalization and starts
---------------------------

For a chosen root, traverse outgoing read-0 then read-1 edges breadth first;
renumber newly reached working controls in order; record written bit,
direction and target for both rows of every reached control. Every undefined
terminal target is represented by -1. Hash the compact JSON serialization.
The table fingerprint is the minimum hash among roots reaching the largest
number of controls. This agrees with the repository's table-class convention.

A table admitting a spanning root has a complete transition-graph invariant
under arbitrary state renaming and arbitrary choice of spanning root. This
does not designate a historically intended blank-start state. In particular,
native HAZ tables contain state zero but explicitly start at74, whereas their
dense presentations explicitly start at zero. Original start metadata must be read
from the corresponding packet. No start is inferred for an imported table
merely because its labels happen to be contiguous.

check_novelty.py requires the candidate to have one halt and to be reachable
from its specified start (explicit comment, or the candidate's dense-zero
convention). It compares all spanning roots, arbitrary state names, global
tape reflection, and global binary-symbol complementation. By default it also
ignores the write and direction of transitions that enter the terminal label.
This is deliberately stronger than preserving those irrelevant terminal
effects. Symbol complementation is a structural novelty test; it is not said
to preserve an all-zero-blank computation. --strict-terminal restores those
terminal effects. Nonspanning fixtures are excluded from this novelty test.

The recorded candidate_novelty.json covers PA194QN5 and PA194QN6. Each has no
match among any of the 76 spanning 194-state corpus graphs, even under these
transformations. This establishes structural difference within the documented
corpus. Material semantic differences are recorded in material_deltas.json
and comparison_section.tex; graph novelty alone is not a consistency proof.

Offline use
-----------

Python 3.10 or later and its standard library are sufficient. From this folder:

  python3 -B check_novelty.py /path/to/PA194QN5/machine.tm \
      /path/to/PA194QN6/machine.tm --output /tmp/novelty.json

All 576 representative tables are bundled, including larger sizes; a network
connection or repository checkout is unnecessary for this comparison. Every eligible literal representative is reparsed and its bytes and root-free
fingerprint checked against the index; cached keys are not trusted without
that replay. The same script works on larger spanning candidates.

To reproduce the inventory against a separately supplied exact repository:

  python3 -B audit_inventory.py /path/to/ProveIt /tmp/fresh-census
  python3 -B scanners/json_inventory.py /path/to/ProveIt \
      --output /tmp/fresh-json-census

These commands write receipts and normalized inventory tables, not source
changes. The supplied graph_tools.py provides the common fingerprint used to
compare supplementary JSON tables with table_index.json. The JSON scanner's
own graph_hash uses its inherited serialization and is not directly the same
hash convention; never compare unlike fingerprint formats by value.

Contents
--------

packet_ledger66.*            All 66 deliveries with substantive reading notes.
frontier194.*                Annotated complete 76-graph current frontier.
table_index.json, tables/    All 576 representatives, hashes and exact locators.
candidate_novelty.json       Chosen QN5/QN6 comparison receipts.
material_deltas.json         Exact changes against the nearest prior families.
rejected193.json             Why the two smaller tables are not solutions.
comparison_section.tex      Includable mathematical/family discussion.
delivery_ledger.tex          Includable complete 66-delivery comparison table.
audit_inventory.py           Read-only primary fresh-census scanner.
scanners/                   Attributed broader JSON scanner and dependencies.
json_census.json             Complete supplementary JSON recognition receipt.
census_*.json                Fresh main inventory and source locators.
catalog_recheck.json         All 535 retained catalogue recomputations.
repository_*                Pinned repository's own indices for provenance.
incoming_listing.json       Pinned GitHub names, sizes and Git-blob identities.
licenses/                   Retained upstream license notices.

Attribution and proof boundary
------------------------------

The source programs, arithmetic engine, compiler, mathematical calibrations
and prior constructions are inherited from James Chang's BusyBeaver work,
Vladimir Reshetnikov's ProveIt research corpus, Wade's register framework, and
the attributed research packets. Their notices are retained. The primary
census is adapted from the incoming 2026-11-13 reduction study; the broader
JSON recognizer and its literal parser are retained from the filed Q-radix
packet. Newly written work here consists of the pinned combined corpus,
annotations, representative packaging, root-free comparison wrapper, and
the combined evidence accounting. No earlier research is claimed as new.

The PA-calibration arguments for the candidates are ordinary mathematical
arguments with explicit inherited dependencies and universal executable
certificates. This comparison is not a newly elaborated end-to-end Lean/Rocq
proof of their PA biconditional, and it is not an iPRA endpoint.
