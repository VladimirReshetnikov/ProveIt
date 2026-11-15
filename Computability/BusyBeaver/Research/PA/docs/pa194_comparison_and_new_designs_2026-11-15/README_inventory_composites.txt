CURRENT CORPUS COMPARISON AND TWO 194-STATE COMPOSITES
===================================================
Repository: VladimirReshetnikov/ProveIt
Commit: 8d31445d858761a8f6150c2e5012adae8895e932

This subbundle contains the complete recognized current 194-state frontier,
a comparison of all research packets, two literal constructions, the new
direct relative preservation proof, and their attributed proof dependencies.
The enclosing report governs the final research claim and reduction search.

NEW CONSTRUCTIONS
-----------------
Both machines are binary, deterministic, single-tape machines with 194 working
controls, 388 transition rows, dense start 0, and separate halt label 194. The
tape is infinite in both directions and initially all zero. Every transition
writes one bit and moves one cell left or right.

PA194AX11H_SF
  composites/machines/PA194AX11H_SF/machine.tm
  SHA256 23fc656adc1afbe9e63f3a56df6e0c73a4f15a6d1493f2048aebaf00c9483ad2

PA194LC_AX11H_SF
  composites/machines/PA194LC_AX11H_SF/machine.tm
  SHA256 e9c6864d7fb452dff86a38e561f39a2dac0ddb873369fdfa3c1e7a88edcac7bf

The first parent is the exact revised AX11H table. The second is its incoming
loop-continuation implementation LC_AX11H. Each new machine applies one
history selector to native controls 127 and 124, then two exact three-step
accelerations. The complete six-row edit appears in composite_proof.tex and
in each construction.json. All six changed rows are active during startup.

The independent verifier checks the entire finite premises of a direct
configuration proof. The acceleration guards are checked on the actual
selector intermediate. The primary SEL packet's other pair, 12 and 38,
does not satisfy AX11H's common-row premise and is not used.

For either exact parent M and new child N, the written proof establishes:
  iPRA proves H_M(t) implies H_N(3*t),
  iPRA proves H_N(t) implies H_M(3*t),
where H_M(t) means halted by time t in the absorbing arithmetic clock.
Primitive-recursive witnesses and quantifier-free induction prove halting
and nonhalting equivalence. The new initialization reaches the complete
parent seed tape in 57,918 steps rather than 57,922.

This is a direct relative mathematical proof. An absolute Con(PA) statement
uses the separately identified exact-parent calibration. These Python checks
do not constitute a completed end-to-end Lean or Rocq proof.

OFFLINE REPLAY
--------------
Use Python 3.10 or later, its standard library, and assertions enabled.
No network or original repository is needed for these commands:

  python3 verify_inventory_composites.py
  python3 verify_inventory_composites.py --lc

The default reconstructs both tables in a private temporary directory,
compares all ten core files byte for byte, checks the new literal finite
premises, compares full graph tuples against all 139 spanning historical
classes and the disconnected diagnostic, checks the frozen census metadata
and exact catalog Git blob identities, and verifies the inherited calibration
ZIP's exact identity. The --lc option additionally rebuilds and fully replays
both inherited LC/parent symbolic physical implementations and their clocks.

Fresh output goes to verification/inventory_composites. Use --output PATH
to select a different directory. The combined replay preserves frozen tables
and receipts. Successful finite checking is not itself a verification of
the imported arithmetic calibration.

The independent finite-premise checker explicitly verifies pinned parent
hashes, pinned child dense hashes, all 388 rows, the unique halt label,
dense/native conjugacy and reachability of all 194 working controls. It
checks four selector cases and twelve shortcut cases over arbitrary untouched
tape exteriors. Complete startup tape equality is checked block by block.

COMPARISON SCOPE
----------------
The 93-delivery ledger covers 87 filed packets plus six current incoming ZIPs.
The 27-family comparison explains recurring source semantics, physical
changes and distinct proof obligations. Current incoming archives contribute
29 new spanning 194-state classes beyond the filed 110-class frontier.

The literal frontier contains 139 spanning 194-state classes and one additional
disconnected 194-control diagnostic. Its attributed roles are 67 principal
constructions, 7 supplementary constructions, 47 research auxiliaries,
4 research seeds, 14 rejected classes and 1 diagnostic. These are report
classifications, not counts of independently verified consistency theorems.

All 140 literal representatives appear under comparison/frontier194. Their
annotations retain exact source-member origins, relative paths and hashes.
The graph comparison allows every spanning initial root, arbitrary control
names, reflection, global bit exchange and ignored final write/move actions.
Global bit exchange is an additional structural screen; it is not assumed
to preserve zero-blank semantics. Exact tuples are compared.

comparison/audit.py checks the frozen occurrence ledgers and reclassifies all
140 provided tables. The all-size count 747 is the union of the pinned
705-class filed catalog and 42 additional incoming classes. The frozen
incoming census has 1,439 direct .tm occurrences, or 2,945 including nested
archive references, with 500 distinct byte payloads and 389 table classes.
The original 87 filed archives are not duplicated here. Offline mode does
not claim to reparse every historical table absent from this bundle.

To repeat the recursive incoming .tm census, use:

  python3 comparison/audit.py --refresh --output verification/refreshed_census.json

This optionally downloads the six exact pinned public ZIP URLs into temporary
storage, checks both Git blob SHA-1 and SHA-256, reparses every recursive .tm
member, and compares every occurrence with the frozen ledger. Add
--archive-dir PATH to reuse existing archives. The original filed catalog
remains an explicitly attributed pinned catalog in this mode. Default audit
mode uses no network.

FILES
-----
comparison/packet_ledger93.csv,json   All 93 delivery records.
comparison/family_comparison.csv     The 27 mechanism families.
comparison/frontier194_annotated.*   All 140 attributed table records.
comparison/frontier194_index.json   Full source locations and relative paths.
comparison/frontier194/             Every literal 194-control representative.
comparison/current_*               Exact frozen census and source identities.
comparison/catalog/                Unchanged pinned filed machine catalogs.
composites/                        New constructors, checks, tables and proof.
references/ax11h_calibration.zip    Exact unchanged revised written calibration.
references/ax11h_written_ipra/      Extracted proof sources and provenance.
references/lc_ax11h/                Complete standalone LC proof and replay.
verification/inventory_composites/  Fresh relocated replay receipts and logs.

INHERITED PROOF DEPENDENCIES
---------------------------
The revised AX11H calibration ZIP is preserved byte for byte:
  93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075

It contains the original report, proof sources, code and reference material,
licenses and evidence. Its ten written proof fragments are also exposed in
references/ax11h_written_ipra/proof for convenient reading. Its claim is a
written mathematical theorem; the completed Lean endpoint remains absent.

The companion's LC dependency is a standalone attributed package. Its
proof.tex and proof_fragment.tex give the relative iPRA theorem with the
polynomial witness bound 13*t^2 + 707*t + 58616. Its 37 integrity-pinned
source/input files, both parent and LC tables, and independent literal
verifier are included. Run its verify_all.py with --output PATH for its
own complete replay.

The new contribution is the specific selector/acceleration composition on
these exact parents, its checked interaction, symmetric 3*t relative bounds,
new literal graphs and current-corpus reconciliation. The selector,
acceleration, loop transformation and numerical-calculus calibration remain
attributed to earlier supplied reports and their cited authors. Original
James Chang, Wade and ProveIt notices are retained. This subbundle establishes
neither a state count below 194 nor a general lower bound.
