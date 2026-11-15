LATEST-HEAD COMPARISON SUPPLEMENT

Snapshot: 99f17206a77a04d36a9bb7dd04ce2e5d0360cf7d
Prior main comparison: 793c68737d94bffa4e32a75bce6cc8058d6d22f0

This bounded supplemental check extends the pinned comparison to the final
observed main revision. The earlier 97-delivery ledger, 83 named designs,
31-family taxonomy and 520-class frontier remain unchanged in the parent
directory. This supplement records the additions separately.

RESULT

The latest incoming listing contains seven ZIP deliveries. The original
four ZIP blobs are unchanged; three new ZIP blobs add eight named, spanning
194-state table classes:

  AX11GDH archive: PA194AX11GDH, PA194AX11GDHS, PA194AX11GDHF, PA194AX11GDHR
  Witness archive: PA194H5X, PA194JH5X
  Marker-separation archive: PA194LCGMS, PA194LCGSMS

Combined scope: 100 deliveries (93 filed + 7 incoming), 91 named designs,
and 528 recognized spanning 194-state table classes. These are corpus and
structural counts, not 528 proved consistency theorems. The three added
mechanism groups are described in extra_named_designs8.json and in the
retained source READMEs. The original 31-family taxonomy is not renumbered.

Both delivered constructions, PA194-LCSF3 and PA194-MP, are structurally
different from every one of the eight new classes. Fresh independent
explicit-bijection checks tried every root of each extra table, reflection,
global symbol exchange, and erased halt-entry action decorations: 6,208
attempts per delivered construction, with no matches. Together with the
prior 520-class replay, this covers the combined 528-class frontier. Symbol
exchange is an additional structural screen, not a zero-blank semantic
equivalence. All eight extra tables have greatest immediate-action
congruence of size 194, as do the previously checked 520 tables.

The full extra-archive scan adds one 193-state diagnostic class, the
witness archive's Runtime193, bringing the recognized 193-state research
class count from 54 to 55. It is explicitly rejected by its source archive;
the supplied blank-start audit reports two halting starts and 191 outward
rays. The representative is retained in extra193.json and representatives/.
This is not a positive sub-194 consistency construction. Imported proof
claims are attributed to their source reports; this inventory verifier does
not prove their semantic calibration.

SCAN SCOPE AND EXACT COUNTS

The fresh scan recognized complete numeric text tables and supported
explicit JSON table encodings in the three added ZIPs and their nested ZIPs.
It inspected 2,880 non-ZIP payloads and five distinct ZIP payloads, finding
2,151 table occurrences, 903 normalized labelled tables and 750 table
classes. There are 529 physical 194-state classes in those three archives,
of which 528 are spanning; the remaining nonspanning class was already
known. All eight new spanning classes occur as literal tables; JSON adds
no further new spanning 194-state class. The scan reported no parse errors.

This scan reused an old table-class computation only when the complete
normalized labelled table bytes had the same SHA-256 as an entry in the
independently reclassified pinned corpus. New normalized tables were
classified afresh. The independent verifier reclassifies all nine extra
representatives without relying on those cached classification values.

There are 15 new class keys relative to the complete prior union: eight
194-state classes, one 193-state diagnostic, five 203/204-state raw tables,
and one one-state diagnostic. The prior union of 1,137 keys therefore
becomes 1,152. The raw three-archive scan's union with the filed catalogue
alone is 1,146; that partial-scope value must not be presented as the
combined old-plus-new count. See scan_summary.json and all_new_classes15.json.

These recognition rules do not enumerate machines implicit only in arbitrary
executable generators or prove completeness for every possible table
representation. Each retained occurrence has an archive/member locator and
normalized-byte identity. The original ZIPs are not duplicated here;
archive_identities.json gives exact pinned retrieval URLs, Git blob SHA-1,
byte counts and SHA-256 values for all three.

PA TREE DELTA

The entire PA/docs Git tree, including the 93 filed deliveries, is unchanged.
Only PA/pa194 and PA/pa194-work differ. Recursive tree comparison identifies
98 changed or added blobs: 60 .lean, 18 .md, 19 .sh and one .py. No .tm,
.json, .txt, .csv, .tsv or .zip input changed. Thus the explicit machine
inputs covered by the earlier outside-docs census are unchanged. This
supplement does not claim to have re-audited the new Lean proof work or to
have obtained a new end-to-end kernel theorem. The exact listings and
old/new blob identities are retained in the PA_*.json files.

FILES

  extra_named_designs8.csv/json   Eight name/class/source/mechanism mappings
  extra193.json                  Rejected 193-state diagnostic identity
  representatives/              Eight extra194 and one extra193 literal tables
  verification.json/log          Fresh offline reclassification and novelty replay
  verify.py                      Portable independent replay, standard library
  scan_summary.json              Full text-plus-JSON counts and scope corrections
  scan_*.json                    Per-payload and per-occurrence scan ledgers
  all_new_classes15.json          Every new key, including raw/diagnostic classes
  archive_identities.json         Exact three input identities and pinned URLs
  incoming_listing.json          Captured seven-archive main listing
  PA_*.json                      Pinned/latest Git tree and blob delta receipts
  source_reports/                Original README/results/provenance/license excerpts
  literal_screen.json            Earlier literal-only explicit-bijection receipt
  scan_extra_archives.py          Optional archive census rebuild

REPLAY

Python 3.10 or later is sufficient; do not use Python -O. From the complete
delivered archive root (with comparison/, construction/, mp_construction/):

  python3 -B comparison/latest_head/verify.py --output /tmp/latest-check.json

To choose the two delivered table paths explicitly:

  python3 -B comparison/latest_head/verify.py \
    --lcsf3 /path/to/LCSF3/machine.tm --mp /path/to/MP/machine.tm \
    --output /tmp/latest-check.json

To rebuild the full three-archive explicit-table scan, download the three
exact ZIPs identified in archive_identities.json to one directory, then run:

  python3 -B comparison/latest_head/scan_extra_archives.py \
    --archive-dir /path/to/three-zips --output /tmp/latest-census

The scanner verifies their Git blob identities before reading contents.
Its summary describes only those three archives; combine its class keys
with the prior comparison/census and catalogue keys to recover 1,152.

Attribution and source notices are retained in source_reports/*/licenses/
and in the main comparison/licenses/ directory. The eight extra designs
are existing repository contributions, not new constructions of this report.
