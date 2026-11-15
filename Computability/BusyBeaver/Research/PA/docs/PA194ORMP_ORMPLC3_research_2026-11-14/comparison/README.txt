CURRENT CORPUS COMPARISON AND NOVELTY REPLAY

Snapshot: VladimirReshetnikov/ProveIt
7c0bb454cf73c29ca1c385f9fec856ddd236a7cb

Read ARCHITECTURE_AUDIT.txt for the synthesis and proof-status distinctions.

packets106.csv/json: all100 filed packets and six current incoming ZIPs.
named_designs104.csv/json: attributed mechanisms/proof status, rebound to
freshly parsed tables. This is not a count of104 independently checked
consistency theorems.
incoming13.csv/json: the13 current incoming proposed dense tables.
incoming13_startup_replay.json: fresh full-tape startup checks of those13.
incoming_tables/: their exact dense tables, included for independent replay.
classes194.csv/json: all548 spanning194 graph classes with source locators.
research193_classes61.csv: the61 recognized193-control research classes.
inherited_families35.csv: attributed historical family comparison.
census_summary.json: combined recognized-format coverage and counts:
7,342 occurrences and 1,381 normalized labeled tables; 548 spanning
194-control classes and 61 spanning 193-control research classes.
base_census_summary.json: unchanged original scanner summary.
json_coverage/: the supplementary numeric/Boolean JSON coverage audit,
its two additional source locators and their compressed original document.
verify_json_supplement.py: exact tuple checks that both supplemental
tables belong to previously indexed graph classes.
scope_manifest.json.gz/source_blob_binding.json.gz: pinned direct input
Git identities and checked content digests.
frontier194_index.json.gz: full exact transition tuples for all548 prior
spanning194 graphs and the two nonspanning194 diagnostic tables.
check_novelty.py: standalone standard-library exact novelty comparison.
novelty_replay.json: both new candidates and their pairwise comparison.
congruence194.csv/summary.json: ordinary action/target partition refinement.

Typical replay, adjusting candidate paths to the delivered package layout:

python3 -B check_novelty.py ../PA194ORMP.tm \
  ../PA194ORMPLC3.tm --output /tmp/novelty_replay.json

python3 -B verify_incoming_startups.py --output /tmp/incoming_startups.json

python3 -B verify_congruences.py --output /tmp/congruences.json

python3 -B verify_json_supplement.py --output /tmp/json_supplement.json

Optional full census rebuild, requiring the complete pinned input checkout:

python3 -B rebuild_census.py --source /path/to/ProveIt \
  --output /tmp/pa194_current_census

schema_parser.py is retained unchanged from the identified incoming packet.
PROVENANCE.json and licenses/ preserve its source identity and attribution.

The census recognizes complete explicit text tables and documented JSON
matrix shapes, including nested ZIPs. The base parser is retained unchanged;
a supplemental audit extends 193/194-control JSON coverage to numeric and
Boolean directions (False=L and True=R). It does not execute generators or
extract arbitrary tables from prose. Identical ZIP payloads are inspected
once globally; occurrence counts reflect that policy. Every selected direct
source blob was verified against its pinned Git object identity.

Graph novelty, a finite startup, a universal source contract, a written
weak-arithmetic theorem and a completed Lean theorem are different claims.
Read the per-design fields and main report for the relevant boundaries.

Attribution: source mechanisms, reports, compiler infrastructure and
calibrations remain credited to their original authors. The source census
recognizer is inherited from the current pa194_research_2026-11-15 package;
the named/family descriptions are attributed to the identified upstream
comparison ledgers. The new merger, compact exact comparison data,
standalone novelty and startup replay, and current synthesis are this
audit's additions. No upstream repository file was modified.
