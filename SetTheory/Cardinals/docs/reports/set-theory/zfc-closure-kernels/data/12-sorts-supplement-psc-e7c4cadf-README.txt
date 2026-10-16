PSC compiler supplement, audited commit e7c4cadf9b180e4b1801755b09777a7572412360

The .py sources, .md document, and upstream-psc-backend-results.json are
byte-for-byte pinned GitHub files. comparison.json records their Git blob
and SHA-256 identities, independent reproduction scope, and comparison.
reproduced-results.json is the local rerun of all seven fixed recipes and
all core checks. The optional 144/200 search families were not rerun.

offset_bottom4_repair93.tm is a NAMED PARTIAL 252-state table, distinct from
the frozen raw C/G 252-state table. It has 503 rows and the single undefined
1.inc/read1 row. No new normalized table or simulation certificate is claimed.

From the complete report archive's root, reproduce against its preserved
baseline helper/backend subset with an external scratch path:

PYTHONPATH=vendor/proveit/Computability/BusyBeaver/Research/ZFC python3 supplement/psc-e7c4cadf/psc_backend_experiment.py --scratch /tmp/zfc-psc-reproduce --output-evidence /tmp/zfc-psc-results.json

The program's own directory supplies psc_adapter_checks.py. The PYTHONPATH
supplies the existing pinned recovery/emission helpers, whose unchanged
upstream backend is already included in the report archive.

The mathematical audit is in the adjacent new_psc_commit_review.md or the
main report's countermodel supplement. These experiments expose an
inadequate proof calculus and do not constitute a new consistency record.
