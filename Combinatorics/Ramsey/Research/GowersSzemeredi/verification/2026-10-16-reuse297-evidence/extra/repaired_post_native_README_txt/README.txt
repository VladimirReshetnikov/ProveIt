Prepared, unexecuted NEXT297 post-native helpers.

Run only after all three native modes actually pass, while HEAD/source/inventory still match the pinned repaired6a75 snapshot. Both helpers retain current source/artifact stability checks. Use the actual receipt paths and SHA256 values; none are forecast here.

Archive arguments (same interface as predecessor):
  python3 /tmp/gowers-next297-post-native-tools-repaired6a75/archive.py --snapshot SNAPSHOT_PATH SNAPSHOT_SHA256 --source-ledger LEDGER_PATH LEDGER_SHA256 --core ACTUAL_CORE_RECEIPT ACTUAL_CORE_SHA256 --shared ACTUAL_SHARED_RECEIPT ACTUAL_SHARED_SHA256 --supplemental ACTUAL_SUPPLEMENTAL_RECEIPT ACTUAL_SUPPLEMENTAL_SHA256 [--extra-evidence MANIFEST_PATH MANIFEST_SHA256] --output NEW_ABSOLUTE_TMP_DIRECTORY

Retention arguments (same interface as predecessor):
  python3 /tmp/gowers-next297-post-native-tools-repaired6a75/verify_retention.py --snapshot /tmp/gowers-next297-repaired6a75-source-snapshot.json --final-receipt ACTUAL_SUPPLEMENTAL_RECEIPT --final-receipt-sha256 ACTUAL_SUPPLEMENTAL_SHA256 --output NEW_ABSOLUTE_TMP_FILE

The archive records three actual invocations and77 root closure metadata entries (1+58+18). The native union is1955; the seven historical roots cover125 modules, with116 overlapping and9 outside. Only after actual artifact checks may the retention verifier report1964 combined modules. The two added native modules are exactly FullPartitionScale and ThresholdFreeCorollary58. Historical evidence remains unchanged and explicitly attributed to its old25-root/437-module invocation.

preparation.json pins the integrated snapshot and mandatory source ledger. changes.patch records all executable differences. common.py and run.py are byte-identical copies of the reviewed native helpers. No helper was imported or executed during preparation.

This successor changes exactly three executable string literals: archive source commit, retention source commit, and retention snapshot SHA256. The native tool directory and all validation logic are unchanged. The repaired-source ledger pin is recorded in preparation.json and remains a mandatory archive argument. No helper was imported or executed during preparation.
