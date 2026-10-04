# Relocatable independent audit replay

This adapter preserves the frozen audit scripts and proof byte-for-byte. It
changes only their runtime directory bindings and the mapping of18 authenticated
original provenance paths to files in the extracted frozen Report47 release.
It authenticates the complete95-file baseline and the frozen audit manifest
before executing inspected own arithmetic/audit code. No physical-ant or saved
schedule implementation runs.

After safely extracting the packaged Report47 archive, run:

    python -B replay_independent_audit.py \
      --audit-dir /path/to/Report48/independent_audit \
      --candidate-dir /path/to/Report48/science \
      --report47-dir /external/extraction/Research_Report47 \
      --out-dir /external/new-audit-replay

The output directory must not already exist and must lie outside all three input
source trees. Its parent must already exist. Do not use Python -O. The adapter
copies the unchanged two scripts and generic proof to the fresh output directory,
then runs both checks there. It does not create or require candidate_snapshot.
The cache checker runs via run_path only after the correct audit module has been
bound, so its import-time work and receipts stay in the fresh output directory.

A successful run ends with PASS_RELOCATED_FROZEN_INDEPENDENT_AUDITS and writes
replay-receipt.json. The five reproduced evidence JSON objects must equal their
frozen originals. All source trees must retain their before-run hashes.
An interrupted/failed run leaves its output directory for inspection; choose a
new directory for another attempt. The adapter does not delete or overwrite it.
