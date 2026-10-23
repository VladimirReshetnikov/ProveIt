# Release dependency audit

Snapshot reviewed on 23 October 2026 while the final family reports were
still being assembled. This is an AI-assisted local packaging audit, not
an independent human endorsement or a mathematical compiler certificate.
No other worker's active files were modified.

## Findings requiring release-owner attention

1. **Nine-variable coefficient adapter: resolved.**
   The initially missing `upstream/COEFFICIENT_PROOF.md` is now included.
   A subsequent path/hash check confirms the active binding resolves and
   matches its recorded SHA256. Merely keeping SIGNED10_PROOF.md would
   not have been equivalent: its Section 2 cites rather than proves the adapter.

2. **Jones adapter metadata: resolved.**
   The active path now correctly names `upstream/COEFFICIENT_PROOF.md`.
   A subsequent check confirms both existence and recorded SHA256.
   SIGNED10_PROOF.md remains the separately labeled reference.

3. **Short-family optional reference path: resolved.**
   Removed the unused optional SIGNED10_PROOF.md pointer and role.
   The actual adapter under upstream_verified/ exists and its hash is now
   explicitly authenticated by audit_relaxed.py, as is the historical
   original binding. The historical binding's inert relative path is
   explicitly documented.

4. **Runtime dependencies: resolved and checked.**
   `batching/check_eleven.py` and `elimination/audit_package.py` import
   NumPy. The remaining reviewed canonical replay scripts use the Python
   standard library. The root requirements.txt now declares NumPy/SymPy.
   Do not claim the entire release is stdlib-only.

5. **Degree-certificate assertions: resolved; helper hardening remains.**
   The nine-variable final leader and unresolved-cancellation checks are
   now explicit exceptions. The Jones and short builders have likewise
   replaced their asserts. At the last scan, assertions remained in
   nine/circuit.py and packing/mask_popcount/build.py and circuit.py.
   These are helper/invariant checks rather than the removed degree
   certificate gates. Replace them if claiming blanket rejection parity
   under -O. Valid-input -O success alone cannot establish that property.

6. **Nine-variable selective source checker: updated.**
   The originally stale local checker copy has been replaced by the
   current hardened version, including explicit source hashes and transport
   convention. Its companion SOURCE_PINS/source_support files are present.
   A subsequent fresh-copy normal/-O replay of nine, Jones and short passes
   with byte-identical stdout in each pair. The copied nine checker is
   byte-identical to the authoritative weights checker.

## Successful fresh-copy replay

Copied only the planned canonical component directories into a fresh
temporary directory, omitting render caches, Python caches, logs and the
compiled search binary. No sibling research tree was copied. These commands
all succeeded from an unrelated working directory, normally and with -O:

- weights/verify_selective.py and weights/test_selective.py
- packing/mask_popcount/reproduce.py
- nine/verify_nine.py
- jones/check_jones.py
- batching/check_eleven.py
- elimination/audit_package.py and elimination/audit_eleven.py
- short/audit_relaxed.py

The final root verify.py was inspected but not run at this stage because
the final sealed manifests and remaining reports were still being written.
Run it on the actual extracted final ZIP after sealing, not only on the
development directory. Its selected stages are portable relative paths.

## Paths, historical provenance, and packaging

- No active top-level builder/checker in the selected families contains
  an absolute workspace/home/temp dependency or an active wave6 dependency.
- jones/check_jones.py intentionally reads the sibling
  weights/code_v1.json; elimination's audits intentionally read batching/.
  These are satisfied by the proposed root archive layout. They are not
  standalone-family guarantees.
- All existing SOURCE_PINS and RATIO_SOURCE_PINS entries scanned matched
  their local SHA256/Git-blob digests. This checks the registered local
  byte bindings; it is not a new remote audit of every historical citation.
- The copied coefficients/original_binding.json files contain an original
  relative complete_interface_proof path that no longer resolves after
  relocation. Preserve those files byte-for-byte as historical sources,
  explicitly label them inert, and use the corrected active bindings.
- Historical upstream Python files can contain old repository paths.
  They are legitimate provenance if explicitly inert and never included
  in the replay stages; they should not be advertised as runnable here.
- weights/optimize_joint.py needs the search executable; targets.py needs
  an intermediate vector. They are optional search history, not proof
  dependencies. If the binary/logs are omitted, also omit these scripts
  or keep their optional/non-replay status conspicuous.
- The short family correctly identifies the historical Q56 relaxed kernel
  as prior art and does not advertise its degree56/74-op pair as new.
- Root report inputs/results tables and nine/Jones reports were unfinished
  at this snapshot. Check every final TeX input and document link after
  those workers finish; their absence now is not a reported final defect.

## Recommended final gate

After the fixes, freeze the tree, authenticate every active binding path,
seal a relative-path SHA256 manifest, create the ZIP, extract it into a
fresh directory, and run root verify.py with the declared dependencies.
Also run the hardened family checks under -O, compare rebuilt artifacts
byte-for-byte, compile the complete report twice, and inspect final pages.
Do not rewrite historical source bytes to repair their inert paths.
