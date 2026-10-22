# Reading the evidence

`verification_summary.json` records the accepted **separate** overlay checks,
their targets, module counts, compiler identity, and printed axiom reports.
The `base` entry is the original 24-module provider build; it is not a fourth
proposal. Counts overlap between builds.

Each directory under `checks/` contains the original `verification.json` and a
portable `log-map.json`. The former is unmodified historical output and retains
the original absolute paths. The latter binds each accepted module's source
hash and transitive source fingerprint to its bundled original compiler log.
Source references identify either the pinned repository path or a file in this
packet. `logs/` deduplicates identical logs by full SHA-256 digest; an empty
log is normal for a successful Lean module with no diagnostic output.

The source and log hashes in every accepted row were rechecked against the
delivered source files or the pinned checkout during assembly. Compiled proof
objects and toolchain binaries are not distributed. Reproduce a check from
source using the commands in the top-level README; delivered ledgers alone
cannot serve as an object-cache provider.

`history/machine2/` and `history/machine3/` preserve development runs that
successfully compiled some providers but failed at their last target. Their
full raw ledgers and failed-target logs are retained for provenance. Those
failed target source hashes are not accepted results and are not the final
delivered source hashes. A printed `sorryAx` in a failed elaboration is not
an accepted proof; the corrected final source passed and its accepted axiom
reports use only the stated standard Lean axioms.

`measurements/` contains static import, source-size, primitive-count, and
receipt-comparison data. These are not timing benchmarks or theorem-term
dependency counts. `patch_applicability.json` records successful `git apply
--check` for all three supplied patches against the pinned checkout.

The Python packet verifier checks integrity and evidence/source correspondence.
It does not replace Lean or Rocq kernel checking. No combined production replay,
complete machine-specific `KEndpoint215` rebuild, or new Rocq check is claimed.

