# Integrity and scientific scope

Authentication, repeatable finite computation, and mathematical proof are separate claims. This release uses SHA256 as an external integrity pin, not a digital signature or distributor identity proof.

`MANIFEST.json` lists every payload file except itself and `SHA256SUMS`. Its hash is embedded in `verify_release.py`. For that file alone, the exact one-line manifest pin is normalized to64 zeros before hashing. The fixed-width replacement avoids a circular byte-hash equation; all other payload bytes are exact. `SHA256SUMS` then lists the actual verifier bytes and manifest along with all payloads. Obtain the external ZIP hash from the sender through a trusted channel.

The verifier rejects unexpected or missing files/directories, symlinks, nonregular files, wrong modes, malformed JSON, duplicate keys, nonfinite values, changed source identity and stale approval. Exact receipt comparison distinguishes integers, Booleans and floats, and rejects unknown keys or list changes. Enclosing safety checks contain no removable assertions.

The science in the literal and endpoint packets does use assertions. It is executed only in unoptimized child interpreters after full identity verification. Explicit guarded scripts are checked to reject optimization; documented unsupported standalone entries are not misrepresented as optimized passes. The independent interface regression also runs unoptimized. Only Report38 science supports optimized replay, as separately specified and preserved.

Original release metadata preservation means bytes, modes and nanosecond modification times of files and directories. Reading may update access times. Mutable external scientific copies intentionally rewrite receipts and regenerate data; their metadata is not claimed unchanged. No command executes the predecessor loader or rewrites frozen evidence.

All output locations and temporary parents are resolved and rejected if inside the release, including symlink aliases and hostile TMPDIR selections. PDF compilation uses no shell escape. ZIP checks validate exact names, counts, regular modes, sizes and payload bytes before extraction, and enforce the trusted enclosing inventory as the size bound.

The independent source audit, mathematical proofs and finite receipts retain their scopes. Full2^24 Boolean checks are exhaustive Boolean checks. Finite template histories are complete for their declared history languages. Infinite geometry and all-history visitation follow from the article's selector, ownership, chronology, long-wire and layer proofs. There is no formal proof-assistant claim, dense-bitmap claim, full physical row expansion, newly implemented arbitrary-program U15 compiler, or universal arithmetic total.
