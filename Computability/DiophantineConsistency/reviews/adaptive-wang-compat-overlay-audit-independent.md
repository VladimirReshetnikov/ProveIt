# Independent compatibility overlay overlap audit

Root replay `/tmp/adaptive-wang-compat-overlay-audit-wf16bhnh` **PASS**: all 367 canonical project `.olean` objects match the compatibility overlay byte-for-byte, with exactly the 27 expected compatibility WangTable and chunk objects added. The complete `result.json` hash matches the author audit exactly; both audits reauthenticated all recorded inherited source guards and selected provider objects and the chunk records.

The three-file `adaptive-wang-compat-overlay-audit-independent-evidence/FILES.json` manifest has SHA-256 `5c23f887b07a0c1ef3ccc8b31d5c59e7e3281ac2c6bd11ab26d128e3a83ad377`. This read-only overlap check does not modify or substitute any provider. It does not establish full elaborator interface equivalence or authenticate the historical original object against current source.
