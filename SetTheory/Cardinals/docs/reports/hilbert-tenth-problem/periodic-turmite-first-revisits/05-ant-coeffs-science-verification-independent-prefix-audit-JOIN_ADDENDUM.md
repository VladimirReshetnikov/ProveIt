# Independent actual-join addendum

## Verdict

**PASS for both actual strict literal joins.** This supersedes the pending-join limitation in the earlier `AUDIT.md`; all other scope limits remain in force.

A separately authored binding adapter, `check_join_independent.py`, regenerated the inspected new constant prefix and both authenticated owned Report44 main streams. It actually traversed and hashed every joined gate and every domain, residual and final-equation record. Its complete hashes and counts match the construction author's independently written `join_strict.py` exactly.

Two raw inputs:

- 14,335,963 multiplications + 17,052,868 additions/subtractions
- **31,388,831 operations**
- 465 positive witnesses; raw coordinates RawLeft, RawRight
- Final equation: gate 31,388,830 equals paid-zero gate 0
- Complete joined SHA-256: `b235ba1d2baf0cf089c9658b1995f9c19fbe3ff033dc6ae67c76ec8cd6522d03`

One raw input:

- 14,335,967 multiplications + 17,052,874 additions/subtractions
- **31,388,841 operations**
- 467 positive witnesses; raw coordinate RawInput
- Final equation: gate 31,388,840 equals paid-zero gate 0
- Complete joined SHA-256: `737866317089c07465253a0d489813bf1bab50aaba0dda6083acbf78ef45f276`

Both joined sources have only literal 1 and 3 leaves, retain one final equation and preserve exact variable degree 2,304,000. No new witnesses or equations are introduced.

## Binding and pointwise equivalence

Let N=29,081,374 be the prefix gate count. Every old integer reference r is translated to N+r. Every old coefficient C:k is resolved to its checked prefix label. Every raw/positive coordinate name is preserved, with declarations required before use. The independent adapter rejects forward references, unknown coefficient labels, undeclared coordinates, unsupported opcodes and record types, duplicate/reserved witness names, and extra final equations.

The actual used coefficient set equals the full 1,152,598-label prefix dictionary in each arity. There is no unresolved C: operand or extra free coefficient declaration. The actual regenerated old canonical hashes match the authenticated values:

- Two-input old stream: `c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac`
- One-input old stream: `85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a`

The full positive-coordinate name lists agree with the authenticated lists, in their original order. The 285 and 286 residual records remain metadata; they are not added equations. Every old arithmetic gate is preserved without algebraic deletion or unpaid simplification.

The prefix audit proves each replacement label equals its old prescribed integer coefficient. Induction on the old arithmetic gates therefore proves pointwise equality of the final polynomial for every assignment of raw and witness coordinates. This is stronger than an unproved satisfiability-preserving substitution. Constant-only prefix gates have variable degree zero, so the inherited exact degree and domains are unchanged.

## Execution boundary and retention limit

The reused main module is the inspected, newly authored and already authenticated **owned Report44 arithmetic generator**, SHA-256 `eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395`. Its executed closure uses only its three reconstructed JSON specifications: the history, recoder and endpoint arithmetic data. The parent explicitly confirmed that reuse of this owned source was allowed. No upstream Python, physical ant program, color recipe, saved row decoder or upstream saved arithmetic schedule was executed.

The joined arithmetic format is a fully specified mixed line format: arithmetic rows are tab-separated `id,op,a,b`; domain/residual/final rows are compact JSON lines, retained in the old main order. The constant prefix precedes all main records. Both implementations hash identical bytes under that convention.

The complete joined streams were generated and hashed in streaming mode. They were not retained as enormous flat files. The exact new generators, data, receipts and hashes specify a replayable source. This addendum does not assert a fresh proof of inherited ant dynamics or history theorems, an expanded literal board, a giant-integer numerical evaluation, a novelty claim or an optimality claim.

## Evidence

- Independent adapter: `check_join_independent.py`
- Independent receipt: `joined-independent-receipt.json`
- Receipt SHA-256: `35de9dde7bec35ce6f2f8f023d9709084c81d85d4d6120adfeaa9c1999a69030`
- Candidate adapter SHA-256: `9c2c9ea9a65d3d651e32ed5a71388908b166d4ff0816f9c602558079c71905a6`
- Independent adapter SHA-256: `217d2c5e76f0ae32089b5d5dcb9278be09338b0a7bf35e1489e835109e9e6d0f`
- Addendum artifact hashes: `JOIN_MANIFEST.json`

The original prefix audit and its manifest were left unchanged. Read this addendum together with that audit.
