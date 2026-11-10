# Independent external audit: sign16 conditional V elimination

The independent `check.py` ran with `python3 -I -S -B` and exited 0 (outer
session `16318`), producing `result.json` without calling the candidate's
builder or checker. Checker SHA-256:
`3d0c64011a08b94a1cf5ec51c921777401ae8447557eabec4c8936a353b48f59`;
result SHA-256:
`a8a329b7e6e1c402567ad32d0ef543952833ff1c94dd6e3cb05009110a2d4a2f`.

The checker reconstructs the signed V substitution, all seven retained ASTs,
metadata and unchanged port bindings. It verifies the removed old coordinate
17 occurs outside its defining row only twice, as a single square in Na.
All residuals have syntactic degree at most 56, and Na does not use input 0.
A separate nested coefficient-list calculation finds `[t^56] Na = 64*beta^34`
when all 16 witnesses equal t. The degree-112 coefficient of the fixed-port
square sum is a sum of integer squares, at least `4096*beta^68`; checked beta
bytes are positive. The checker verifies gzip/raw hashes, byte lengths and bit
lengths for all four ports and the inherited certificate/proof-file hashes.

The deleted replacement is signed. Reverse lifting to an old natural witness
is justified only if that replacement is nonnegative; deriving this from the
reduced equations is open. The audit does not prove that sign condition, an
unconditional sign16/sign17 equivalence, Lean/JSON binding, model bridge, or
iPRA endpoint. The external degree calculation and structural substitution
remain valid independently of the unresolved natural-lift condition.

The accompanying `PROOF_PLAN.md` is explicitly a plan. I checked that the
named `Sign33AbsDiffSquare.absdiff_sq`,
`Sign33Windows.windows_from_maintained_norms` and
`Sign33InnerVRing.inner_v_of_window_and_strong` declarations exist and have
the broad roles described. This audit does not verify the planned extraction
of their hypotheses from the reduced rows, monus/cast identifications, or the
claimed non-circular derivation; those remain proof obligations.

The auditor subsequently reran this checker and overwrote `result.json`; that
rerun exited 0 directly (no session ID) and produced the same SHA-256 recorded
by the original author tool output. The first version of this README had
transcribed the result digest incorrectly as
`a8a329b7e6e1c402567ad32d0ef543952833ff1c94dddbb55a9a2f141c5953397`;
that receipt typo is corrected above. The checker and result bytes are frozen.
