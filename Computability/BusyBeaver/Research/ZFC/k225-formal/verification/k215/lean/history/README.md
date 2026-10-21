# Preserved Lean execution history

The initial source closure had 171 project modules. Its first 150 modules
compiled successfully into a fresh isolated cache. The original monolithic
`KSource215` then reached its 900-second wall limit with no compiler error text
and no output object. Its exact source is retained in
`KSource215-monolithic.lean.gz`.

The first supervisor killed Lake on timeout but left its Lean child alive.
The pending Rocq lock waiter had already been cancelled. The child was explicitly
killed and checked before any other proof compiler was allowed to proceed;
`timeout-cleanup.json` records that correction. No overlapping proof compilation
is asserted. The successor used a dedicated process group and killed and waited
for that group before unlocking on timeout.

The 34-module partition replaces one original module and therefore gives 204
project modules. It moves the 32 independent finite-certificate proofs into
separate imports, preserving every declaration statement and proof body. The
public facade and theorem remain the same. The generator checks in `repairs/`
compare regenerated files byte for byte on disposable copies.

The executed `build_serial_v2.py` is retained unchanged. Its non-timeout
interruption path did not clean up the child group; the healthy active build was
not interrupted. The separately published portable `../build.py` and final
audit successor handle both timeout and interruption, with noncompiler controls
in `../controls/`. Historical scripts are evidence, not the recommended replay
commands.

`toolchain-boundary.json` is the historical 171-module statement;
`toolchain-boundary-v2.json` binds the current 204-module inventory. The original
absolute paths in receipts identify the actual execution locations. Publication
maps provide the corresponding retained repository files.
