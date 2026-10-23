# Independent review of the final mixed-radix compiler

The final frozen recipe uses 943 tiles, rho=2^125, 15625 radix positions,
two reflected clause bands at 7631 and 8733, and spatial displacement 42.
The reviewer reconstructed all four actual integers independently in
`check_mixed_independent.py`, without importing the coefficient builder.
Every byte matched the supplied manifest. Its receipt is
`MIXED_INDEPENDENT_CHECKS.json`.

The mixed-radix soundness argument is ordered correctly. The low ten-bit
selector count is at most943 and cannot receive a carry from higher bits.
The low mask forces count0/1. Only after that fact is known are the forty-four
payload sums at most2 and therefore carry-free in radix4. The separate
global rho carry bound applies even before selector extraction.

All22 overlap/anchor targets and both clause targets were checked against
every989 native basis positions for each relevant contribution, yielding
69230 identities. The two clause-band rotation-hit sets are disjoint, and
the two anchor alignment sets intersect only at zero. These finite identities
prove the linear coefficient statements for every native assignment, rather
than merely sample a few intended tableaux. The inherited binary-alignment
argument still includes the one upper-dummy spill position.

The largest product position is12029. The new860 field tests12030..12889 are
therefore zero on every aligned intended assignment, including safe dummy
adjustments, and do not restrict canonical completeness. The population and
low-congruence identities were checked on the actual integers. The unit
2DC-DR modulo5 remains1, preserving actual-rank tuning.

The complete proof also restores the exact disjoint packed-mask identity,
not the false assertion that the two native masks are mutually disjoint.
It yields pc(R)=3t+2 and hence odd s, simultaneously with odd i and square w.
This additional promise is necessary for the24-integer forms. Thus the whole
four-port replacement is justified for the normalized and ordinary arithmetic
interfaces, including the quartic32 used by the nine-variable specialization.

No unresolved issue was found in these new adapter steps. The universal
marked-Wang-language theorem, native/Pell interface, and literal K215 logical
calibration remain explicitly inherited mathematical dependencies. This
review and its finite program are not a fresh Lean/Rocq certification.
