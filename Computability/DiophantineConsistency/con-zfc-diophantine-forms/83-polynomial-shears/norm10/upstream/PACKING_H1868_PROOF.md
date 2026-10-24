# Exact compatible target layout of height 1868

This finite certificate changes only target positions, not source coordinates,
source residuals, variable weights, coefficient ports, or bit-extraction logic.
It uses the whole original31 wang943-mixed-121x8801 tuple from the prior packet.
The source and weights are byte-level JSON specifications; coefficients are
formal polynomials in beta,K0,MC,MF, with the same materialized values as before.

The exhaustive symbolic extraction verifies all monomials, including absent
ones, in all22 identities [T^q_j](D2 U^2+D1 U+D0)=2 rho_j.
Equal tap coefficients are retained once, never added. There are86 records
and81 distinct stored positions. The new layer degrees are1408,1727,1636,
W=116,H=1868,Q=1836. The leading coefficients remain -6,+2,+1.
The dominance gaps are460,25,0, so the previous unconditional positivity proof
applies: D2 dominates D1 by25 powers of B and D0 by460 powers.

Every coefficient is unchanged from the prior86-record source, so the bound
M=2^2134927 remains valid without recalibration or mixing coefficient tuples.
The same sparse carry estimates use B>=4096 M b^2. The target headroom H-Q=32
is unchanged. Replace H1873 by1868 in the prior derivation; all inequalities
are at least as strong, except the harmless constant-layer gap460 instead489,
which is still much larger than the required gap1.

For the ten-integer interface use N0=B^117, Z=B^1869, Nblock=B^1986,
Y=2^(16*2134940-23) b B^2109, cap=b B^116. The sourceX degree is7942,
and sourceY degree4219. Consequently the prior free-Lucas finalizer has degree
96*7942+192*4219+544=1573024, before any additional finalizer simplification.
Actual circuit operations must be recomputed, not inferred from this table.

This is an existential-equivalence-preserving coefficient encoding and a
finite exact certificate. It is not a new proof-assistant kernel certificate,
new smaller variable count, or optimality claim. The small height reduction
is supplementary to the main round11 structural results.
