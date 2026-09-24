# Sharing the two binary packs: the same certificate in 96 operations

The complete binary tag certificate in
`EXPLORATION_BINARY_TAG_AND_KERNEL.md` has an exact **96-operation**
schedule: **52 multiplications and 44 additions/subtractions**, with the
same 28 positive unknowns and 17 source equations. This saves one addition
by sharing a repeated band in its two six-block packs.

Every supplied value, source polynomial, packed word, scale, index, and
positive Pell witness is unchanged. The result therefore has exactly the
published 97-operation theorem's encoded-instance promises and scope.
It remains five operations above the normalized ternary 91-operation
route. No optimality, fixed-appendant, or raw numerical-input claim is
made. The published predecessor files are unchanged.

## 1. Exact identity and shared schedule

Retain the predecessor's coefficients and positive coordinates, including

    N=2Tcontent+S1, M1=Q+S1, L=Nsum+H.

Its packs are

    S=S1+q M1+q^2 E+q^3 Q+q^4 Q+q^5 N,
    W=H+q L+q^2(cH)+q^3(Q+M1)+q^4(Q+AH)+q^5 Nsum.

The fixed pair order and orientation remain unchanged. In particular the
first pair is (S1,H), which gives the even canonical index, and the last
pair is (N,Nsum), which supplies the pre-kernel content bound.

Move the already-paid instruction q2=q*q before the packs, and compute

    qp1=q+1,
    Qband=qp1*Q,
    qAH=q*AH,
    other_band=M1+qAH,
    q2N=q2*N,
    S_high=Qband+q2N,
    q2Nsum=q2*Nsum,
    Wband=Qband+other_band,
    W_high=Wband+q2Nsum.                           (1)

Then append the three low coefficients of each pack by ordinary Horner
steps:

    S=S1+q(M1+q(E+q S_high)),
    W=H+q(L+q(cH+q W_high)).                       (2)

The identities

    Qband=Q+qQ,
    Wband=(Q+M1)+q(Q+AH)

show that (1)-(2) equal the old S,W for arbitrary integer values, before
any source equation, positivity condition, or bit decoding is used.
The separate old calculations WM=Q+M1 and WG=Q+AH are deleted.

## 2. Complete count and source equivalence

The old top three coefficients of S and W used four Horner pairs, costing
4M+4A, plus the two coefficient sums WM and WG, costing 2A. Thus that
portion cost 4M+6A=10 operations. The nine instructions in (1) cost
4M+5A. The low six Horner pairs and the power chain have exactly their
old costs. Moving q2 introduces no new multiplication and does not
duplicate its definition.

| Portion | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Derived coordinates, transports, cH | 8 | 9 | 17 |
| Shared-product geometry | 3 | 2 | 5 |
| Both complete packs | 10 | 11 | 21 |
| q^2,q^3,q^6,q^12 | 4 | 0 | 4 |
| Packed complement and index | 2 | 4 | 6 |
| Base-two Pell kernel | 25 | 18 | 43 |
| **Total** | **52** | **44** | **96** |

The six-bit-pair interface still uses the supplied positive Tplus and
the equations

    S+Tplus=W+1,
    r=(n-1)(n(W+1)+Tplus), n=q^6.

Consequently the index and its squared scale q^12 are unchanged. All
other source equations and all supplied coordinates are identical to the
predecessor. The map between positive solution tuples is literally the
identity, including the sixteen Pell auxiliaries. There is no need for
a new parity argument, changed-width history, or fresh Pell-coordinate
construction to prove equivalence.

The source checker independently compares all seventeen fresh symbolic
source polynomials against the full new schedule and the old schedule.
The retained triangular correction at zero-based comparison 15 is still
comparison 14 multiplied by `(z^2-y^2)`. Comparison 14 is exact. No
additional correction arises from the packing identities.

## 3. Bounds, soundness, and positive converse

The published pre-kernel order is unchanged: the shared geometry first
recovers R=CA and AH=A H; the length equation bounds every W coefficient;
positive Tplus then bounds S and its highest coefficient N; the content
equation bounds E. The single power/binomial kernel makes S a bit-subset
of W and recovers all six separate AND predicates and all four implicit
complements. In particular the two tests involving Q remain distinct.

Since both complete packed values are identically unchanged, none of
these deductions requires bounds on a new intermediate register. The
same initial-width proof and first-short-row argument certify actual
halting. Every promised genuine singleton-zero run has exactly the same
positive outer tuple, even index, valuation, and positive kernel
extension in the new source.

## 4. Fresh verification and scope

The maintained checker is
`../verification/explore_shared_binary_tag_packing.py`; its adjacent JSON
contains all 96 primitives and the full source-comparison receipt. Its
source proof treats coefficients as symbolic fixed numerals, verifies the
two packing identities without source substitutions, and confirms that
q2 is evaluated exactly once.

A fresh complete regression constructs 88 positive canonical histories,
with 382 genuine source rows and 48 odd-beta histories. For each it checks
all seven outer equations under both schedules, all six AND predicates,
the pre-kernel ranges, and the exact even index and valuation. Every
packed value, scale, Tplus, and index agrees with the predecessor. The
enormous Pell coordinates are not materialized; the identical positive
solution set and the predecessor's general converse supply them.

Review status: author and two independent complete proof/source/dependency
reviews and fresh verification PASS, with no findings.
