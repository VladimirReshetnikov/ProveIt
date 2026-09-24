# Prefix-complement fusion into the content guard admits a full false halt

The complete nine-field104 certificate has separate masks on E, Ebar and
GN=N+jAH. A natural attempted saving removes Ebar and instead masks

    GF=N+jAH-D E,  D=R/k=3R/K.

For a genuine source row, with b=R/K and hK=(K-1)/2, this puts the prefix
complement into the high guard: its row is n+b(hK-3e). It saves packing
operations, but it also allows a borrow from one row to alter the next
row's apparent content. The attempted construction below has an exact
**103-operation schedule, 51M+52A**, including explicit positivity of GF
and a bound E<q. A full positive counterexample refutes even this version.
The valid104 certificate is unchanged; no improved bound is claimed.

Author and independent complete proof/source reviews and fresh verification
runs pass without findings. The maintained [checker](../verification/explore_fused_prefix_content_guard.py)
and [receipt](../verification/explore_fused_prefix_content_guard.json)
contain the full source comparisons and exact positive outer tuple.

## 1. The precise proposed source

Retain the input, fixed constants, all coordinates and all nine outer
comparisons of [the complete104 source](EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md),
except for the new packed word and scale. Keep its first six fields and use

    Gstar,Q,S0,S1,M0,M1,E,GF,
    P=Lo6+q^6(E+q GF), D0=q^8.

Add positive supplied coordinates GuardPositive and PrefixSlack, with

    GF=GuardPositive, E+PrefixSlack=q.

These ensure GF>0 and E<q before any Boolean decoding. They are explicitly
counted: computing the second comparison's left side costs one addition;
the first compares an already computed register with a supplied coordinate.
Thus there are **35 positive unknowns and 22 equality comparisons**.

Begin with the rejected Ebar-deletion100 DAG, which already packs E and GN
in the last two fields. Compute D E, subtract it from jAH, and use that
reduced guard in its existing addition with N. These add one multiplication
and one subtraction. The explicit E bound adds one addition. This gives
103=51M+52A. The checker verifies all22 symbolic source comparisons in
both fixed appendant-leading-symbol branches; the retained kernel norm
correction is at comparison19.

The new upper bound is included because E positivity alone would permit
carry into the next q-block. Likewise, GF positivity is included rather
than inferred from the predecessor's different guard. The counterexample
satisfies both additions, and even satisfies all eight masks individually.

## 2. A genuine fixed point and a false seven-row history

Take the same program 0->0, 1->01 and deletion number beta=2, so

    K=9, k=3, B=3, U=3, cc=1,
    C=2187, j=972.

The actual input is 10101, read least significant symbol first. Its
coordinates are Ni=91 and Li=243. Deleting its first two symbols and
appending01 gives 10101 again, so this input never halts.

The following false history ends at Nf=0,Lf=3:

| Row | n | Length marker | Selector | e | Extra prefix t | Previous t | Guarded low content |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 91 | 243 | 1 | 81 | 27 | 0 | 91 |
| 1 | 64 | 243 | 1 | 90 | 30 | 27 | 37 |
| 2 | 58 | 243 | 1 | 91 | 30 | 30 | 28 |
| 3 | 57 | 243 | 0 | 10 | 3 | 30 | 27 |
| 4 | 3 | 81 | 0 | 1 | 0 | 3 | 0 |
| 5 | 0 | 27 | 0 | 0 | 0 | 0 | 0 |
| 6 | 0 | 9 | 0 | 0 | 0 | 0 | 0 |

Every e and t in the table is ternary Boolean. Write e=e0+k t, where
e0=(n modK)/3 rounded down. The low deleted prefix n modK is Boolean in
every row, even though some full n are not. All scalar transitions hold:

    n_i-3e_i-s_i+U s_i L_i=K n_(i+1),
    L_i(B if s_i=1 else 1)=k L_(i+1).

They telescope to the unchanged content and length transports, including
the original input and terminal zero. The checker verifies these exact
integer equalities row by row and again in the whole packed source.

## 3. Why the fused guard does not detect the false history

Choose A=729>243 and R=CA=1594323=3^13. Let q=R^7 and
H=1+R+...+R^6. Form N,E,Q,S1,M0,M1,L by their literal row sums.
The row contribution to GF is

    n_i+b(hK-3e_i)=n_i+b(hK-3e0_i)-R t_i.

Consequently the normalized GF row has low content n_i-t_(i-1),
as displayed in the final column, and high guard hK-3e0_i. The last
t is zero, so there is no outgoing borrow at the end of the whole word.

Each guarded low content is Boolean, and each high guard is either1
or4. Their ternary positions are disjoint. Hence GF is strictly positive,
Boolean and belowq. The first six fields are the ordinary correctly typed
length/projector words, and E is Boolean and belowq. Gstar has unit trit1.
Thus every individual retained mask passes. The old omitted Ebar=H-E
is itself positive, but non-Boolean; global positivity of that word also
would not repair this failure.

Supply F_Q=Q+1,F_S1=S1+1,F_E=E+1,F_Nfinal=1 and
F_T=(N-S1)/3+1. The divisibility follows from each n_i mod3=s_i, and
all these coordinates are positive. Supply the geometry and lengths above,
v=q/R, alphaI=A-243=486, alphaH=9-3=6, together with
GuardPositive=GF and PrefixSlack=q-E. These are all strictly positive.

## 4. Complete positive Pell extension and evidence boundary

Use the eight-field P and set

    D0=q^8, r=P+(D0-1)/2, betaP=D0-r.

Every source comparison outside the kernel now holds exactly. The index
has native ternary digits1/2 and unit2, with exact central-binomial
valuation

    v3(binomial(2r,r))=8*13*7=728.

The checker verifies 27<=r<D0, D0<r^2 and betaP>0. The established
parity-free44 converse supplies fresh strictly positive values for all
seventeen Pell auxiliaries at this new index. Thus the false tuple extends
to a solution of the complete22-equation source. These enormous auxiliary
values are not claimed to have been materialized.

The verification covers both complete symbolic sources, their exact
operation counts, the complete positive outer tuple, all eight individual
masks, the exact index valuation and the genuine nonhalting fixed point.
This rejects the stated fusion and bounds, rather than establishing a
lower bound against different ways to share prefix and content checks.
