# Either single head-mask deletion admits a full positive false halt

Neither of the two head masks in the complete prefix-first ternary90
certificate follows from the other eight fields and the transports.
Deleting S0 gives a literal **88-operation** source, **48M+40A**;
deleting S1 gives **89 operations, 48M+41A**. Both are false. This note
gives a complete positive counterexample to each source, including its
fixed-plus43 Pell extension, on an input beginning `00`.

The valid90 construction is unchanged. This is not the earlier merged-mask
counterexample: here one head mask is deleted and the other remains Boolean.
The counterexamples preserve Ebar,E,Q,G,M0,M1,GN, both transports, true power
geometry, the fixed input bound, a genuine one-reading event in the real run,
and the singleton-zero endpoint. They are not full Neary Table2 instances.

## 1. Exact proposed sources and operation counts

Retain all fixed coefficients, positive supplied coordinates, and comparisons
of [prefix-first90](EXPLORATION_PREFIX_FIRST_TERNARY_TAG.md). In particular,
write Z=AH for its supplied product coordinate, D for transport_scale,
k=K/3, j_g for its fixed content-guard coefficient, and

    M1=2Q+S1, G=Q+Z, M0=L-M1, Ebar=cH-E, GN=N+j_g Z,
    N=3Tcontent+S1          when the appendant begins zero,
    N=3Tcontent-2Q          when the appendant begins one.

For deletion of S0 take F=S1; for deletion of S1 take F=S0=H-S1.
The retained eight fields, in order, are

    Ebar,E,F,Q,G,M0,M1,GN.

Their exact packing is

    V=Q+qG+q^2[L+(q-1)M1+q^2 GN],
    P=cH+(q-1)E+q^2[F+qV].                         (1)

The checker constructs (1) in 18 operations, 9M+9A, when F=S1.
Computing H-S1 adds one subtraction in the other case. It uses only
q^2 and q^4 before the common scale q^8=q^4*q^4, so the q^9
multiplication disappears. All coefficient multiplications are paid.
This yields 88=48M+40A and 89=48M+41A respectively. Numerals and equality
tests are free, and signed intermediate registers are allowed.

The eight outer comparisons now read

    kD=R,
    D(Tcontent-E+Ut M1)=N-Ninit,
    D(L+(B-1)M1)=L-Linit+3q,
    RH=H+q-1, RH=CZ, Rv=q,
    2r+1=q^8+2P, r+betaP=q^8.                      (2)

The ten fixed-plus43 kernel comparisons are retained at scale D0=q^8.
There are still 29 strictly positive supplied unknowns and 18 equations.
The checker verifies all 18 symbolic sources for each deletion and each
leading-symbol branch. The auxiliary norm correction at full-source index
16 is full-source index 15 times `(u^2-y_aux^2)`, with both indices numbered
from zero. Explicitly, the correction is the preceding auxiliary-norm residual

    ((i*c_p^2)^2-Delta*(f^2-1))*(u^2-y_aux^2).

This source ledger defines the rejected systems; it is not a soundness proof.

## 2. One exact genuinely nonhalting instance

Both examples use

    beta=3, 0 -> 0, 1 -> 010, initial=0011001.

The first symbol is stored at the least significant ternary position.
The genuine transitions are

    0011001 -> 10010 -> 10010 -> ... .

Every word in this orbit has length at least three. This is an exact
nonhalting fixed point, not a time-cutoff claim. The initial word begins
`00`, has a one in its first deleted prefix, and the real run reads a one.
The deletion number is three, so no claim about a full Neary compilation
is made.

Choose the following fixed constants and a genuine width:

    K=27, k=9, B=9, U=3, Ut=1, c=4,
    Ninit=765, Linit=2187,
    C=3^14, C/k=3^12, j_g=(3^14-3^11)/2,
    A=3^9, R=CA=3^23, D=R/k=3^21.                  (3)

In particular C>K^2 Linit=3^13, and A exceeds every source length marker
used below. The other fixed margin requirements hold as well.

## 3. Delete S0 while S1 remains Boolean

For any active marker lambda=3^ell and any z<ell, the pair

    S1row=3^z, Qrow=(lambda-3^z)/2

consists of Boolean ternary words and gives 2Qrow+S1row=lambda. The Q word
is the run of ones from position z through ell-1. Thus Boolean S1 alone
does not anchor its selected symbol at the row head. If 1<=z<beta is a
one in the deleted prefix, taking Erow=(prefix-3^z)/3 also passes both
prefix masks. The scalar content equation can then apply the one appendant
to a genuine zero-headed source word.

Use these six source words, followed by terminal `0`:

    0011001, 1001010, 1010010, 0010010, 00100, 000 -> 0.

The supplied per-row quantities are

| Quantity | Row 0 | Row 1 | Row 2 | Row 3 | Row 4 | Row 5 |
|---|---:|---:|---:|---:|---:|---:|
| S1row | 9 | 1 | 1 | 0 | 0 | 0 |
| Erow | 0 | 0 | 3 | 3 | 3 | 0 |

At each nonzero selector use Qrow=(lambda-S1row)/2; otherwise use Qrow=0.
The first transition is false and every subsequent displayed transition is
genuine. At the first row, lambda=2187, Nrow=765, Qrow=1089, and

    (765-9+3*2187)/27=271=value_3(1001010).

The genuine first successor is instead `10010`. All six effective selectors
are Boolean, and their packed S1 has no digit two. Their content, prefix,
projector and marker fields also remain Boolean. Set
Trow=(Nrow-S1row)/3; each is a nonnegative integer, and the packed T is
strictly positive. E is strictly positive because of the later rows.

## 4. Delete S1 while S0 remains Boolean

A different hole permits a genuine one-headed word to take a zero step.
If its prefix has a zero at some position d with 1<=d<beta, set

    Qrow=(3^d-1)/2, S1row=1-3^d, S0row=3^d,
    M1row=0, Erow=(prefix-1)/3+3^(d-1).

Then 2Qrow+S1row=0 and 3Erow+S1row equals the genuine prefix. Q,S0,E
are Boolean, including the newly filled zero position of E. A later genuine
one step can make the whole supplied S1 positive despite its negative row.

Use four source words, followed by terminal `0`:

    0011001, 10010, 100, 010 -> 0.

| Quantity | Row 0 | Row 1 | Row 2 | Row 3 |
|---|---:|---:|---:|---:|
| S1row | 0 | -2 | 1 | 0 |
| Qrow | 0 | 1 | 13 | 0 |
| Erow | 3 | 1 | 0 | 1 |
| S0row | 1 | 3 | 0 | 1 |
| M1row | 0 | 0 | 27 | 0 |
| Trow | 255 | 10 | 0 | 1 |

Only the transition from `10010` is false. Its content and length equations
are nevertheless exact:

    (28-3*1-(-2)+3*0)/27=1=value_3(100),
    (243+(9-1)*0)/9=27.

The whole S1 equals R^2-2R>0 but is not Boolean. Conversely, S0 is literally
the Boolean packed word with the displayed rows. Every remaining supplied
outer coordinate will be strictly positive.

## 5. Full outer tuples, including parity

In each example pack the displayed Nrow, Qrow, S1row, Erow and Trow
with weights R^i, obtaining N,Q,S1,E,Tcontent. Let L_base pack the ordinary
length markers 3^length(word). All the scalar content and length equations
hold exactly, including the one designated false step in each example.

For the S1 deletion take height h=4, q=R^4=3^92 and L=L_base.
For the S0 deletion the six-row unpadded index is odd. Use the established
zero-edge padding explicitly, with m=23, beta-1=2 and q0=R^6:

    h=6+(23-2)=27, q=R^27=3^621,
    delta=3q0*sum_(i=0)^22 (R/9)^i,
    L=L_base+delta.                                 (4)

These 23 added length bits are distinct and lie between q0 and q. They
belong entirely to M0; every other data word N,Q,S1,E,Tcontent is unchanged.
The identity

    (R/9-1)*delta=3(q-q0)

proves the padded length comparison in (2). This is a formal zero-marker
continuation, not a claim that the short queue `0` executes actual tag steps.
Such continuations are permitted by the retained source; the valid
soundness proof itself stops at the first short row.

In both examples set H=(q-1)/(R-1), Z=AH and v=q/R. The JSON receipt gives
the resulting full outer integers. The formulas above independently specify
them exactly. The eight retained fields lie in [0,q) and are Boolean:

* Q has its displayed Boolean intervals, and G adds the disjoint A bit per row.
* M1 consists of the selected genuine length markers; M0 consists of the
  remaining length markers and, in (4), the disjoint added zero-edge bits.
* E and Ebar partition cH, including the additional empty rows after padding.
* N is Boolean and below A in every occupied content row. The high guard
  j_g Z therefore leaves GN Boolean.
* The respective retained head field is Boolean as proved above.

The omitted field is still positive as a whole integer in both examples.
For deletion of S0, its low trits include a two because S0=H-S1 and the first
selector is 9. For deletion of S1, R^2-2R has forbidden trits. Thus merely
retaining global positivity of the omitted field would not repair either
source.

Form P from (1) and set

    D0=q^8, r=P+(D0-1)/2, betaP=D0-r.              (5)

Ebar has unit trit one in both tuples. Hence r has unit trit two and all
remaining trits one or two; its central-binomial valuation is exactly
the number of D0's ternary positions. This number is 4968 in the S0
deletion and 736 in the S1 deletion. In both cases

    r is even, D0>=81, 27<=r<D0, D0<r^2, betaP>0.   (6)

The even parity can also be checked without giant integers. The exponent
of D0 is even, so (D0-1)/2 is even. In the S0 deletion, P modulo two is
S1+L+N: S1 is odd, N is even, and the 23 added markers make L odd.
In the S1 deletion it is H-S1+L+N: H and L are even, while S1 and N
are odd. Here c=4 is even and j_g is odd, so the omitted coefficient
terms contribute evenly. Thus (5) gives an even r in each case.

## 6. Sixteen fresh positive Pell witnesses

Apply the [general-scale fixed-plus43 converse](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md)
to each new pair (D0,r). Its hypotheses are precisely (6), power-three D0,
and the divisibility just proved. For completeness, an exact specification
of all sixteen witnesses is as follows, using the standard Pell sequences
chi_X,psi_X and avoiding the fixed prefix constant c:

    J=2r+1, Up=3^J,
    Y=floor((Up+1)^(2r)/Up^r), w=Up/D0, s=Y/D0,
    a=Y(Up+1), A_p=a+3, Delta=A_p^2-1, P_p=2Up Y^2+1,
    c_p=psi_(A_p)(J), d=chi_(A_p)(J), k_p=psi_(P_p)(r+1),
    eta=c_p-Y k_p, zeta=k_p-eta,
    tau=(chi_(P_p)(r+1)-1)/2, h_p=(k_p-r-1)/(Up Y),
    gamma=(d-Up-a c_p)/(6a+8),
    m_aux=2c_p J, f=chi_(A_p)(m_aux),
    R_aux=Delta psi_(A_p)(m_aux), i=R_aux/c_p^2,
    u=chi_(R_aux)(J)/R_aux, y_aux=psi_(R_aux)(J),
    j=(u-J)/c_p, o=(u-c_p)/f.

The cited converse proves integrality and strict positivity of every
supplied value, as well as all ten equations. Since r is even, J=1 modulo
four, giving the plus signs in both normalized-root congruences. The enormous
auxiliary integers are specified by these exact formulas and proved to
exist; they are not materialized by the finite checker. No auxiliary tuple
from another packing or index is reused.

Together with (2)--(6), these witnesses give full positive solutions of the
rejected 18-equation systems for an actually nonhalting input. Consequently
neither single head-mask deletion is valid on the stated initial00 domain.

## 7. Evidence and scope

The companion [checker](../verification/explore_deleted_tag_head_masks.py)
and [receipt](../verification/explore_deleted_tag_head_masks.json) verify all
four complete schedules: both deletions, each in both leading-symbol branches.
They compare all 72 symbolic source residuals, the packing identities and
the retained norm corrections. The two zero-leading counterexamples check
every scalar transition, the unique false transition, the actual nonhalting
fixed point, all eight whole-source outer comparisons, all eight remaining
masks and field bounds, positive outer coordinates, padding, even index,
and exact central valuation.

This does not preclude a replacement head encoding with additional equations,
or a separate implication relying on full Neary-specific constraints absent
from the current normalized theorem. It refutes the two explicitly stated
single-mask deletions and the proposed inference from the other retained
fields and transports alone.

Review status: author and two independent complete proof/source reviews and
fresh receipt checks PASS. One reviewer previously contributed the local
S1-deletion mechanism; the complete gates additionally cover both exact
sources, the independently authored S0 construction and both Pell extensions.
