# Zero-terminal tag histories admit either index parity

For even deletion number beta>=2, every genuine halt with terminal content
zero has two complete nine-field outer witnesses, at the same encoded input
and width, whose kernel indices have opposite parity. One witness stops at
the genuine halt. The other appends a complete cycle of zero-channel length
edges, while keeping all numerical content zero after that halt.

This gives three separately counted positive certificates:

| Terminal specialization | Operations | Positive unknowns | Comparisons |
| --- | --- | --- | --- |
| No endpoint specialization | 103=52M+51A | 32 | 19 |
| Terminal content zero | 100=51M+49A | 31 | 19 |
| Terminal word exactly `0` | **99=51M+48A** | 29 | 18 |

Their soundness is actual eventual halting for every admitted input.
Completeness of103 and100 is proved here for even beta and actual
zero-content halts;99 further requires the actual terminal word to be the
single symbol `0`. On a domain where every halt has the relevant terminal
property, the corresponding source is a complete halting certificate.

This is not a proof that every halt admits an odd-duration witness. The
padding actually preserves the duration's parity and flips the index directly.
Nor is this a generic103,100 or99 converse for nonzero-terminal halts or odd beta.
The encoded-word input remains unchanged. Neary's encoded instances satisfy
the required terminal condition, as explained in Section6; no fixed-u/raw-input
universal polynomial follows from that compatibility statement.

Author and two independent complete proof/source reviews and fresh full
verification runs pass without findings. The companion receipt records the
checks. The published single-content-guard104 source is unchanged.

## 1. The precise43-operation kernel requirement

Use the two fixed-sign kernels proved in
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`. Their soundness, under

    D0>=81, r>=27, r<2D0, D0<r^2,

does not require a parity hypothesis. Their proved positive converse uses
the fixed sign sigma=(-1)^r. In particular the plus kernel gives every
positive auxiliary witness when r is even. The sign is fixed in the
certificate; it is not a free runtime choice. The theorem does not assert
nonexistence of other witnesses at the opposite parity.

The plus kernel costs43=25M+18A with16 positive auxiliary coordinates and
ten comparisons. The parity-free kernel of the104 predecessor costs44,
with17 auxiliaries and eleven comparisons. Replacing it by the plus kernel
changes none of the60 outer instructions or their nine comparisons. Thus
the new schedule costs103=52M+51A, with32 positive unknowns and19 comparisons.

The entire104 pre-mask bootstrap still applies: the outer positive domains
first give P>0 and (q^9-1)/2<r<q^9. These satisfy all the43 scale hypotheses.
Its soundness then gives the same ternary-power and unit-two conclusions,
so the full nine-field recovery and signed-content soundness proof apply
without any assumption about the index's parity.

## 2. The exact parity of the nine fields

Use the notation and fixed compiler constants of
`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`:

    K=3^beta, k=K/3, cc=(k-1)/2,
    C>max(K^3,K*3^a,2KU+3), j=(C-C/K)/2,
    R=3^m=CA, q=R^t, H=(q-1)/(R-1).

The nine field expressions are

    Gstar,Q,S0,S1,M0,M1,Ebar,E,GN,
    Gstar=Q+AH+S0, S0=H-S1, L=M0+M1,
    Ebar=ccH-E, GN=N+jAH.

Their sum is

    2Q+(j+1)AH+(cc+2)H-S1+L+N.

Since A and q are odd, the packing satisfies

    P=N+S1+L+(1+cc+j)H mod2.

The integer cc has parity beta-1, while
j=3^(log_3 C-beta)*(3^beta-1)/2 has parity beta. Therefore

    P=N+S1+L mod2,
    r=P+mt mod2.                                      (1)

These identities hold for every decoded nine-field witness. They do not
assume that each formal row contains exactly one marker or that N is Boolean.
The second identity uses D0=q^9 and
r=P+(D0-1)/2; the parity of (3^e-1)/2 is e mod2.

## 3. Adding a complete zero-edge cycle

Consider any genuine halting computation with terminal word consisting only
of zeros. Write its terminal length marker as F=3^s, where
0<=s<beta. Choose one sufficiently large odd width exponent m such that

    m>2(beta-1), A=3^m/C

is a power of three strictly larger than every genuine source length marker.
This is always possible by enlarging m. There is no counted exponentiation
or extra width comparison in the certificate: this is the construction of
existential witnesses from a finite halting trace.

Let the genuine history have t source rows, q0=R^t, and write h=beta-1.
Its zero-channel length-edge multiplier is

    b=R/k=3^(m-h).

Append exactly m further zero-channel edges, starting at the old terminal
marker q0 F. Define

    DeltaM=q0 F*(1+b+...+b^(m-1)),
    T=t+m-h, q1=R^T.

Because b^m=R^(m-h), the new endpoint is q1 F, with exactly the same
short within-row marker F. The added source exponents are

    tm+s+i(m-h), i=0,...,m-1.

They are distinct and all at or above tm, disjoint from every original
source bit. The largest is

    (T-1)m+s+h<Tm,

because s<=h and m>2h. Thus DeltaM is Boolean and lies entirely below q1.
Some artificial rows contain two M0 markers. This is allowed: the104 source
has no containment equation imposing exactly one marker in every post-halt row.

Set

    M0_new=M0_old+DeltaM, M1_new=M1_old,
    L_new=L_old+DeltaM, H_new=(q1-1)/(R-1).

Keep Q,S1,E,N and terminal content Nf=0 unchanged. Extend the computed
head-dependent fields using H_new:

    S0_new=H_new-S1,
    Gstar_new=Q+AH_new+S0_new,
    Ebar_new=ccH_new-E,
    GN_new=N+jAH_new.

All nine fields are Boolean. The original low rows are unchanged. In each
additional row Q=S1=E=N=0; S0 contributes its head, Gstar its head and
A-position, Ebar its fixed prefix block, and GN the top-beta guard.
The additional M0 bits may share a row with these other fields, since the
fields have separate q-block masks; their own exponents never coincide.

The exact length-flow identity is preserved because

    (b-1)DeltaM=q1 F-q0 F.

Equivalently, adding DeltaM to M0 and L changes both sides of the length
source by the same value. The content source is unchanged: Q,S1,E,N and
the input are fixed, while the sole q-dependent term qNf remains zero.
The new H and v=q1/R satisfy the paid geometry. A,R and both boundary
slacks remain unchanged because F and the input length are unchanged.
The positive content-coordinate adapter T is unchanged as well.

Hence the unpadded and padded constructions are actual complete outer
tuples, not merely a formal path identity or a local mask illustration.

## 4. The cycle flips the index and supplies the positive converse

The unchanged N and S1 and the m added M0 bits imply, by(1),

    P_new-P_old=m mod2.

The native-offset parity changes by m(T-t)=m(m-h). Therefore

    r_new-r_old=m+m(m-h)=mh mod2.                      (2)

When beta is even, h is odd; m was chosen odd. Thus(2) equals1. Exactly
one of the two outer tuples has even r. Notice that T-t=m-h is even:
the construction flips the index without changing the height parity.

Choose the even-index member. Pack its nine Boolean fields and set
D0=q^9, r=P+(D0-1)/2 and betaP=D0-r. The first trit of Gstar is still1;
the native word has unit2, with exact central-binomial valuation log_3 D0.
All positive scale and packed-slack inequalities hold as in104.

The fixed-plus43 theorem now supplies all sixteen positive Pell auxiliaries.
They are rebuilt at the chosen new index. No old auxiliary tuple is reused,
and no large Pell value is silently materialized. This proves the103
positive converse for every even-beta genuine zero-content halt.

The compiler sign stays plus in both appendant-leading branches. The
existential choice between the two explicitly constructed histories is
ordinary witness existence, not an uncharged choice of source equations.

## 5. The fixed-zero100 source

For the completeness class just proved, both histories have Nf=0. The
source can therefore specialize this endpoint to zero. Delete the positive
unknown F_Nfinal and the three instructions

    Nfinal=F_Nfinal-1,
    n_end=q*Nfinal,
    n_shift=n_initial+n_end.

Compare n_left directly with n_initial=N-Ni. This removes one multiplication
and two additions from103, giving

    100=51M+49A, 31 positive unknowns, 19 comparisons.

Every zero-target solution extends to a103 outer solution by F_Nfinal=1;
its fixed-plus kernel is identical. Thus actual halting soundness is inherited.
Conversely, the parity construction already has Nf=0 and supplies every
remaining positive coordinate, proving the same zero-terminal completeness.

The checker expands the complete source for both100 and103 and both fixed
appendant-leading branches. The nine outer comparisons and ten kernel
comparisons are checked separately against their source polynomials. The
known norm-source correction is at comparison17. The fixed-zero substitution
does not omit a divisibility equation or an endpoint adapter still used elsewhere.

### 5.1. The single-zero99 source

If the actual terminal word is exactly `0`, the cycle preserves its marker
F=3 as well as Nf=0. Specialize the100 source to Lfinal=3. Delete the positive
unknowns Lfinal and alphaH, the instruction

    halt_bound=Lfinal+alphaH,

and its comparison with K. Replace the sole remaining Lfinal use by the
fixed numeral3 in l_end=q*3. That multiplication remains charged. The result is

    99=51M+48A, 29 positive unknowns, 18 comparisons.

Every99 tuple extends to a100 tuple by Lfinal=3 and alphaH=K-3. This slack
is strictly positive because even beta>=2 gives K>=9. Thus soundness again
follows from100. Conversely, for an actual halt at the single-symbol word `0`,
both parity witnesses constructed above have the same endpoint marker3;
the even-index member supplies every remaining positive coordinate of99.
No conversion of the encoded input or new boundary operation is needed.

The two99 branch schedules have eight outer comparisons and ten kernel
comparisons. Symbolic substitution makes the deleted terminal-bound source
identically zero. The norm-source correction moves to comparison16. All
packing, radix, content and length polynomials are otherwise the same after
substitution; in particular l_end=q*3 remains an actual runtime product.
This is not a99 converse for a longer all-zero terminal word.

## 6. Compatibility with Neary's encoded instances

Neary's Lemma9 uses beta=10p and productions b->b, c->u, with a designated
suffix of u as input. Its halting simulation enters an all-b cleanup.
The normalization in Theorem11 chooses s=x(beta-1)+1; every reachable length
is1 modulo beta-1, so the true terminal word is exactly b. With b=0, these
instances have even beta, Nf=0 and F=3, precisely the premises for99.
See Lemma9 and Table2 on pp655-656 and the normalization on p660 of
[Neary, STACS2015, DOI10.4230/LIPIcs.STACS.2015.649](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).

This is compatibility with the constructive encoded-instance reduction.
The cyclic program and its input are compiled into u. It does not give
one fixed u with a raw numerical input loader, or a universal raw-input
Diophantine bound of99. No such stronger interface is asserted.

## 7. Exact evidence and remaining scope

`explore_zero_terminal_tag_parity.py` verifies all six complete schedules,
their112 source comparisons, the field-sum identity, the fixed constant
parities and the wrapped exponent paths. The path tests include artificial
rows with multiple length markers. The source regression builds canonical
and padded outer tuples from actual zero-terminal halts, checking all nine
masks, both103/100 endpoint-source variants and the exact new valuation for
each. The99 schedule is additionally checked whenever the terminal word is
exactly `0`, including all eight retained outer comparisons and the positive
inverse boundary slack K-3.
Exactly one member of each pair has even index and is covered by the full
positive plus-kernel converse.

The author and independent fresh runs passed all six schedules and112 symbolic comparisons,
96 constant-parity checks and110 wrapped paths, including670 artificial rows
with multiple markers. It constructed454 complete outer tuples from227
zero-terminal histories with391 genuine source rows. The unpadded indices
split136 even and91 odd, so91 selected witnesses require the padding. Among
these,173 histories terminate at the single zero symbol; their346 canonical
and padded tuples also pass the99 source, and73 require padding to select the
even index. These are fresh outer/mask/valuation checks together with the
proved positive43 extension, not materialized huge Pell auxiliary tuples.

The finite program examples are ordinary tag programs used to test this
arithmetic theorem. They are not presented as materialized Neary universal
machines. Nonzero-terminal halts and runs reaching the simulation cutoff
are recorded separately. No completeness claim for those cases, or for
odd beta, follows from this padding lemma.
