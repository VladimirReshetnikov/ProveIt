# A 94-operation binary certificate on the original first-zero domain

The complete binary tag certificate has a **94-operation** schedule,
**50 multiplications and 44 additions/subtractions**, with 28 positive
unknowns and 17 equations, on the full first-zero input domain of
`EXPLORATION_REORDERED_BINARY_TAG_PACKING.md` (binary95).

This ties the count of `EXPLORATION_PREFIX_FIRST_BINARY_TAG_PACKING.md`
while removing that construction's additional initial-second-zero promise.
It uses a different field order and the fixed minus version of the
43-operation base-two Pell kernel. There is no runtime sign selector.
The domain remains beta>=2, an appendant of length a>=2 beginning zero,
an initial word beginning zero with a nonzero symbol among its first
beta deleted symbols, a genuine one-reading event, and singleton-zero
termination for completeness. Soundness is the same eventual-halting
statement as binary97/95. The normalized Neary001 family is included,
but this is not a fixed-appendant/raw numerical-input construction or
an optimality claim. The ternary normalized frontier is now 90.

## 1. Reordered fields and two shared identities

Keep the fixed constants, positive supplied coordinates, and derived
values of the complete binary97 construction:

    R=kD, N=2Tcontent+S1, M1=Q+S1, L=Nsum+H,
    c=k-1, k=2^(beta-1), n=q^6, scale=n^2=q^12.

The six paired coefficients, from lowest to highest, are

| Pair | S coefficient | W coefficient |
|---|---|---|
| Projector guard | Q | Q+AH |
| Projector marker | Q | Q+M1 |
| Prefix partition | E | cH |
| Head partition | S1 | H |
| Marker partition | M1 | L |
| Content partition | N | Nsum |

With the already-paid q2=q*q and q3=q2*q, put

    qp1=q+1, F=qp1*Q, X=q*M1,
    S=F+q2[E+q(S1+X+q2*N)],
    W=AH+F+X+q2[(q+c)H+q2(H+qp1*Nsum)].             (1)

The identity L=Nsum+H is used in the upper denominator blocks:

    q^4 L+q^5 Nsum=q^4[H+(q+1)Nsum].

The prefix and head blocks use

    q^2(cH)+q^3 H=q^2(q+c)H.

Together these make (1) exactly the displayed pair packing. The
quantity qp1 is shared by F and the upper denominator expression.
No standalone cH multiplication occurs. Both full packs cost
9M+11A=20 operations, including F,X and all their shared arithmetic.

The complete source ledger is

| Portion | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Derived coordinates and transports | 7 | 9 | 16 |
| Shared-product geometry | 3 | 2 | 5 |
| Both reordered packs | 9 | 11 | 20 |
| q^2,q^3,q^6,q^12 | 4 | 0 | 4 |
| Packed complement and index | 2 | 4 | 6 |
| Fixed-minus base-two kernel | 25 | 18 | 43 |
| **Total** | **50** | **44** | **94** |

Numerals and equality comparisons are free; all displayed coefficient
multiplications and variable powers are paid in this ledger.

## 2. The complete outer source and pre-kernel bounds

Retain the seven comparisons

    D(Tcontent-E+Ut M1)=N-Ni,
    D(L+(B-1)M1)=L-Li+2q,
    S+Tplus=W+1,
    RH=H+q-1,
    RH=C(AH),
    Rv=q,
    r=(n-1)(n(W+1)+Tplus).                         (2)

All twelve outer coordinates remain positive. The fixed constants,
including the margin on C, are unchanged from binary97/95. Although
the packed polynomials change, their W coefficient list is merely
permuted and the content coefficient N is still highest in S.

Consequently the entire preliminary argument from the complete
binary97 proof applies. First k even gives R,q even, the head
equation gives H odd, and RH=C(AH) with C a power of two gives C|R.
Thus A=R/C is a positive integer and AH=A H. The length equation
and the fixed C margin bound every W coefficient below q, giving
0<W<n. Positive S,Tplus with their comparison imply S<n. Since
q^5 N<=S, one obtains N<q. The unchanged content transport then
bounds E<q, so all S coefficients are nonnegative and below q
before the Pell or bit-mask argument. In particular no complement
is assumed positive before its typing is recovered.

Set T=Tplus-1>=0. Then S+T=W<n and the index comparison is exactly

    r=S(n^2-n)+(T+1)(n^2-1),
    n>=64, n<=r<2n^3.                              (3)

These are the same base-two43 bootstrap hypotheses as before.

## 3. The fixed minus kernel is sound without a parity assumption

Use the ten retained base-two kernel comparisons at scale n^2, with
the same sixteen positive auxiliary coordinates. Write c_p for the
Pell coordinate (distinct from the fixed prefix coefficient c), and
J=2r+1. Change only the two auxiliary congruence constructions:

    u=J+j*c_p, u=c_p+o*f

become

    u=j*c_p-J, u=o*f-c_p.                          (4)

The two products and the two additions/subtractions have the same
cost. This is exactly the fixed-minus extension proved in
`EXPLORATION_ODD_INDEX_PELL_SIGNS.md`; the retained base-two
discriminant and exponential source are unchanged.

For clarity, its soundness does not assume the parity of a putative
r. The main and auxiliary Pell arguments, independent of (4), first
give c_p=psi_A(p), f=chi_A(m), c_p|m, 0<2p<=m and 0<J,p<c_p.
The auxiliary norm classifies u up to sign, and its two polynomial
congruences together with (4), after squaring the congruence modulo f,
still give J=plus or minus p modulo c_p. The alternative J+p=c_p
is excluded by c_p=psi_A(p)=p modulo two while J is odd. Thus p=J
as before, and the remaining exponential and central-binomial proof
is identical. Equivalently, since j is positive and c_p>J, (4)
already gives u>0 at this stage; no early sign assumption is needed.

The kernel therefore recovers q as a power of two and n^2 dividing
binom(2r,r). The same exact popcount identity for (3) yields S&T=0.
Since the six fields were bounded beforehand, their extraction gives

    Q&AH=0, Q&M1=0, E&(cH-E)=0,
    S1&(H-S1)=0, M1&(L-M1)=0, N&(Nsum-N)=0.

These are exactly the binary97/95 predicates, with their four
nonnegative complementary words. The unchanged true-power row
geometry and transports consequently give the same first-short-row
halting soundness proof. The first-pair choice does not alter it.

## 4. Positive converse and automatic odd index

Given a genuine promised singleton-zero halt, retain the same
ordinary-binary row words, fixed C and sufficiently wide A as in
binary95. All outer supplied coordinates remain positive. Form S,W
by (1), and set

    Tplus=W-S+1,
    r=(n-1)(n(W+1)+Tplus).

The six AND conditions give S<W<n and positive Tplus. The unit
bit of Q is zero because the initial head symbol is zero. Also
AH=A H is even because the chosen A is a positive power of two
strictly above every source marker. The lowest pair is (Q,Q+AH),
so S and W are both even. Hence Tplus is odd, and since n is even,
the index r is odd. This argument does not refer to the second
initial symbol and works for either parity of beta.

The exact valuation remains 2log2(n), with the range (3) and scale
n^2. Apply the full positive converse with the fixed minus signs.
Specifically, J=3 modulo four. In the ordinary normalized-root
construction, the positive auxiliary value u satisfies

    u=-J mod c_p, u=-c_p mod f.

Thus j=(u+J)/c_p and o=(u+c_p)/f are positive integers satisfying
(4). All the other fourteen auxiliary coordinates have the same
positive-converse construction, at the new index. This supplies
sixteen fresh positive witnesses. The old binary95 index was even,
so neither it nor its auxiliary tuple is reused.

## 5. Exact verification and evidence boundary

The maintained checker is
`../verification/explore_odd_binary_tag_packing.py`, with an adjacent
JSON receipt recording the complete 94-operation DAG. It verifies
both pack identities and all seventeen source comparisons. Only
comparisons 2,6,15,16, numbered from zero, change from binary95:
the packed comparison, index, signed auxiliary norm and final
auxiliary congruence. The triangular norm correction at comparison
15 is retained with the new u, namely source14 times `(u^2-y_aux^2)`.

The fresh regression uses the original binary95 corpus of 88
histories and 382 source rows, including 48 odd-beta histories.
Seventy-two of these initial words begin `01`, explicitly exercising
the domain restored relative to prefix-first94. It checks both
old and new seven-comparison outer schedules, all six new ANDs,
positive coordinates, pre-kernel coefficient and index bounds,
and exact old and new valuations. All 88 indices change from even
to odd. The enormous new Pell auxiliaries are not materialized;
their full positive existence is proved by the general converse
after all required new index hypotheses have been checked.

Review status: author and two independent complete proof/source/dependency
reviews PASS; fresh verification reproduces the saved receipt. Both
binary95 and prefix-first94 are preserved unchanged.
