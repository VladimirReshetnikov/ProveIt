# Independent Pell and arithmetic audit of the 82-operation history component

Audit result: PASS. This concerns the finite-history component
`../verification/round42_1980_implicit_history_bound.py`; it establishes no
universal bound below 90. The complete history proof is in
`EXPLORATION_IMPLICIT_BOUND_MOVING_FRAME.md`.

## Pre-power bounds

Write Q=q^2, L=Q^8, N0=Q^6, H=hrow and

    P=Dword+Q*Xword+Q^2*Eword+Q^3*Zword+Q^7*(Bword+H).

The positive geometric witness satisfies 3lambda=L-1, so q>=2 and Q>=4.
The source equation

    r=(L-P)*(L-1)+2lambda>0

forces the integer P<=L. Its positive low term Dword then gives
Bword+H<Q, hence Bword<Q. Before any bit interpretation, the local
equations imply

    Cword=Bword/4,
    Xword+2Dword=Bword+Cword<5Q/4,
    Zword+2Eword=4Bword+Dword<37Q/8.

Thus each of Dword,Xword,Eword,Zword is less than 5Q, and their low part
is less than

    5Q*(1+Q+Q^2+Q^3)<(20/3)Q^4<Q^7.

Since Bword+H is an integer at most Q-1, this proves P<L strictly,
before Pell classification or Boolean decoding. There is no endpoint
P=L case to add to the periodic-mask lemma. It also gives

    r>L-1>N0, r<L^2=Q^16<N0^3, N0>=64.

Here N0 is mathematical notation; the certificate computes only
N0^2=Q^12. These are stronger than the required n<=r<2n^3 with n=N0.
The obsolete lower bound r>N0^2 is neither assumed nor needed.

## Retained index, exponential, and rounding hypotheses

The kernel uses U=wQ^12 and Y=sQ^12. Consequently

    E=UY>=Q^24>2r+1,
    a=Y(U+1)>Q^24>2r+1,
    4r/a<4/Q^8<1/2.

The first index congruence therefore has its needed positive residue
r+1<E. The positive interval and comparison Pfirst>A give the same
initial main index p>=r+2>=66 and c>A(A^2-1)^2. Hence the relaxed
auxiliary rank proof and the half-parameter index proof apply in their
original order. They recover p=2r+1; growth then isolates the first
index r+1. The lower ratio proves Y>=U^r before the first exponential
criterion is used. That criterion gives U=2^(2r+1), so q is a power
of two. The base-two tail and ratio-error estimates then prove
Q^12 divides binom(2r,r), exactly as in `BASE_TWO_PELL_90_PROOF.md`.
No second fixed-index Pell equation is retained or invoked.

The now-valid periodic mask proves P Boolean. The low-part bound <Q^7
isolates Bword+H as a Boolean word. In particular Bword<Q/3. The local
equations sharpen the bounds to Dword,Xword,Eword<Q and Zword<2Q.
Thus the three low fields are separated, and the whole normalized
Zword, including a possible digit at Q, is Boolean. The empty gap
between that word and the top field prevents interference.

For positive necessity the causal history proof supplies Boolean
fields and even Dword at the unit position; hence P and r are even.
One may widen the rows as needed, preserving the fixed endpoints and
finite run. The canonical periodic mask then gives the binomial
divisibility. Since N0<=r and N0 is a power of two, N0^2 divides
2^(2r+1), and every positive witness in the existing first-Pell
necessity proof is available. The history proof separately permits
the last physical output 4F to extend one position beyond a chosen
stored source width; this does not affect any Pell bound.

## Exact source and operation audit

The completed round42 checker was read in full and independently
rerun without rewriting its receipt. It passes 82 primitives:
45 multiplications and 37 additions/subtractions, with 30 positive
unknowns and 20 source equations. The retained kernel has exactly
43 instructions. The outer change removes ABC and bound, removes
alpha and its source equation, and changes only pack0's multiplier
from Q to the already-computed Q4.

An independent transformation of the preceding round41 schedule
obtained the same 82 instructions and expanded all 20 residuals
exactly. After the source deletion the auxiliary norm prerequisite
is source 17, and its triangular correction belongs to source 18;
those indices and signs agree with round42. The deleted alpha does
not survive in any source polynomial. The direct power identity
n2=q^24 remains exact. Separate finite checks at q=2,...,100
corroborated the new low-part and preliminary scale inequalities;
the general inequalities above are the proof.
