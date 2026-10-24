# Independent mathematical review: signed terminal outputs

Reviewed against ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`.
This note reviews the proposed change to the 75-predicate direct C222
integer system. It does not claim that finite testing proves the source
calibration, and it does not itself certify a completed projected artifact.

## Exact changed interface

The proposed radius is

\[
W=2+\sum_{a\in\mathcal A\setminus\mathcal M}a+
\sum_{m\in\mathcal M}m^2,
\]

where the old 43 power-argument atoms are \(\mathcal A\), and the nine
signed outputs are raw546,573,583,591,599,607,617,625,635. The dropped
scalar sign guards are raw548,575,584,592,600,609,618,627,636. All other
source rows and predicates are retained; the old frame summation gates
may remain as definitional dead wires. The sole changed source row is
1176, `shared.frame_definition`.

An independent exact-row audit has verified the original signed prefix
identities and filtered their usable nonnegative monomial deductions
without any of the nine omitted guards. Every one of the other 34 frame
atoms is still nonnegative. Every selected power has base raw531 at least
2 and positive exponent. Its individual index slack is retained. The
recovered raw93>=2 proof uses only raw87>=2,raw94>=0,raw95>=0, and must
precede prefix interpretation exactly as in the frozen 75-predicate proof.

The selected powers and retained index-slack coordinates are:

| Power call | Output | Exponent | Index slack |
|---:|---:|---:|---:|
| 7 | 546 | 110 | 825 |
| 10 | 573 | 44 | 891 |
| 12 | 583 | 46 | 934 |
| 13 | 591 | 48 | 964 |
| 14 | 599 | 50 | 994 |
| 15 | 607 | 52 | 1024 |
| 17 | 617 | 54 | 1084 |
| 18 | 625 | 56 | 1114 |
| 20 | 635 | 58 | 1174 |

## Signed power lemma

Let W,A,n,k,m be integers with W>=4, A>W^W, 2<=n<W,
1<=k<W and |m|<W. Put

\[
T=2An-n^2-1.
\]

Assume Y=psi_A(k)>0, X is either chi_A(k) or its negative, and

\[
T\mid X-(A-n)Y-m.
\]

Then X=chi_A(k) and m=n^k.

First T>A, because

\[
T-A=(2n-1)A-n^2-1>A-(W-1)^2-1>0.
\]

Let x=chi_A(k), y=psi_A(k), p=x-(A-n)y and q=x+(A-n)y.
The Pell norm gives

\[
pq=1+Ty^2,
\]

and the elementary Pell recurrence gives p=n^k modulo T. In the
negative-X case the actual power row says m=-q modulo T, so

\[
T\mid mn^k+1.
\]

This integer cannot be zero: n^k>=2 cannot divide -1. Moreover

\[
|mn^k+1|\le (W-1)^W+1<W^W<T.
\]

The strict middle inequality holds for W>=2 by the binomial expansion
of ((W-1)+1)^W. This contradiction excludes the negative-X case even
though m was initially allowed to be negative.

In the positive-X case, T divides m-n^k. The inequality

\[
|m-n^k|\le (W-1)+(W-1)^{W-1}<W^W<T
\]

forces m=n^k. The condition n>=2 is essential: for n=1 the signed
pair X=-chi_A(k),Y=psi_A(k) admits m=-1 modulo T; the product
mn^k+1 then vanishes. None of the nine selected calls has base1.

## Bootstrap and ordering

The modified radius guarantees |m|<W for every selected output because
m^2<=W-2. The other frame atoms obey 0<=a<=W-2. The unchanged base0
modulus guard gives A>=2. Its proof uses no selected output. The unchanged
bootstrap Pell row then excludes a zero bootstrap ordinate, gives a
positive multiple of W as the bootstrap index, and implies A>W^W.

The predicates V>=1 and the exact common-unit norm give |U|>=A. The
comparison-base constructor and congruence exclude B=1 and yield |B|>=3,
without a positivity assumption on the omitted q4 coordinate. For each
of the nine selected seeds, its retained index slack gives Y>=k>=1.
The inherited signed-comparison index theorem therefore supplies exactly
Y=psi_A(k), |X|=chi_A(k) for these seeds. It need not interpret any
unguarded seed first. The signed power lemma above then applies to all
nine calls simultaneously, before the missing prefix signs are restored.

## Restoring the omitted quotient signs

For each of the eight range calls, the original row identities have form

\[
m=M Lq+r,\qquad L=r+s+1,
\]

with M>=1 and r,s>=0 already certified. Hence L>=1 and 0<=r<L.
If q<=-1, the first identity gives m<=-ML+r<0, contradicting m=n^k>0.
Thus q>=0.

For the extra exact-binomial call7, the source has

\[
m=L(C+bq)+r,\quad L=r+s+1,\quad b=C+z+1,
\]

where C,r,s,z>=0 and L>=1, b>=1. If q<=-1, then C+bq<=C-b<=-1,
so again m<=-L+r<0. Thus raw548=q>=0. This is why a ninth guard can
be removed with the same signed-output mechanism. The other exact-binomial
high quotients raw534/raw561 are deliberately retained: their power seeds
participate in the more delicate missing-index bootstrap, so the same
argument cannot simply be invoked at the earlier stage.

## Existence maps must rebuild the arithmetic frame

Changing W changes the bootstrap and shared Pell parameters. It is not a
pointwise deletion of nine guards on an unchanged source tuple. The
unbounded proof must therefore make the following distinction explicit.

Soundness: recover the nine signs as above, then reuse the frozen
75-predicate arithmetic reasoning with the established magnitude bounds
and bootstrap conclusions. Its local factorial and paired-index stages
now have all their required prefix premises. This yields all genuine
semantic power values and the calibrated finite refutation. Alternatively,
a new literal old-radius tuple may be rebuilt from those values.

Completeness: from a calibrated genuine arithmetic witness, retain its
semantic data and true terminal powers, calculate the new W, and regenerate
A=chi_(W+1)(W), its bootstrap ordinate, all main index pairs, a common
unit and comparison pair by the finite-period construction, and all power
quotients. All arguments of the power requests were fixed before W was
chosen. This ordered reconstruction is finite and has no self-dependence
through private Pell coordinates. The new guards are a subset of the
old ones and have fresh three-square witnesses.

No claim that old and new private tuples, zero sets, or full polynomials
are pointwise equal is justified. The intended statement is equivalence
of existence of integer zeros. This is sufficient for the Con(ZFC)
endpoint once composed with the original ordinary C222 calibration.
