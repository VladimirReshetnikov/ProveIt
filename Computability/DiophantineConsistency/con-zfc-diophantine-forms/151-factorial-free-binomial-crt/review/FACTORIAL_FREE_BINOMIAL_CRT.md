# Factorial-free arithmetic via a binomial CRT modulus

## Status and scope

This note proves a replacement for the *arithmetic source* used by the
Common Remainders direct C222 construction. It is not merely a change of
Turing machine. It removes the requirement that an unknown equal t! and
replaces both jobs of that factorial by two separate elementary arguments:

1. sufficiently large evaluation of products of linear label factors
   recovers exact Horn-rule balance;
2. a single binomial coefficient retains enough prime powers to decode
   every row, even though the consecutive factors need not be coprime.

The selected final variant uses an odd-square radix and H0=2+sum of the
nine actual representatives; it imposes no parity condition on x.

The local C222 rule polynomial, its literal majorants, normalized common
remainders, signed Pell frame, semantic anchor, strict K=x budget, and
C222/ZF/ZFC calibration are inherited. The changed front is specified
below. A concrete emitted quartic must still be checked against this
specification. No new variable count or end-to-end formalization is claimed
by this proof note alone.

## 1. The new front

Let t=16+h0^2 and let all final coordinates range over the integers. Keep
all original beta endpoint equations and the eighteen power-request slots,
but replace the old request V0=(F^2+1)^t by

  p0=2(t+1),       F=p0^t.                           (1)

The symbols for a variable power in this note denote the output of its
retained ordinary polynomial Pell certificate. No variable exponent is a
primitive of the final polynomial. Equation (1) reuses the existing
principal pair at index t; it requires no new principal index. Identify
the old F coordinate with this new power output globally, including every
source row, metadata occurrence and frame atom.

Delete the two factorial ceiling equations and their private witnesses,
and delete the old definition y=V0(V0-1). Introduce the two-coordinate
beta-scale certificate

  v_beta=(2w+1)^2,       y=F v_beta,                    (2)

and the one-coordinate radix certificate

  q=(2z+1)^2.                                         (3)

Both are ordinary quadratic graphs. They imply y>=F>0 and q>=1, but the
boundary y=F is not excluded by (2) alone; Section 5 supplies the essential
late zero-path contradiction. There is NO parity condition on x in the
final equation. The old exact-digit output slack need not have a sign
guard; if its row q=B+o+1 is retained, o is unrestricted until its eventual
sign is derived.

Retain the exact-binomial digit graph, now intended to represent

  R=F^2,  B=binom(R+t,t),  N=B^x,
  H0=2+sum(the nine actual CRT representatives),
  q=(B H0)^x.                                         (4)

Retain B dividing C0+R+1, where C0 is the actual index representative, not
its stored coordinate minus one. All range tests and the local polynomial
congruence still use N. The same four denominator groups are q^t,
q^(t+1), q^(y+1), q^x, normalized to M=q^x.

## 2. Signed power recovery and absence of circularity

The retained square frame bounds every actual base, exponent and output
atom in absolute value by W, with W>=258 and |A|>W^W. The signed anchor
and pooled errors orient both coordinates to X_k(A),Y_k(A) at every
signed requested index. This part uses only squares of atoms and retains
its validity after (1)-(3), provided the actual new atoms replace the old
ones in the frame.

For a nonzero signed base n, set T=2An-n^2-1. Then |T|>W^W+W and
T=-1 modulo n. The canonical power congruence gives m=n^k modulo T
when k>=0; the small absolute error forces equality. If k=-j<0, it gives
m*n^j=1 modulo T. The error has absolute value below W^W+1, so equality
holds; this is impossible if |n|>=2. For n=1 or -1, every signed exponent
is allowed but the output is exactly 1 or (-1)^k respectively. Thus
negative bases are handled without a positivity assumption, and n=0 is
explicitly excluded when this lemma is used.

The acyclic recovery order is as follows.

1. Since t>=16 and p0=2(t+1)>4, the t request in (1) gives the genuine
   positive F=p0^t>4^16=2^32. In particular F>=7 and y>=F>0.
2. Since q>=1, the numerator bases q+1>=2 force all actual CRT
   representatives to be nonnegative. Thus H0>=2. They also orient the
   derived label as a nonnegative exponent; the signed anchor had already
   excluded zero.
3. The raw row B*h_index=C0+F^2+1 excludes B=0. Consequently |B H0|>=2.
   The signed-base lemma applied to the request q=(B H0)^x forces x>=0
   and supplies that exact equality. This step does not assume B>0,
   q>1 or that x has either parity.
4. Exclude x=0 using the LAST endpoint first: the coefficient
   1+(t+1)y>1 cannot divide -1. Thus x>=1. The first endpoint
   x=F+1+(y+1)u0 and y>=F would give x<=F-y<=0 if u0<=-1, a
   contradiction. Hence x>=F+1. The last endpoint now gives ut>=1 and
   x>=2+(t+1)y. Hence x>=2 and

     q=|B H0|^x >= 2^x,       q>=4B^2,       |B|<=q/4.

   Positivity of q makes the absolute-value equality valid whether B
   initially has positive or negative sign. In particular q>1 now follows.
5. All powers at q and q+1 are exact at their genuine nonnegative values.
   All four low-digit denominators are positive, and their exponents are
   <=x. The normalized common remainder norm therefore implies
   |r_i|<q^(k_i)/2 as before. The N=B^x request may be left uninterpreted
   until B has been recovered as positive; the exact-binomial B digit
   uses no N, so this postponement creates no circularity.

No binomial or factorial interpretation is used in this order.

## 3. Authenticating the one binomial without a factorial ceiling

For m,t>=1 and 0<=j<=t, the elementary uniform bound is

  binom(m+t,j) <= (m+1)^t.

It follows by Pascal induction, treating the last coefficient using
product_(i=1)^t (1+m/i) <= (m+1)^t. Apply it with m=F^2 and write
V=(F^2+1)^t merely as proof notation. This V is not a retained witness.

For every integer F>=7, F^2+1<=2^(F-1): the base case is 50<=64,
and induction follows from
2(F^2+1)-((F+1)^2+1)=F^2-2F-1>0. Here F is enormously larger than 7.
Accordingly

  V <= 2^(t(F-1)),
  x >= 2+(t+1)F = tF+F+2,
  V/q <= 2^(-F-t-2).

In particular V/(q-1)<1/32. Each true low binomial remainder before
position t is below q^t/32. The normalized common-remainder norm selects
exactly that least nonnegative remainder, as in its existing proof.
The exact-digit row then gives

  B = binom(F^2+t,t) modulo q.

The binomial C=binom(F^2+t,t) satisfies 0<C<=V<q/32. The possibly
signed candidate B satisfies |B|<=q/4, so |B-C|<q. Their congruence is
therefore an exact equality, proving B=C>0 without any front sign guard
on B. In particular B>=2, and for t>=2 one has B>F^2+1. Only now interpret
N=B^x as a positive exact output.

The retained row B|(C0+F^2+1) also excludes C0=0. Hence C0>=1; the
needed H0>=2 was already known because its new constant is two.
Also the old output slack, if present, satisfies o=q-B-1>=0. No condition
that F=t! is asserted or required.

## 4. Binomial CRT lemma: all rows are detected

Let t>=1, let R be a positive integer with R>(t!)^2, and put

  B=binom(R+t,t).

For a prime p write e=v_p(B). Two facts suffice.

### 4.1 Every prime of B has a compatible row

Let v=max_(1<=i<=t) v_p(R+i). Legendre's formula gives

  e=sum_(j>=1) (floor((R+t)/p^j)-floor(R/p^j)-floor(t/p^j)).

Every summand is zero or one. Above j=v there is no interval multiple;
also p^j>t, since any t consecutive integers contain a multiple of p^j
if p^j<=t. Therefore those summands vanish, and e<=v.

For every p|B, choose an index i attaining v. Then p^e divides R+i.
This fact is used in completeness for EVERY prime of B, not only the
prime powers selected in the next paragraph.

### 4.2 Every row has an isolating prime power in B

Fix i in [1,t] and put a_p=v_p(t!). Because R+i>(t!)^2, there is a prime
p with v=v_p(R+i)>2a_p. Otherwise R+i would divide (t!)^2.

The inequality v>a_p implies p^v>t. For every j!=i in [1,t], therefore,

  v_p(R+j)=v_p(j-i).

Consequently, writing a=a_p and c=v_p((i-1)!(t-i)!),

  e=v_p(B)=v-a+c.

The quotient t!/((i-1)!(t-i)!)=t*binom(t-1,i-1) is an integer, so
0<=c<=a. Hence

  v-a <= e <= v,       e>a,       p^e>t,
  p^e divides R+i.                                    (5)

For p>t, a=0 and the same conclusions are immediate. These are precisely
the isolation and index-identification facts the old pairwise-coprime
reciprocal moduli provided. They do not require those moduli to exist as
integers.

### 4.3 Soundness of bounded row decoding

Let K=x, N=B^K. Suppose N|binom(C0,t), B|(C0+R+1), and the unchanged
column ranges N|binom(A_j,k_j) hold, with all upper arguments nonnegative.
For row i choose the prime power p^e from (5). The one-sided binomial
range lemma gives

  C0=s modulo p^(Ke),  0<=s<t.

Modulo p^e, the raw index row and (5) give s=i-1. Since p^e>t, this is
an exact equality. Every column has a residue in its specified bounded
interval modulo p^(Ke). The local congruence N|L(C0,A) gives
p^(Ke)|L(i-1,w). Its retained bound 0<=L<2^K<=p^(Ke) forces L=0.

The derived-label range is unchanged: its local value and its residue
are both less than 2^K, so the range modulo p^(Ke) gives the actual local
label bound <=t. Therefore every row is recovered.

### 4.4 Completeness, including non-isolating primes

Start with a valid bounded row tuple for each i in [1,t]. For each prime
p|B let e=v_p(B), choose i as in Section 4.1, and prescribe modulo p^(2Ke)

  C0=i-1,       A_j=the j-th local value of row i.

These prime-power moduli are pairwise coprime and multiply to B^(2K)=N^2.
Ordinary CRT supplies the representatives. The raw index congruence holds
because p^e|R+i for each selected i. The local congruence holds already
modulo p^(2Ke).

For any range lower index k<=K and canonical residue 0<=w<k, if the global
upper argument a<k then binom(a,k)=0. Otherwise the falling factorial
contains a factor a-w divisible by p^(2Ke); division by k! loses at most
v_p(k!)<=k-1<K<=Ke. Thus p^(Ke)|binom(a,k). The same argument applies to
the derived polynomial label, by polynomial congruence. Every range holds
at every prime of B. No leftover-prime gap remains.

## 5. Initial-state recovery and large evaluation

Before using the positive-accumulator product, the boundary y=F must be
excluded. Section 4 recovers genuine local rows without assuming a positive
initial state. Their beta equations and bounded remainders supply a sequence
S_0,...,S_t, with S_i<=y, and updates

  S_(i+1) W_(c_i)=S_i W_(p_i) W_(q_i),  W_j=1+jF>0.

If y=F, the first endpoint makes S_0=0 because F+1 equals the first
modulus y+1. The final endpoint nevertheless gives S_t=1, since its
modulus 1+(t+1)y is greater than one. Every update preserves zero in the
forward direction, a contradiction. Therefore y>F at every full zero.
Now F+1 is a proper first remainder, so S_0=F+1, S_t=1 and induction
makes every S_i positive. This universal zero-path argument is essential;
simply citing the parent's positive-initial-state proof would be invalid
at the standalone boundary allowed by (2).

For a Horn-flow certificate with exactly t rows, each conclusion and at
most two premises per row has a label j in [0,t]. Retain the weights

  W_j=1+jF,   W_0=1.

Multiplication of the positive accumulator updates gives

  product_(rows) W_conclusion
    = (1+F) product_(rows,premise slots) W_premise.      (6)

First show that the two sides have the same number of nonunit factors.
Let their counts be d_L and d_R, ignoring all zero labels because W_0=1.
The left count is at most t; the right may initially be as large as 2t+1.
If the counts differ, put d=min(d_L,d_R), so d<=t. The side with more
factors is at least (F+1)^(d+1), while the other is at most

  (1+tF)^d <= t^d(F+1)^d.

But F+1>t^t>=t^d, since F=[2(t+1)]^t. This is impossible. This argument
also covers d=0. Thus d_L=d_R<=t.

Each side is now an evaluation at z=F of a polynomial product of at most
t factors 1+jz. All coefficients are nonnegative and their sum, the value
at z=1, is at most (t+1)^t<F. Consequently every coefficient of the
difference has absolute value less than F. A nonzero polynomial with
such integer coefficients cannot vanish at F: divide by its lowest
nonzero power of z, then reduce its value modulo F. Thus (6) is an
identity of polynomials in z.

The nonconstant factors 1+jz for distinct positive j have distinct roots
-1/j and are irreducible over Q. Unique factorization recovers the exact
multiplicity balance at every positive label. The truth label contributes
the unit factor one, exactly as intended. The inherited one-conclusion
Horn closure argument then yields derivability of falsity. It is valid
for cyclic supplied rule multisets and repeated premises.

Conversely, expanding a finite proof tree from its root gives a positive
pending-multiset accumulator path with exactly these weights. Truth
padding reaches exactly t rows. No coprimality is required for this
completeness construction.

## 6. Budgets and canonical parity

The local majorant Rmaj=2+t+x+y+F satisfies Rmaj<2x because

  x-(2+t+y+F) >= t(y-1)-F >= (t-1)F-t > 0.

Also x>=F+1>2^32, so the retained E=2^23 estimate gives
L<Rmaj^E<(2x)^E<2^x. This needs no factorial identity. Every lower index is <=x, since the only ones are
t,t+1,y+1,x. The derived-label ledger h<=H0^ell, ell=2^22, still gives
carry-free coefficients because x> (t+1)F > ell(t+1). Thus the ordinary
range-remainder estimate H0^x/(q-1)<2/B^x<1/32 remains valid.

For canonical completeness, choose the padded horizon first, then F by
(1), and the actual positive accumulator path. Let O be the odd part of
t!. Choose an arbitrarily large odd number a_beta=O(2m+1), and set
v_beta=a_beta^2 and y=F v_beta. Because v_2(F)>=t>v_2(t!), y is an even
multiple of t!; choose m large enough that y>F and y exceeds every
accumulator. This factorial is used only in a finite existence proof for
the beta CRT; no unknown is asserted equal to a factorial.

The beta moduli 1+(i+1)y are pairwise coprime and odd. Choose a positive
EVEN beta code x by adding their odd product if necessary, and enlarge it
further in that parity-preserving class if needed. The canonical beta
quotients remain in [0,x), as their denominators are at least two. Only
afterward set K=x and N=B^x.

The factor two in p0=2(t+1) ensures B is odd. Indeed
v_2(R)=v_2(F^2)>=2t>log_2(t), so for every 1<=i<=t,
v_2(R+i)=v_2(i). Their product ratio B has valuation zero. Thus N^2 is odd.
The arithmetic CRT representatives can therefore be shifted by N^2 to
choose arbitrary parity. Choose every representative except the dominant
a to be even, and choose a odd. The existing dominant a construction
keeps 2N^2<=a<4N^2. In particular a has parity opposite to the schema
parameter b, yielding the required even semantic anchor h and its gap
over all other indices. Their sum is odd, so H0=2+sum(a_i) is odd.
Thus B H0 is odd, and the chosen even x makes q=(B H0)^x an odd square;
z=((B H0)^(x/2)-1)/2 supplies (3).

All fixed front indices are still below N^2. In particular B>=F^2+t
follows from the elementary binomial bound binom(n,k)>=n for
1<=k<=n-1; hence F^2+t<B^2<N^2. The other bounds follow from the endpoint
and N=B^x. The original signed squared cap, odd auxiliary Pell witnesses,
coordinate orientation and all normalized low remainders can consequently
be constructed with the same completeness arguments.

## 7. Result and exact boundary

The modified front, the retained polynomial local rule checker and range
circuits, and the unchanged Pell certificates have a simultaneous integer
solution if and only if the finite C222 calculus has a refutation. The
forward direction uses Sections 2-6. The reverse direction constructs all
witnesses in the order in Section 6. With the retained ordinary logical
calibration, this proves in ZFC the requested equivalence between
nonsolvability of the resulting fixed polynomial and Con(ZFC).

The conceptual result is the removal of factorial authenticity. The
binomial B itself and the low-digit arithmetic remain present. This note
claims neither a global simplicity minimum nor a new proof-assistant
endpoint. Exact finite polynomials, operation counts, variable counts and
coefficient heights require the separate concrete construction and audit.
