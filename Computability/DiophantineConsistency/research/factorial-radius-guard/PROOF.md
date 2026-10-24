# One factorial lower bound replaces two index guards

This ordinary research argument is relative to the frozen77-guard domain in
`research/paired-index-guards`. It keeps that domain's V>=1 and product
of the t/k122 slacks, but replaces its two guards at raw711 and raw779
(the K and shifted-K index slacks) by one guard raw87-2>=0. This gives76
predicates before any projection. No new projected count, quartic, Lean
or internal-ZFC theorem is claimed here. Source rows and indices are exactly
those pinned in `paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json`.

The other75 predicates of the77 system are kept; replace the two
selected predicates by one, giving76 total. Equivalently, of the original78
scalar guards remove raw674,711,779,861,1214 and add the three predicates
V/raw656>=1, raw674*raw861>=0, and f/raw87>=2. Every semantic-prefix
premise and base0.T remain.

## 1. The unchanged early bounds

The complete prefix certificate still gives all643 prefix signs, t>=1,
K/raw86>=3, nonnegative N/raw93, raw59, raw113, raw94, raw95, raw534,
raw535, raw536 and raw537. The retained bootstrap gives A>W^W>W²,
where all actual n,k,m in the21 power calls satisfy 0<=n,k,m<W and
all15 seed indices are positive. V>=1 first gives every seed Y nonzero
and recovers raw1214>=0 exactly as in the77 proof. Thus abs(U)>=A,
abs(B)>=3, Y²|V and the signed comparison-base interfaces remain valid.
None of these steps uses the two missing K/shifted-K slacks.

Use the exact abbreviations from the local factorial proof:

    f=raw87>=2, d=raw89=f*K², s=raw90=K+d,
    N=raw93, C=raw91, b=raw530, M=raw129.

The original cuts give

    M=1+f*(raw59+1)>=f+1,
    b=M*(1+N+raw113)>=(f+1)*(N+1)>=3,
    C=raw94+raw95+1>=1,
    f*C=N+raw95, 0<=raw95<C.

Consequently f=ceil(N/C). This ceiling relation and positivity are literal
row consequences before either missing index has been interpreted.

## 2. A seed without its index guard has an exact dichotomy

Consider either of the two seeds, with its positive index k<W and an
actual supporting call at a base 2<=n<W and output 0<=m<W. If abs(Y)>=2,
Pell classification gives a main index i>=2, hence

    abs(Y)>=psi_A(2)=2A>W>k.

Use abs(Y) as its natural numerical parameter; Y²|V gives B=1 modulo
4*abs(Y), and the original signed R congruence is unchanged modulo that
positive modulus. The already accepted signed comparison-base index theorem now has its
short-interval premise k<=abs(Y). It gives abs(X)=chi_k(A),
abs(Y)=psi_k(A), without an index-slack premise. The three wrong signs
would make T divide m*n^k+1, m*n^k-1 or m+n^k. Each has absolute value
strictly below T, by the unchanged frame and A>W^W. The first and third
are positive; the second cannot be zero because n>=2,k>=1. Thus the
actual X,Y are positive, and the call output is exactly n^k. The other
calls at this same pair have their intended powers by their unchanged
small-residue argument. The actual index slack is strictly positive.

If abs(Y)=1, the main norm gives abs(X)=A directly. Here the four possible
actual residues X-(A-n)Y are

    (X,Y)=( A, 1): n,
    (X,Y)=(-A, 1): -2A+n,
    (X,Y)=( A,-1):  2A-n,
    (X,Y)=(-A,-1): -n.

The actual modulus is T=2An-n²-1. Since n>=2 and n,m<W,

    T-(2A+n+m)
      =2A(n-1)-n²-n-m-1 >= 2A-W²>0.

Also 2A-n-m>0 and 0<m+n<T. Therefore the second and third residues
differ from m by a nonzero integer of absolute value below T; the fourth
would make 0<m+n<T divisible by T. They are impossible. For the first,
|m-n|<W<T forces m=n. Thus the only small-ordinate branch is exactly
X=A,Y=1 and exponent1 output at every positive supporting base. This
branch is not mislabeled as an intended k-power.

The K seed has base d+1>=2 in call1; its call6 base b>=3 is also positive.
The shifted seed has base b+1>=4 in call5. Hence the dichotomy applies to
both actual seeds. Let e be K or1 according as the K seed is large or
small, and let h be s or1 for the shifted seed. Precisely

    N=(d+1)^e, raw533=b^e, raw532=(b+1)^h.

In both branches the actual main coordinates have positive signs. These
statements interpret only the three actual calls1,6,5.

## 3. The digit equations exclude a collapsed shifted seed

Write a=raw534,u=raw535,v=raw536,z=raw537. The exact original rows are

    (b+1)^h=b^e*(C+b*a)+u,
    b^e=u+v+1, b=C+z+1.

All four auxiliary values are nonnegative, so 0<=u<b^e and 1<=C<b.
If h=1 and e=K>=3, then b+1<b^K. Euclidean division in the first row
forces C+b*a=0, contradicting C>=1. If h=1 and e=1, division of b+1 by b
forces C=1 (and a=0,u=1). But N=d+1 and f*C=N+raw95 then imply

    f>=d+1=f*K²+1>f,

impossible. Thus h=s: the shifted seed is large and its index slack
has been recovered, regardless of which K branch was present.

## 4. The factorial lower bound excludes a collapsed K seed

Suppose e=1. Then N=d+1, and the radix bound gives

    b>=(f+1)*(d+2)>=2d+4>K+d=s,

because d=fK²>=K. Reducing the exact binomial expansion modulo b² gives

    (b+1)^s = 1+s*b modulo b².

All terms of degree at least2 are multiples of b²; no bound on those
coefficients is needed. The literal remainder bound 0<=u<b first gives
u=1. The literal digit bound 0<=C<b and 0<s<b then give C=s=K+d.
As K>=3,

    0<N=d+1<K+d=C,

so the literal ceiling equation gives f=ceil(N/C)=1, contradicting f>=2.
Therefore e=K too. Both missing seed coordinates are the positive Pell
coordinates at their actual indices; each actual ordinate is at least2A
and exceeds its index. Both omitted slacks are strictly positive.

## 5. Both directions and the exact domain boundary

Starting from a new76-guard zero, regenerate the two old K/shifted-K guard
triples at the unchanged body tuple. All other75 predicates of the77
system were retained, so this gives a77-guard zero. Its complete ordinary
proof now recovers the t/k122 slacks, the full old78 domain and its inherited
ordinary logical calibration. There is no circular appeal to that full
power semantics in Sections1–4.

Conversely, the77 proof's local factorial lemma, with its retained K and
shifted-K bounds, gives f=K!>=6. Thus every77-guard zero satisfies f-2>=0.
Keep all other guard triples and choose a fresh Legendre triple for f-2;
forget the two old index triples. This gives a76-guard zero. The body is
unchanged in both directions. The three-square guard for the affine value
f-2 is quadratic and needs no extra defining gate. Actual projected sizes
must be measured and independently checked; they do not follow by merely
subtracting three variables from a previous projection.
