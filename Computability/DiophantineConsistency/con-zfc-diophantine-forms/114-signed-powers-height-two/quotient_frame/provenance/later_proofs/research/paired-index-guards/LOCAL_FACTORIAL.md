# The retained K/shifted-K seeds suffice to recover factorial0

This closes the local source obligation in README Section4. It is an
ordinary arithmetic proof about the exact original rows, using only three
actual power calls. The unchanged bootstrap, frame and signed-index
interfaces are those of `research/main-root-and-modulus-signs/README.md`
Sections1–5 and `research/comparison-base-sign/README.md` Sections1–2.
Their source and proof hashes are retained in the local certificate. It does not invoke all21 power meanings or either of
the index guards being recovered. No new projected equation/count or
Lean/internal-ZFC theorem is claimed.

## 1. Early hypotheses, without the two missing index guards

The proposed domain retains all61 semantic-prefix guards and base0.T.
The accepted prefix proof therefore gives all643 prefix values
nonnegative, t>=1, A>=2 and A>W^W as before. Its proof uses only the
unchanged scalar-prefix premises; neither missing index slack nor the
old product-factor guard is used. The new V-1 guard gives V>=1.
In the exact row

    V=(product over all15 seeds of Y^2)*(raw1214+1),

every Y is consequently nonzero. The squared product is a positive
integer, so raw1214+1 is a positive integer and raw1214>=0. This recovers
the old product-factor sign pointwise before any signed-index theorem.

Keep the two slacks for K/raw86 and Nshift/raw90. They give Y_K>=K>0
and Y_shift>=Nshift>0. The common unit, positive V and their squared
divisibilities satisfy the already accepted signed comparison-base index
criterion for these two seeds only. Thus their main abscissae have
absolute values chi_K(A) and chi_Nshift(A), and their positive ordinates
are the corresponding psi coordinates. This does not require the
t/raw4 or k122/raw122 slack to be natural. The comparison base remains
possibly negative; its B=1 exception is excluded using abs(U)>=A and
U dividing A-1, exactly as in the accepted78-guard proof.

For a call at one of these two seeds with positive base n, the actual
modulus satisfies T=2An-n^2-1>=A. Its source row is
X-(A-n)Y-m=T*h. If X were negative, the Pell recurrence and norm imply
T dividing m*n^k+1. The frame bounds give
1<=m*n^k+1<=W^W<A<=T, contradiction. Hence X is positive. The usual
Pell residue gives m=n^k modulo T; both nonnegative values are below T,
so m=n^k exactly. This orientation uses n>=1, not n>=2.

The literal constructors give raw63=t+x+y+M0+2>=3 and23 successive
squares give K=raw86>=3. No parity of K is assumed.

## 2. Exactly three calls, and a strictly larger radix

Put f=raw87, d=raw89, C=raw91, N=raw93, M=raw129 and b=raw530.
The exact source definitions are

    d=f*K^2,
    Nshift=raw90=K+d,
    raw92=d+1,
    M=1+f*(raw59+1),
    b=M*(1+N+raw113), raw531=b+1.

The prefix already proves f>=0,M>=1,raw113>=0. First apply the retained
K pair to **call1** (base/raw92,exponent/raw86,output/raw93). It gives

    N=(d+1)^K>=1.

The exact factorial ceiling/remainder ideals are

    f*C=N+s, C=r+s+1,
    r=raw94>=0, s=raw95>=0.

Thus C>=1 and f>=1. In particular d=fK^2>=K. Also
b=M*(1+N+raw113)>=N+1>N, without any intended meaning of raw113.
Now the same K pair applied to **call6**, and the retained shifted pair
applied to **call5**, give

    raw533=b^K,
    raw532=(b+1)^(K+d).

Their bases are positive actual frame arguments. These are the only
three interpreted calls:1,6,5. No call at the unguarded t or k122
index has been interpreted.

## 3. The literal quadratic rows extract the binomial coefficient

For h=raw534,u=raw535,v=raw536,z=raw537, all nonnegative by the unchanged
semantic prefix, the complete choose0 source cuts are

    raw532=raw533*(C+b*h)+u,
    raw533=u+v+1,
    b=C+z+1.

Consequently0<=u<b^K and0<=C<b. These are both divisions' actual
remainder/digit bounds, not desired meanings assigned to the witnesses.

Let a_j=binom(K+d,j). Since d>=K and0<=j<=K, the binomial coefficients
are nondecreasing up to K, so a_j<=a_K. Furthermore

    a_K=product_(i=1..K) (d+i)/i <= (d+1)^K=N<b,

because (d+i)/i=1+d/i<=d+1. Thus every coefficient a_j for j<=K is a
valid base-b digit. The exact binomial expansion splits as

    (b+1)^(K+d)=L+a_K*b^K+b^(K+1)*H,
    L=sum_(j=0..K-1) a_j*b^j, 0<=L<b^K, H>=0.

No bound on coefficients above K is needed. Each such term is already
a multiple of b^(K+1). Comparing the two Euclidean remainders modulo
b^K gives u=L and C+b*h=a_K+b*H. Comparing modulo b, with both
C,a_K in[0,b), gives

    C=binom(K+d,K).

There is no hidden carry from the lower coefficients: their entire sum
is at most(b-1)*sum_(j<K)b^j=b^K-1. No other power, factorial, CRT or
source-checker semantics occurs in this extraction.

## 4. The self-referential radius has exactly one factorial solution

Here is the needed elementary lemma. For K>=2,f>=1,d=f*K^2, put
C=binom(K+d,K) and N=(d+1)^K. If f=ceil(N/C), then f=K!.

Let m=K!. The exact rational product is

    N/C=m*product_(j=1..K) (d+1)/(d+j)
       =m*product_(j=1..K) [1-(j-1)/(d+j)].

Every factor lies in(0,1]. Their omitted fractions have sum strictly
less than

    K(K-1)/(2d)=(K-1)/(2fK)<1/(2f).

For numbers0<=a_j<=1, induction gives product(1-a_j)>=1-sum(a_j).
Therefore

    m*(1-1/(2f)) < N/C <= m.

The ceiling equation implies N/C<=f and f<=m. If1<=f<m, the integer
inequality f*(m-f)>=m-1 follows from
(f-1)*(m-f-1)>=0. Thus

    2f*(m-f)>=2(m-1)>=m,
    m*(1-1/(2f))>=f,

contradicting the strict lower bound. Hence f=m. This also verifies the
boundary K=2,f=1 without a non-strictness loophole. At the actual K>=3,
f=K! is even.

In the source, f*C=N+s and C=r+s+1 imply0<=s<C, so
f-1<N/C<=f. This is precisely f=ceil(N/C), not an extra assumption.
The preceding sections therefore prove **raw87=raw86!** using only
the retained K/shifted-K seeds and calls1,5,6.

## 5. Parity and the two missing index guards

The even f makes base/raw103=1+(t+1)f odd. Its actual modulus is even.
Reducing the main t-seed norm modulo2 gives
X_t-(A-1)Y_t=1 modulo2. The actual call2 row, without interpreting
that call's power, gives raw104=X_t-(A-base103)Y_t=1 modulo2.
Hence k122=t+raw104+2 and t have opposite parity. This uses neither
missing slack and no sign of either t-seed coordinate.

For the even positive index, V>0 already excludes a zero ordinate.
If abs(Y)=1, its main Pell index is1. Write abs(U)=chi_j(A)
with j>=1, and classify the comparison norm at abs(B). After replacing
the numerical S by sign(X)*S, its abscissa congruence and the signed-B
half-period argument give h=plus or minus1 modulo2j. Thus h is odd.
The actual R congruence modulo4*abs(Y)=4 gives h=plus or minus k
modulo4, hence h even. This contradiction treats the small ordinate
without assuming k<=abs(Y). Therefore abs(Y)>=2. Pell
classification then gives abs(Y)>=2A>W>k, supplying the missing short
interval hypothesis of the signed index theorem. It follows that
abs(X)=chi_k(A),abs(Y)=psi_k(A).

The supporting base is at least2: t uses call0 with t+1>=2, and k122
uses call9 with b+1>=2. The same exact small residues exclude all three
unwanted X/Y sign combinations. They respectively make T divide
m*n^k+1,m*n^k-1 or m+n^k; the first/third are positive below T, and
the second can be0 only if m*n^k=1, impossible for n>=2. Therefore
X,Y are positive for this even index and Y>=2A>W>k. Its original
slack Y-k is strictly positive.

The new guard on the product of the two actual slacks now forces the
other slack to be nonnegative. Both missing original index guards and
the original raw1214 guard have been recovered pointwise at the same
body tuple. Keep every other guard triple and choose three fresh
triples for those original values to reach the accepted old system.
Conversely any old zero has V>=1 and nonnegative old slacks, so the
two new predicates have fresh Legendre witnesses. Thus the proposed
domain replacement has the same integer-zero existence, before any
projection or inherited logical calibration.

## 6. Exact finite source binding and limits

The local certificate and audit collect every coefficient of the
radius/shift/radix, choose0 digit, remainder-bound, digit-bound and
factorial-ceiling cuts from the original rows. They bind calls1,5,6
to exactly the retained K and shifted-K seed pairs, and check the
complete unchanged prefix dependency boundary and new product/sign
premises. They also bind all five norm/congruence/slack cuts for each
of the two missing-index seeds, plus the exact later calls0 and9, so
the parity-based conclusion addresses those actual original rows. Integer diagnostics include low-digit uniqueness, factorial
fixed-point bounds and rejected corruptions. They are diagnostics;
the unbounded proofs are Sections1–5. No whole21-power theorem is
assumed, and no projected equation, coefficient census or Lean theorem
is claimed by this research packet.
