# Review of the H1868 saturated radical and D-register composition

The new nine-positive argument appears sound with one harmless numerical
typo corrected below. The954-operation circuit is an exact polynomial
rewrite of its1086-operation parent, with no new semantic hypothesis.
This review uses ordinary mathematics and Python exact finite certificates;
no Lean was edited or invoked.

## The correct source and its bounds

The H1868 prefix is the31-positive-coordinate,22-quadratic-row `gapN86`
source with its whole original31 coefficient tuple. It is not the compact54
source used by the434-operation degree1628768 equation. The retained
coordinate/row transformations are P_old=P+eta+zeta,N_old=N+1 and the two
specified invertible row changes. Their source-existence interpretation is
inherited from the identified source/compiler proof.

The finite audit reconstructs all22 target identities, including all absent
monomials, from20466 convolution interactions. It confirms31 positive
distinct weights with maximum116,22 distinct targets with maximum1836,
and kernel degrees1408,1727,1636. Their literal leading coefficients are
-6,2,1. All original31 port bytes are authenticated, and the coefficient
box implies |coefficient|<M=2^2134927. No coefficient from compact54 or
the BFS-renamed page is used.

Write B=4096*M*b^2, u=ell+g and epsilon=M/(B-1), for positive b,g.
The leading coefficient1 gives
D2(B)>(1-epsilon)B^1636. The lower kernels satisfy
|D1(B)|<epsilon*B^1728 and |D0(B)|<epsilon*B^1409.
Since u>=B^116, the negative terms relative to B^1636*u^2 are bounded by
epsilon*B^-24 and epsilon*B^-459. Thus

```
Gs > (1-3*epsilon)*B^1636*u^2 > 0,
```

because epsilon<=1/4095. This is unconditional in g, before any binary-digit
or source-zero assumption. The low mask is nonnegative because b<=B and its
31 positions are distinct within0..116. Hence Sc,Tc>=0, and

```
R=(L-1)*(Sc+Tc+1)+Tc,
L=2*b*B^1986
```

gives R>=8 and R>=b on every positive ambient assignment. The positive
threshold N=2^16012032*B^1055 is also at least8 and b.

After the ratio margin yields g<4*b*B^116, one has u<6*b*B^116. Direct
geometric bounds give2*Gs/B^1869<86*M*b^2/(B-1)<1/32. The targets lie
below B^1837, so Sc+Tc<B^1986<L. These estimates provide the needed
packing ranges before digit decoding. The maximum signed convolution
coefficient is at most(31^2+31+1)*M*b^2=993*M*b^2<B/4. Thus the identified
sparse signed-carry theorem has its required coefficient and gap bounds.
Its unbounded semantic statement remains an inherited mathematical lemma.

For completeness a fixed positive source zero packs at arbitrarily large
binary b with g<b*B^116. The all-one tuple is not a zero: row5 is identically1
in all four coefficient ports. This ensures g>0, rather than silently
assuming positivity of a packed all-zero offset vector.

## A typo in the expanded population identity

For b=2^k, put kappa=2134939 and v=kappa+2k. The actual definitions give

```
u_L = 1+k+1986*v,
pop(Tc) = 139*v-31*k-22,
u_L+pop(Tc) = 2125*kappa+4220*k-21.
```

The retained H1868 audit and section text print4210 in the last expression.
It should be4220. The delivered threshold is correct:

```
2*log2(N) = 2*16012032+2110*v
          = 2125*kappa+4220*k-21,
```

because15*kappa-21=32024064. The new verifier compares both affine
coefficients symbolically; it does not infer a universal identity from a
finite sample of k values. The factor2 in L and absence of an extra b in N
are necessary for these definitions. They are preserved in the literal DAG.

Consequently pop(R)=u_L+pop(Tc)-tau, with tau>=0 and tau=0 exactly at
bitwise disjointness, gives the intended N^2 central-binomial threshold.
At b=1 the low mask is B^117-1, which excludes any positive g below B^117;
there is no exceptional false positive at that endpoint.

## Saturation, range recovery and integrality

The modified norm is the same one reviewed in
`../saturated-nine/PEER_REVIEW.md`:

```
D=1+(A^2-1)C^2,
F=1+(A^2-1)D(i*J*C^2)^2,
G=A+F(CD+1-A),
H=C+F(B1+(j-1)C),
I=1+(G^2-1)H^2.
```

Its pairwise-coprime factors recover D,F,I as integer squares. The rank
argument gives C|m even when C is even. The finite-period construction or
the old-witness transport i_new=sqrt(D)*i_old supplies completeness without
requiring sqrt(D)|i on every new certificate. Dividing an arbitrary new i
to reconstruct an old witness would be invalid; the ordinary proof instead
reconstructs fresh old witnesses once C=psi_A(B1) is known.

The new report also states a broader version for odd B1 and A>=2, using
psi_A(n)=n modulo2 to exclude the negative index branch. In the actual
nine-positive composition, A>=33280,1<B1<A and J>=A already hold.
After recovering C>B1 from the margin, the stronger A>=3 theorem and its
direct signed-index folding proof from the earlier review apply. Thus this
endpoint does not depend on an unexamined A=2 exception. The cited
[Sun Lemma2.2](https://arxiv.org/html/2609.01594v1) also supplies the stated
general integral index congruence under the established m>3 condition.

The cheap local majorant has unconditional positive defect. The corrected
radical majorant below likewise holds before a final zero. Since E0>0,
real factorization of the norm first forces m>0. Only then is the margin
used to obtain C>K and C>B1+W1, and to separate the two radicands. Their
signed rational sum is nonzero, so the isolation identity makes each root
rational and hence integral. J|Q follows after this recovery. The argument
does not assume the very Pell range that it needs to establish.

## The correct radical correction and exact degree

The uncorrected333-term polynomial P has the same formal-square-root role
as before, but the new correction is

```
Pplus = P + 297874*C^24*i^6*Z,
sigma = 1024*C^5*i,
Z = B1+(j-1)*C.
```

The corrected defect Pplus^2-sigma^2*DFI has36309 strictly positive
coefficients after A->A+3,C->C+1,i->i+1,Z->Z+1. Its positive constant is
8341416066461366340. The shifted positive branch of P is also checked.
Therefore Pplus>sigma*sqrt(DFI)>0 throughout the required range. The old
H2082 correction2^20 is not substituted into this candidate. Both are
valid bounds, but these are distinct parent polynomials and certificates.

The complete shifted certificate, not samples or an asymptotic estimate,
justifies the inequality. Dividing a recovered integral root of
sigma^2*DFI by positive sigma yields a rational root of the integer DFI,
which is integral. Completeness has positive n because this majorant
exceeds4D and the inherited correction W1^2+Q/J is below2D.

The leading kernel coefficient1 gives Gsource~B^1868. Consequently
R~4*b*B^3971 and deg(R)=7943, while deg(N)=2110 and deg(A)=16385.
At weights(16385,1,1,7943), the unique local heads are

```
Pplus: 2^20*A^18*C^24*i^6*Z,
defect: 624687054848*A^18*C^48*i^12*Z^2.
```

Their positive coefficients survive the actual fixed tuple. The exact
cancellation-resolved outer identity has four contribution degrees
950392,999518,991546,753714. Only the second is largest. This establishes
both the upper bound and degree attainment for the specialized equation.

## Exact954-gate composition

Replace A^2*C^2 by D+C^2-1 until the A exponent is at most1. Termination
follows because each step lowers that exponent. The333 original monomials
collect to263 in A,C,D,i,Z. The chosen Horner evaluation uses only the
already computed D. It does not add a variable, a source constraint or a
majorant assumption.

The checker independently normalizes the actual original and new majorant
DAGs at the five registers, substitutes D=A^2*C^2-C^2+1, and obtains the
same333-term polynomial. Every other retained gate is identical after its
operand remap. All new nodes are covered by those identities. Induction on
the old topological order proves the full outputs equal over every
commutative ring, hence on the complete positive domain. A changed final
majorant operation is rejected by this exact proof.

In addition to that rewrite certificate, the original1086-gate parent is
bound exactly to all stated source, ratio, Pell and norm formulas. Each
kernel, ell, target sum and full333-term majorant is normalized exactly;
small-register identities are checked at earlier independent cuts. No
modular samples are used to justify the transcription. The independent
source auditor checks all22 extraction identities and the full radical
defect and degree certificates. All12 signed fixed leaves are regenerated
from the complete original31 tuple and checked byte for byte.

The ordinary source/native/refutation interpretation and its unfinished
internal-ZFC formalization remain inherited. This circuit identity and the
finite audits neither assert Con(ZFC) nor prove unsolvability independently.
