# Independent review of the 27-integer weighted-root construction

## Verdict and scope

I reviewed `INTEGER27_PROOF.md` and `build_integer27.py` against the pinned
`14-integer29/proofs/signed_domain_proof.md` and the pinned
`09-combined13/arithmetic/polynomial13_84.json` at
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

**No new algebraic, domain, denominator, parity, or degree gap was found.**
The equation has 27 unrestricted integer inputs, 139 binary arithmetic
operations (74 multiplications and 65 additions/subtractions), and exact
total degree 1116.

This is a mathematical review of a reduction relative to the inherited
signed compiler theorem. It is not a new Lean/Rocq verification or an
independent rebuild of the native compiler or K215 calibration. Transfer
to the new complete pruned-T4 coefficient tuple relies on the separately
supplied compiler proof, including its canonical parity/padding argument.

## 1. Unit signs and signed h

The unit argument is valid over the unrestricted integers. The main norm
cannot be minus one modulo four because Delta is zero or three modulo
four. The root resultant is a square modulo four, so its guard cannot be
minus one. The remaining outer units must therefore have one common sign.

The zero square scale is excluded before any positive-X estimate is used:
when w=0, reduction of the main norm modulo H gives 0=1 modulo H, with
H>1. Thus w>0. The inherited transport estimate now gives E>R+2.
From k=R+epsilon+hE>0 it follows that h>=0; assuming h<=-1 would give
k<=R+1-E<0. Hence R<=k+1<=2k. No hidden positivity assumption on h is
needed in the later denominator proof.

## 2. Positivity of the denominator C

For Y>=4 the numerical inequality

    Y^4 > 8((Y+1)^2+4)

is valid (already 256>232 at Y=4, and the difference increases). Combined
with c<k(Y+1) and R<=2k it yields A>8(c^2+R^2). The estimates

    (D+v^2)^2>=4Dv^2,
    (D+v^2)^2>=D^2,
    (c+RD)^2<=2D^2(c^2+R^2)

are independent of the sign of T. The chosen doubled weight only
strengthens them. They give AM^2>2(Dv^2+Z^2), and hence
dAM^2>e+1. Therefore C=d(t^2+M^2A)-e>0 even for signed t and T.
The odd substitution t=2v0+1 separately guarantees t is nonzero.

## 3. The T=0 exceptional branch

The proof correctly handles this branch instead of dividing by T. At T=0,
the resultant gives C^2=4d^2t^2M^2A. Thus the rational number
tau=C/(2dtM) has integral square A and is an integer. Then y=t-Mtau
is an integer, and direct expansion gives

    (Q-1)y^2=QZ^2-1.

The estimate 1<Z<Q is sound: Delta>R follows from a>R+2, and

    Q-Z=(Delta-R)D-Delta-c
       >=D-Delta-c
       >=1+Delta(c^4-1)-c>0.

Here c>=2 and |i|>=1, the latter supplied by the odd affine substitution.
For integers 1<Z<Q, the auxiliary equation is impossible: it would give

    0<y^2-Z^2=(Z^2-1)/(Q-1)<Z,

whereas a positive difference of these integer squares is at least 2Z+1.
Consequently B=2QvZ is nonzero on every zero of the proposed polynomial.

## 4. Rational root recovery and the inherited signed theorem

All denominators in the displayed reconstruction are now nonzero.
The identities

    f=-U/(2CB),
    tau=(C+Bf)/(2dtM),
    y=t-Mtau

give f^2=D and tau^2=A. The elementary rational-square-root lemma makes
both f and tau integers; the last formula makes y an integer. Expansion
then yields

    d y^2=e-Bf=Q(vf-Z)^2-1.

Since f^2=D, the expression vf-Z is exactly
c(Tf-1)-Rf^2. Thus the normalized strong equation and the original
auxiliary equation are restored exactly, without a rational-root
shortcut for a nonmonic quadratic.

The cited normalized theorem in `14-integer29` requires precisely seven
positive coordinates, odd i and square w, and allows arbitrary integer
h,T,gamma,f,tau,y. These are exactly the recovered hypotheses. Its
signed-gamma and signed-quotient arguments are therefore applicable; a
positive-only theorem is not being applied to signed recovered roots.

## 5. Odd t completeness

The inherited canonical witness uses odd i and square w. Its final rank
R is odd, and the canonical auxiliary coordinate is y=psi_rho(R).
The Pell recurrence reduced modulo two gives psi_rho(n)=n modulo two
for every integer rho, so y is odd. (The proof's additional observation
that rho itself is odd is true but is not needed for this parity step.)

The weight M=2(D+v^2) is even. Therefore t=M tau+y is odd and has an
unrestricted affine representation 2v0+1. This proves existence of the
required odd t witness, rather than incorrectly claiming every original
root sum is odd. The seven independent positive-surjection substitutions
then give exactly 7*3+6=27 integer coordinates. Their surjectivity proof
using the three-square theorem is correct.

## 6. Circuit correspondence and exact degree

The vendored `parent_polynomial13_84.json` has exactly the same arithmetic
source and witness ports as the pinned repository's 84-operation packet.
The new builder makes precisely the stated changes: seven positive
surjections, affine odd i and t, square w, and the single doubling gate
for M. Its ledger is consistent with 84+49+5+1=139 operations.

The degree computation is also correct. In particular, expansion of the
main norm cancels the degree-44 terms and leaves the unique degree-35
leader 2ac gamma H. The index and transport degrees are 13 and 4.
For the resultant chain, the degrees are

    A:44, Q:90, D:66, v:11, Z:74, M:66, e:238,
    C:266, U:532, Res:1064.

The largest terms in C, U and Res are unique. Their nonzero leading forms,
and the nonzero main/index/transport leading forms, multiply to a nonzero
form in a polynomial ring over the integers. Hence the product degree is
uniformly exactly 35+13+4+1064=1116, not merely a generic upper bound.

## 7. Supplementary independent diagnostics

`INTEGER27_INDEPENDENT_CHECKS.json` records:

* 27 inputs and the independently recounted 139/74/65 operation ledger;
* 1,000 signed local elimination fixtures, including negative f, tau and
  y, with exact rational reconstruction of all three original roots;
* an additional dense modular univariate degree computation yielding 1116
  modulo the prime 65521.

These checks corroborate the algebra and bookkeeping. They do not prove
the inherited semantic/compiler lemmas or exhibit an accepting K215 run.
