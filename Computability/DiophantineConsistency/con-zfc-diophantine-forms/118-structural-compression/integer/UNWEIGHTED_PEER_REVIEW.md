# Independent mathematical review of the unweighted positive endpoints

Review date: 24 October 2026.
Reviewed manuscript: `analysis/unweighted_radicals/PROOF.md`.
Reviewer: independently assigned integer-reduction research agent.

## Conclusion

The new ordinary mathematical reduction is valid as stated, conditional on
the same retained source/Pell/native calibration as the accepted parents.
I found no gap or counterexample in the square-gap lemma, the elementary
three-radical rationality lemma, their application before all transport and
index deductions, the soundness/completeness transfer, or the claimed
degree-of-difference arguments. The new result changes the polynomial and
preserves positive-solvability existence; it does not assert equality of
polynomials or equality at unchanged witness tuples.

The review read the complete author proof and both actual parent proofs:

- `source/active/candidates/ten-positive-zero-offset/PROOF.md`;
- `source/active/candidates/ten-positive-direct-zero-offset/PROOF.md`.

I also checked the relevant transport formula in
`ten-positive-short-projection/PROOF.md` and the adjacent-descent interface
in the retained `zero-offset/source/ORIGINAL_PROOF.md`. The review does not
reprove the transitive native-compiler/refutation calibration or claim a
new Lean/internal-ZFC certificate.

## 1. Square-gap lemma

I independently expanded all four displayed parity identities using a
standard-library sparse polynomial ring in the two indeterminates m,t.
The even and odd formulas for D-h^2 and (h+1)^2-D match exactly.

The inequalities also hold on the complete stated domain, not merely in
a bounded sample. For even x=2m, m>=1 and t>=1:

    2t^2+4(m+1)t-m >= 3m+6 >0,

and

    2m(4m+1)t^2-4m^2t+(m+1)^2
       >= (4m^2+2m)t+(m+1)^2 >0.

For odd x=2m+1, m>=1. The lower gap evaluated at t=1 is
7m^2+18m+7>0 and increases with t. The upper gap is the square
[tx-(m+1)]^2, with tx>=2m+1>m+1, hence is strictly positive.
Thus the two consecutive-square inequalities are valid.

The identity Delta*v*(v+1)=t^2 D is exact. If the alleged equality
Delta I^2=v(v+1)k^2 held with nonzero I,k, then
D=(Delta I/(tk))^2 would be a rational square. An integer rational square
has an integer square root, contradicting the strict gap. This reasoning
does not require gcd assumptions on I,k,t or Delta.

The x=1,t=1 exception is correctly excluded. The actual applications have
X>=32, so no small-domain repair is needed.

## 2. Three-radical rationality

The algebraic identity

    4s*K_a*u = K_a^2+4s^2*a-4bc,
    K_a=s^2+a-b-c,

follows directly by squaring 2vw=K_a-2su. If s=0, the prohibited
triangle identity follows. If s is nonzero, at least one K is nonzero:
indeed K_a-K_b=2(a-b), and the radicands are pairwise distinct. Thus one
root is rational. The other two have a rational sum; that sum cannot be
zero because their squared magnitudes are distinct. Rationalizing their
sum gives each remaining root rational. This handles dependent square
classes and all choices of signs; no hidden Galois independence is used.

All three actual radicands are positive before using the target equation.
The pair-distinctness deductions are correct:

- d_tau=d_f is excluded by the square-gap lemma.
- d_tau=d_y would place a positive integer strictly between 0 and Q as
  an integer multiple of Q; Delta>v+1 and I>=k give the strict bound.
- d_f=d_y would make the integer d_f-V^2 equal 1/Delta, impossible.

The triangle expression is an integer after multiplying by delta^2.
Its residue is exactly -3 modulo mu, because Delta=v=Q=0,
delta=Dnum=-1 and d_tau=d_f=1 there. Only mu>3 is needed; mu need not
be prime. Consequently the noncancellation assertion holds uniformly.

## 3. No premature use of transport or rank

At every positive input, t=mu*Y and mu=q^2+1>3, so the modular hypothesis
is automatic. The parent source has k=eta+zeta>=2,
c=kY+eta>k and I=i*c^2>=c^2>k. Therefore I>=k is available before root
extraction. Delta>v+1 also follows directly from the new zero-offset A.

The auxiliary coordinate V=Df*b-c cannot vanish even when the integer b
is initially negative: b<=0 implies V<=-c; b>=1 implies
V>=Df-c>c, because Df>2c. This is a valid unconditional argument and
does not presuppose the later b>0 transport conclusion.

The cleared three-root polynomial has a real radical factor because
delta>0, M>0 and all radicands are positive. Dividing that factor by
M*sqrt(delta) supplies the required rational signed sum. The retained
adjacent-Pell descent only needs Q>1, integral V and rational y, all
available at this stage. Its hypotheses are independent of the old
coefficient 3 on tau.

## 4. Soundness and completeness transfer

In both parents, the strong/auxiliary folding and first-index deductions
use the integral root values and their unchanged individual Pell
equations, not the old coefficient 3. The only relevant center estimate
uses the sum 3tau+f. Replacing it by tau+f strictly strengthens the upper
bound used to contradict positive n in the bad-transport branch. The
direct-base estimate including X/q^4 is likewise strengthened. All later
rank, parity, denominator and whole-product steps retain their hypotheses.

For completeness, the parent zero-offset proof explicitly establishes
tau>k>Y>=s and f>kappa. Thus

    n=W*t_transport+rho+tau+f+u-s-kappa

is a positive integer with the fresh canonical witnesses. In particular,
simply subtracting 2tau from an arbitrary old n was not used; the author
correctly reconstructs n from canonical source data. Its center has the
desired unweighted positive radical sum.

The direct-base transfer preserves X and the entire kernel and changes
n by the positive integer (q-1)^2 L*t_transport+X/q^4. The latter integer
is licensed only after the recovered canonical binary-base facts. The
normalized centers agree, and all four norm arguments scale by q^2.
That homogeneity argument is independent of whether the tau coefficient
is 1 or 3, so it transfers to the fresh unweighted source.

## 5. Difference polynomial and exact degree

Expanding the three-root bracket gives exactly

    E_w=(s-c)^2-2(s+c)(wa+b)+(wa-b)^2,
    E_9-E_1=16a[5a-(s+b+c)].

Therefore the author's DIFF identity follows with the coefficient -512
on scab. The degree analysis is consistent and proves that the new
polynomials differ from their parents, rather than merely suggesting it
by modular evaluation.

For zero-offset, the degrees (a,b,s,c,d)=(74,76,104,104,92) give
deg(E_w)=184 with unique leading part d0^2. Since s0=c0, the first
DIFF summand has nonzero leading part -64a0*c0*d0^2 in degree362;
the other summand has degree358. Thus the difference has exact degree362
and cannot alter the degree368 leading component of either polynomial.

For the direct source, the degree tuple (68,70,96,96,85) gives
deg(E_w)=170, difference degree334, and scalar degree340. Again the
competing scab term has strictly lower degree330. All claimed leading
forms remain nonzero with the actual positive fixed beta because the
displayed factors are nonzero polynomials in independent input variables.

The literal row deletion, payload and exact circuit-count checks remain
the responsibility of the separately supplied finite checker. This peer
review establishes the unbounded mathematical changes and checks that the
degree reasoning has no omitted dominant or cancellation branch.
