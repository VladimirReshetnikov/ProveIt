# Independent mathematical audit of the fixed-input specialization

Reviewed source: `design_work/fixed_input_derivation.md` and
`design_work/fixed_input_linear_guard_sources.json`, using repository
snapshot `cdd582bec13f908df3711fa9e05d1ddac368a5db` for inherited lemmas.

Package note: those were the working-draft paths. The integrated proof is now
`../zfc_diophantine.tex`, and the identical circuit source is
`../data/fixed_input_linear_guard_sources.json`. This review is a separate
agent review within the research collaboration, not an external human review.

**Outcome:** the new fixed-input mathematical reduction passes the review
described below. This is an ordinary mathematical audit, not a new Lean,
Rocq, or encoded-ZFC proof check. Source operation and degree ledgers are
separate arithmetic-circuit checks. The enormous concrete compiler numerals
are defined by the finite recipe; this audit does not claim their expansion.

## 1. Exact scope of the new argument

The audited specialization fixes the ordinary input at x=1, so its End
marker is the fixed integer W0=2^(b+2d). It removes the parent Pell input
loader, replaces rho and sigma by the single positive coordinate
gamma=rho+sigma, and substitutes the factor

    Nfixed = 3W + (1-3W0).

The parent seven-factor product is still required to equal 1. Each factor
is an integer unit. Since Nfixed is 1 modulo 3, it cannot be -1; hence
Nfixed=1 and W=W0. In particular C=Z+W0>0 and F+Z<q follow before any
input decoding or full parent universality theorem is invoked.

The 73-operation source scales the complete unscaled polynomial by the
computed discriminant Delta. Delta=(a+1)(a+3)>0 on the entire supplied
positive domain, independently of the equations. Cancellation therefore
preserves its complete positive zero set. The scaled final product must
not itself be interpreted as a product of seven units before this
cancellation: its right side is Delta.

## 2. Unit signs and auxiliary positivity

The first norm is tau^2-v(v+1)k^2 with v=XY^2>1. A putative least positive
negative-Pell solution gives the smaller positive second coordinate
(2v+1)k-2tau: the inequalities vk<tau<(v+1/2)k prove both claims.
Multiplication by the inverse norm-one unit preserves norm -1. This
excludes the negative sign without any computation-encoding assumption.

Delta is either 0 or 3 modulo 4. The main and strong norm factors cannot
be -1 modulo 4. The auxiliary coefficient Kaux is a square; modulo 4
its norm factor reduces to either y^2 or V^2, so its negative unit sign
is excluded as well. Thus the five norm/fixed factors equal +1, leaving
the index and transport factors with a common possible sign.

The unchanged packing estimate gives R>0, R<a<Delta, and E>R+q^3.
The strong norm gives f^2=1+Delta*i^2*c^4 and f>c^2>2c. Using
Kaux=Delta*(f^2-1), the difference

    Kaux-(R*f^2+c)=(Delta-R)f^2-Delta-c

is positive. If V were negative with |V|>1, the auxiliary norm forces
|V|>=2Kaux-1, contradicting V>-Kaux. Values V=0,+1,-1 are also
excluded: V=0 contradicts the norm, and V=-c modulo f with f>2c>2
excludes the two unit values. Therefore V>0. The restored integer
quantities

    o=cT-Rf,       j=Tf-R*Delta*i^2*c^3-1

are positive because of=V+c>0 and jc=V+R>0. This uses no omitted input
coordinate.

## 3. The inherited local lemmas really apply

The relevant part of
`Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` is its generic strong-rank
argument, beginning with the main Pell solution c=psi_A(p). Its necessary
hypotheses are c>A*Delta^2 and

    (i_old*c^2)^2=Delta*(f^2-1),     Delta=A^2-1.

Here A=a+2, and taking i_old=Delta*i gives exactly the required equation.
The new proof establishes p>=25 and c>A*Delta^2 independently first.
The conclusion is f=chi_A(m), c divides m, p divides m, and m>=c>2p.
It does not require an input norm or decoded history.

Section 4 of
`Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md`
then supplies the signed auxiliary step-down. With its ordinary coefficient
T_old=i_old*c^2, the required congruences follow from

    V=of-c=jc-R,
    T_old^2=Delta*(f^2-1),
    0<R<c/2, 0<p<c/2, m>=c>2p.

Every one of these hypotheses is available. The temporary displaced
target of that note is simply R here; the restored linear equation has
sign +1. Thus its local conclusion p=R is legitimate. The proof does not
invoke the whole parent compiler to recover a missing premise.

The first-norm index n satisfies 2n=R+epsilon modulo E and n<p=R.
Because E>R+q^3, any positive multiple of E would make 2n>2R. Therefore
2n=R+epsilon. If epsilon=-1, then p=2n+1. The inequality
chi_A(2)>2XY^2+1 and Pell duplication give c>k(Y+1), contradicting
c=kY+eta with 0<eta<k. Consequently both remaining unit signs are +1.

## 4. Exponent recovery and restoration of the omitted loader

The new exponent argument is noncircular. With r=(R-1)/2>=1, Pell bounds
give

    c/k >= (1/2)*((2A-1)^2/(2P))^r
         > (1/2)*((X+1)^2/X)^r,       P=2XY^2+1.

The strict second comparison follows by expanding its cross-multiplied
difference, which is
12XY(X+1)+9X-2(X+1)^2>0. Together with c/k<Y+1, Y>2, and X>=16,
this proves a>2^R. The recurrence for E_A(n)=chi_A(n)-a*psi_A(n)
has initial values 1,2 and yields E_A(n)=2^n modulo H=4a+3. The main
root identity E_A(R)=X+gamma*H therefore gives X=2^R, since both X
and 2^R lie strictly between 0 and H.

Now q divides X, so q=2^t, and (2^d-1) divides q-1, so d divides t
and q=B^N. **Strict t<R uses the earlier bound R>q^2**, not merely
q dividing X (which on its own only gives t<=R). Since W0<q, the
fixed odd index u0=b+2d satisfies u0<t<R. Both R and u0 are odd, so
R>=u0+2.

The restored coordinates are

    kappa=psi_A(u0), mu=chi_A(u0),
    delta=(kappa-u0)/Delta,
    rho=(E_A(u0)-W0)/H,
    sigma=gamma-rho.

Odd-index Pell congruences give integrality of delta, and the recurrence
above gives integrality of rho. Pell growth gives delta,rho>0. Finally

    H*sigma=E_A(R)-E_A(u0)-X+W0

is positive, since the gap R>=u0+2 yields

    E_A(R)-E_A(u0)
       > psi_A(u0+2)-2psi_A(u0)
       > (4A^2-2A-3)psi_A(u0)>A>X.

Thus gamma=rho+sigma is restored with both summands strictly positive.
The exact parent input norm and its positive-coordinate interface are
recovered before the full parent theorem is applied. Conversely, every
parent positive zero at x=1 gives the specialized zero by forgetting
delta,rho,sigma and supplying their indicated sum. This establishes the
needed existential equivalence. The stronger claimed uniqueness is
consistent with the parent input-rank theorem, but is not needed for the
ZFC-consistency result.

## 5. Two roots may be allowed arbitrary signs

The coordinates tau and y occur only through their squares. The unit-sign
argument remains valid for signed roots: use |tau| in the negative-Pell
descent, and the auxiliary modulo-4 exclusion already uses only y^2.
At every valid zero tau is nonzero: its norm equation says
tau^2=1+v(v+1)k^2>0. Likewise y cannot be zero: its norm equation would
then say Kaux*V^2=1, whereas Kaux=(Delta*i*c^2)^2>1. Therefore every
zero with tau,y arbitrary integers has |tau|,|y| strictly positive and
gives a zero of the positive system. Conversely every positive zero is
already such an integer-root zero. All other fourteen coordinates remain
strictly positive; in particular the coefficients i,h,s,w and the
quotients must not be silently allowed arbitrary signs.

For conversion to an ordinary integer polynomial, every positive integer
is represented by

    Pos(a,b,c)=a^2+b^2+c(c+1)+1,       a,b,c integers.

This is always positive. Surjectivity follows by representing 4n+1 as
three squares for n>=0. The three-square theorem applies since 4n+1 is
not of the form 4^j(8k+7); modulo 4 exactly one square is odd. After
permuting coordinates and writing them as 2a,2b,2c+1, division by 4
gives n=a^2+b^2+c(c+1). This argument also covers n=0.

Replacing the fourteen positive coordinates by independent Pos triples
and retaining tau,y as unrestricted integer variables yields exactly
14*3+2=44 integer unknowns. There are no remaining inequalities or
external positivity conditions. The substitution is polynomial; its
surjectivity and the absolute-value recovery above prove both directions
of existential equivalence. A claim about its expanded exact degree
requires the separately checked leading-form argument and is not inferred
solely from doubling the syntactic degree bound.

## 6. Logical scope

The conclusion is the equivalence of solution existence with a finite
ZFC refutation, and hence of nonexistence with syntactic Con(ZFC).
Proving this equivalence does not prove either side unconditionally.
Under consistency, Goedel's second incompleteness theorem prevents ZFC
from proving the nonexistence statement. Two-sided independence should
not be attributed to bare consistency without the additional relevant
soundness assumption.

The new finite constructions, Pell arguments, congruences, and elementary
existential substitutions are formalizable in ZFC. No general reflection
principle for Lean, Rocq, or ZFC is asserted or needed. The inherited
K215 ordinary calibration and the native compiler remain explicit cited
theorems, rather than being replaced by claims about having run tests.
