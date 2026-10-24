# Signed source evaluation, absolute bounds, and domain restoration

This note records the source and domain changes in the batched direct C222
construction. It accompanies `verify_source.py`, which imports no
compiler and checks only supplied JSON. It separates the universal ordinary
mathematics from the exact finite transcription checks. The batched Pell
theorem is proved separately.

## 1. The source is a fixed eight-column certificate

The inherited direct source is the twelve-rule numerical C222 calculus.
Its label constructors are nonnegative integer polynomials. In each rule,
deterministic constructor wires and the two premise labels and conclusion
label are substituted before any bounded quantifier is eliminated. The
only nontrivial retained axiom guard is the bundle condition

    ((c-a)(c-b))^2=(d+1)^2,

which is equivalent, for some natural d, to c differing from both a and b.
It does not require either difference to have a specified sign.

For a fixed positive horizon N the local witness vector is

    (a,b,c,d,S,q,S_next,q_next),

with the heterogeneous bounds

    (N,N,N,N,y,U,y,U).

The two beta-code rows are

    x=q(1+(i+1)y)+S,
    x=q_next(1+(i+2)y)+S_next.

The bounds S,S_next<=y imply the strict Euclidean remainder bounds,
because y<1+(i+1)y for every natural i,y. The two reconstructions
therefore identify the same consecutive entries of the one common beta
code. Separate endpoints give S_0=M0+2 and S_N=1.

For a selected rule with premise labels p,q and conclusion v, the
accumulator row is

    S_next(1+vM)=S(1+pM)(1+qM),  M=M0+1.

For each rule, add the squares of its retained guard and its accumulator
row. Multiply the twelve resulting alternatives, then add the two
squared beta residuals. Call the resulting fixed integer polynomial R.
For natural row inputs, R=0 holds exactly when the two beta rows and one
valid rule update hold. The polynomial is nonnegative even on arbitrary
integer inputs, but the source proof uses the natural domains recovered
by the bounded certificate.

The audit independently reconstructs each canonical constructor from its
coefficient list, checks each monic defining row, and verifies every
projected premise/conclusion row. It then reconstructs the entire R in
two different representations: the inherited nonnegative pair E-F and
the new direct signed arithmetic expression. Both identities are checked
compositionally over the integers, without numerical sampling.

## 2. Padding and the large-base test

A finite refutation expands into a finite proof tree. Increase its
horizon N until N bounds both its length and its four actual rule
parameters, then pad it by truth rows. A truth row has all three labels
zero and leaves the accumulator unchanged. Let H(N) be the sum of every
rule's three label polynomials after substituting N for the four rule
parameters. Every label is at most H(N). Set

    M0=2^(2H(N)N+1), M=M0+1.

These explanatory powers are replaced by the explicit arithmetic
certificate in the final polynomial. They are chosen before the
accumulator trace, its beta encoding, and the independent bound U.

The products

    A(X)=product_i(1+v_i X),
    B(X)=(1+X)product_i(1+p_i X)(1+q_i X)

have coefficient difference bounded in absolute value by M0. A(M)=B(M)
therefore implies A=B as integer polynomials: the least nonzero
coefficient of A-B would have to be divisible by M after reduction
modulo M, although its absolute value is below M. Comparing the distinct
linear-factor roots -1/j for positive labels j gives the exact Horn
flow balances. The standard finite cut argument for single-conclusion
rules then gives a derivation of the target 1. Cycles and repeated
premises cause no exception. Conversely a proof tree supplies the
integral accumulator by multiplying the factors for its outstanding
obligations.

No bound on the possible size of a ZFC refutation is imposed. N=N0+1
simply makes its positive choice explicit; the proof tree can be padded
to every sufficiently large positive horizon.

## 3. Absolute circuit bounds avoid positive-pair duplication

Let an integer arithmetic circuit C use constants, variables, addition,
subtraction and multiplication. Define C# by replacing a fixed constant
c by |c| and every subtraction by addition, leaving addition and
multiplication unchanged. If each variable z is nonnegative and bounded
by u, then

    |C(z)| <= C#(u).

This is proved by induction on the actual circuit: use the triangle
inequality for addition and subtraction, and multiplicativity of
absolute value for multiplication. C# is a polynomial with nonnegative
integer coefficients, so it is monotone on natural inputs. Shared nodes
do not change the induction or the represented values.

Apply this construction to the signed local circuit R, keeping the outer
parameters fixed and replacing its index by N and its local coordinates
by the bound vector u. Write J=R#(N,u), and choose

    L=J+N, T=L!.

The encoded row congruence now evaluates R directly. The upper bound
evaluates R# directly. Neither evaluation needs the large positive and
negative pair, even though that pair is retained in the artifact as an
independent source comparison. In the CRT proof below, |R|<=J<p is all
that is required. There is no inference from a signed arithmetic wire to
its nonnegativity.

The audit checks the complete upper environment, including its N/y/U
roles, then reinterprets the actual signed DAG under the absolute
operations and compares its result with the literal factorial argument.
It separately compares the signed encoded evaluation with R at the
actual encoded columns. These are exact checks of the entire interfaces.

## 4. The prime-lift bounded-row theorem

Put d_i=1+(i+1)T and B=product_{i<N}d_i. For each local coordinate j,
the certificate requires

    B divides binom(A_j,u_j+1).

It also requires B divides 1+(C+1)T and B divides R(C,A). The encoded
columns A_j are positive; the encoded index C is nonnegative.

For soundness, fix i<N and choose a prime p dividing d_i. Since p does
not divide T=L!, one has p>L. Comparing the index congruences gives
C=i modulo p. Multiply each binomial divisibility by f_j=(u_j+1)!.
The integer identity

    f_j binom(A_j,u_j+1)=product_{s=0}^{u_j}(A_j-s)

gives some r_j in [0,u_j] with A_j=r_j modulo p. The identity also holds
when A_j<u_j+1, because a zero factor occurs. Hence R(i,r)=0 modulo p.
The absolute-circuit bound gives |R(i,r)|<=J<=L<p, so R(i,r)=0 as an
integer. No assertion that A_j modulo the generally composite d_i is
bounded is made. Neither p>u_j nor invertibility of f_j is needed.

For completeness, choose bounded solutions r_ij of all N local rows.
The d_i are pairwise coprime: a common prime divisor of d_i and d_l
would divide i-l but not T, although every positive integer below N
divides T. For coordinate j strengthen each period to

    D_ij=product_{p|d_i}p^(v_p(d_i)+v_p(f_j)).

These strengthened periods are still pairwise coprime across i. CRT
supplies A_j congruent to r_ij modulo D_ij. Choose it sufficiently
large and positive by adding a multiple of product_i D_ij. The factor
A_j-r_ij in the falling factorial has enough p-adic valuation to
survive division by f_j, proving d_i divides binom(A_j,u_j+1). Their
product B therefore divides that binomial. The stronger congruences
imply the original row and index congruences.

The stronger periods matter: with N=2,T=2,B=3*5=15 and u=4,
binom(0,5)=0 is divisible by B, whereas binom(15,5)=3003 is not.
Here the lifted period is 3^2*5^2=225 and binom(225,5) is divisible by B.
Thus a generic shift by B would not justify the positive-column
parameterization; the prime-lift construction does.

Every choice is finite. The order is the proof and padding, M, the
accumulator, beta code, quotient bound U, J,T,B, and finally the encoded
columns. No coefficient, circuit or equation depends on which proof
might exist.

## 5. Arithmetic interfaces and unconditional positivity

All forty power outputs are parameterized as m=m0+1. Both factorial
outputs are parameterized as f=f0+1. These shifts are complete because
all relevant power bases and exponents are positive and all factorials
are positive. For soundness their positivity is a literal domain fact,
not an assumption justified circularly by the same power theorem.

The audit assigns lower bound zero to every guarded semantic input and
no bound to any unrestricted input. It propagates these lower bounds
through the complete arithmetic DAG. All forty power bases and all
forty exponents are already at least one, before using any power or
factorial correctness theorem. No unrestricted semantic variable occurs
in any such argument. This verifies the input hypotheses of the
simultaneous Pell certificate without an arithmetic dependency cycle.

For a binomial graph put q=2^n+1, D=q^k and V=(q+1)^n. Its rows are

    V=D(qh+b)+r, D=r+rs+1, q=b+bs+1.

They give the two strict remainder bounds. The binomial expansion has
every coefficient below q, so b=binom(n,k), including b=0 when k>n.

For a factorial argument n>=1 put R=(n+2)^(n+2) and c=binom(R+n,n).
The retained ceiling identity is

    (R+1)^n+c=c*f+r+1, c=r+s+1.

It is the inherited explicit factorial representation. The modulus
product formula and the three Euclidean divisions are unchanged. The
audit checks each of the eleven binomial, two factorial and three
division interfaces against the actual primitive-call ledger and the
actual polynomial equalities, rather than trusting labels alone.

## 6. Twenty quotient signs need no separate witnesses

The eleven binomial high coordinates h can range over all integers.
Indeed q,D>=1, 0<=b<q and 0<=r<D. If h<=-1 then qh+b<=-1, so the
right side of V=D(qh+b)+r is at most -1, contradicting V>=0. Thus every
integer zero already has h>=0.

The eight coordinate-divisibility quotients are also automatically
nonnegative: their defining equations are binom(A_j,u_j+1)=Bq_j, with
nonnegative left side and B>0. The index quotient is positive because
1+(C+1)T=Bq has a positive left side. B is the already represented
product of positive moduli. These inferred signs are used only after
the corresponding arithmetic identities have been established.

All twenty coordinates are absent from every power base and exponent;
the audit checks this complete dependency condition. Therefore dropping
their guards cannot undermine the positivity proof that licenses the
batched power theorem. The ordinary Euclidean quotient signs are
inferred separately from their natural dividends, positive divisors and
strictly bounded remainders.

## 7. Mathematical and computational scope

The source proof uses finite polynomial arithmetic, elementary prime
factorization, finite CRT, finite induction, and the named inherited
C222 and Pell representation theorems. It is ordinary mathematics
formalizable in ZFC. Its use of internally finite objects does not
require arithmetic soundness, the consistency of ZFC, or restriction to
externally standard natural numbers.

The independent source checker verifies the finite literal
transcriptions and domain licenses described above. The separate
coefficient checker verifies graph flattening and the final collected
polynomial. Neither finite computation replaces the universal
mathematical proof, and neither is a newly emitted object-language ZFC
derivation or a new end-to-end Lean proof.
