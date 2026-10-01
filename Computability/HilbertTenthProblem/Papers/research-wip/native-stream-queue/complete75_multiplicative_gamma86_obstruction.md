# The multiplicative-gamma 86-operation shortcut has empty valid slices

Replacing the main projection quotient `gamma=rho+sigma` by
`gamma=rho*sigma` in [normalized87](complete75_normalized_strong87.md)
saves one addition by sharing the already paid product `rho*H`. The
resulting literal polynomial costs **86=48M+38A**, with the same nineteen
positive witnesses. It has **no positive zeros on any valid complete75
compiler slice**, even for an accepted input. It therefore gives no new
universal bound.

The [source](complete75_multiplicative_gamma86_obstruction.py) and
[receipt](complete75_multiplicative_gamma86_obstruction.json) freeze this
specific rejected shortcut. The obstruction is different from the
[weakened-bound86 collapse](complete75_weakened86_full_negative_family.md):
the present source retains the full raw input bound and every other gate
of normalized87. The conclusion is about this source, not all possible
86-operation representations or the unresolved independent-gamma route.

## 1. Literal source and recovery of the genuine main kernel

Delete only `gamma_sum=rho+sigma`. Replace
`gam=gamma_sum*H` by `gam=sigma*modulus_multiple`, where the unchanged
`modulus_multiple=rho*H` also feeds the input root. Topological reordering
introduces no operation. The comparison certificate costs85=48M+37A;
the final subtraction gives86 operations. Every gate reaches the output.

Use all fixed compiler hypotheses of normalized87, including the actual
masks, dyadic fixed cell radix B=2^d with d>=4, positive ordinary input x,
and odd inner offset b. All nineteen supplied witnesses remain strictly
positive. Write

    q=(B−1)J+1, X=w*q^3, Y=s*q^3, a=Y(X+1),
    A=a+2, Delta=A^2−1, H=4A−5=4a+3,
    k=eta+zeta, c=kY+eta, Gamma=rho*sigma,
    D=X+ac+Gamma*H,
    C=q−F−Z−alpha−2d*x, W=C−Z,
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.                              (1)

The source register named `A` is Delta; mathematical A denotes its Pell
parameter, as in the parent notes. The packed R and all eight norm/unit
factors are otherwise identical to normalized87.

Suppose the polynomial vanishes. Its strong norm cannot be −1 modulo4.
The positive change `i_old=Delta*i` therefore restores the full auxiliary
condition exactly as in normalized87 Section2. This is an algebraic
restoration of that block with the same positive Gamma, not an embedding
into a parent tuple with a necessarily positive additive sigma.

Apply [coupled88 Sections2–5](complete75_coupled_index_linear88.md).
Those sections require only Gamma>0 for the main root, both ratio slacks,
the strong auxiliary block, the retained raw bound and the actual masks.
They do not decode the input norm or use Gamma>rho. In particular weak
transport gives C>=0 and F+Z<q, hence −q<W<q. The packed-index bounds,
rank argument, ratio step and mask population obstruction establish the
genuine main kernel and all unit signs. Consequently

    q is dyadic, q>=16,
    R>(2q−1)(q^2−1)>=q^2, R=3 modulo4,
    X=2^R, c=psi_A(R), D=chi_A(R),
    Y=floor((X+1)^(R−1)/X^((R−1)/2))/2.              (2)

The last identity is the retained
[half-binomial theorem](pell_kernel_half_binomial42.md).
The positivity and norm classification used here precede any input-index
identification. In particular no additive parent witness is silently
assumed positive when sigma=1.

## 2. The input still decodes, forcing quotient divisibility

The raw bound and fixed offset give 3<=u<q+b<2q<R<A−1, with u odd.
The computed input root is positive: W>−q, a>q and kappa>=1 imply
mu>−q+a>0. Its positive Pell norm gives

    kappa=psi_A(v), mu=chi_A(v), v>=1.

The sequence `E_A(n)=chi_A(n)−(A−2)psi_A(n)` has initial terms1,2
and recurrence `E_A(n+1)=2A E_A(n)−E_A(n−1)`. It is strictly increasing
for integer n>=0. Since sigma>=1, Gamma>=rho; together with W<X this
gives the strict inequality

    E_A(v)=W+rho*H < X+Gamma*H=E_A(R).

Thus v<R. This remains strict at sigma=1. For 0<v<R<A−1 the standard
discriminant congruence has representatives

    psi_A(v) = v modulo Delta          if v is odd,
    psi_A(v) = A*v modulo Delta        if v is even.

They lie strictly between0 and Delta. Because kappa=u modulo Delta and
u<A, the even case is impossible and the odd case forces v=u.

For every n>=0 define the integer polynomial

    G_n(A)=(chi_A(n)−(A−2)psi_A(n)−2^n)/(4A−5).       (3)

Its integrality is proved below. It implies W=2^u modulo H. Since
−q<W<q, 0<2^u<X<a and H=4a+3, adding or subtracting H cannot land in
(−q,q). Hence W=2^u exactly, without presupposing W>0.

Equations (1)–(3) now yield

    rho=G_u(A), Gamma=G_R(A), G_R(A)=sigma*G_u(A).    (4)

The remaining proof shows that this numerical divisibility is impossible
in the enormous A-range forced by (2).

## 3. Projection polynomials and a separating negative root

The recurrence of E_A and its initial values give

    G_0=G_1=0, G_2=1,
    G_n=2A G_(n−1)−G_(n−2)+2^(n−2), n>=3.          (5)

This proves (3) in Z[A] by induction. For n>=2, G_n has degree n−2,
leading coefficient2^(n−2), and coefficient norm

    ||G_n||_1 <= 4^(n−2).                            (6)

The bases n=2,3 are1 and2A+2. For n>=4 the recurrence bounds the norm
by `2*4^(n−3)+4^(n−4)+2^(n−2)`, at most `(13/16)*4^(n−2)`.

**Polynomial nondivisibility.** If u>=3 and R>u are both odd, then G_u
does not divide G_R in Q[A]. To see this, put A=−a for 1<=a<=5/4.
Parity of the Pell polynomials gives, for odd n,

    E_(-a)(n)=F_a(n):=(a+2)psi_a(n)−chi_a(n).

At a=1, F_1(n)=3n−1. Thus F_1(u)<=2^u for odd u>=3, with equality
only at u=3. At a=5/4,

    F_(5/4)(n)/2^n=5/3−(8/3)*4^(−n)>1, n>=2.

Continuity supplies a_u in[1,5/4) with F_(a_u)(u)=2^u. Hence
G_u(−a_u)=0, since4(−a_u)−5 is nonzero.

For 1<a<5/4 let `lambda=a+sqrt(a^2−1)` lie in(1,2) and put

    C0=((a+2)/sqrt(a^2−1)−1)/2>0, D0=C0+1.

For real n>=1, extend the sequence by

    F_a(n)=C0*lambda^n−D0*lambda^(−n)>0.

Positivity follows from F_a(1)=2 and the increasing ratio of the first
term to the second. The real function

    log(F_a(n)/2^n)
      =log(C0)+n*log(lambda/2)
         +log(1−(D0/C0)*lambda^(−2n))                 (7)

is strictly concave: the last logarithm has strictly negative second
derivative. At a=1 use `log(3n−1)−n*log(2)`, also strictly concave.
For a=a_u this function is zero at1 andu. Strict concavity forces it
to be negative at every n>u (compare the secant slopes). Therefore
F_(a_u)(R)<2^R, and G_R(−a_u) is nonzero. A common polynomial factor
equal to all of G_u would vanish at every root of G_u, a contradiction.

This argument covers all odd R>u. No finite root search or conjecture
about irreducibility is required.

## 4. Large integer evaluation preserves the obstruction

Polynomial nondivisibility alone does not imply numerical
nondivisibility; a bound on an integer pseudo-remainder supplies that step.
Let d=u−2 and a0=2^(u−2) be the leading coefficient of G_u. Starting at
r_0=G_R, while its degree is at least d perform

    r_next=a0*r−lc(r)*A^(deg(r)−d)*G_u.               (8)

Degree drops at each step, so there are s<=R−u+1 steps. The final
integer polynomial r satisfies

    r=a0^s*G_R−Q*G_u for Q in Z[A],
    r!=0, deg(r)<=u−3.                               (9)

Nonvanishing follows from Section3. Since a0+||G_u||_1<=2^(2u−3),
(6) and (8) give

    ||r||_1 <= 2^[2R−4+(2u−3)(R−u+1)]
             < 2^[(2u−1)R].                         (10)

For the genuine half-binomial parameter in (2), X=2^R and

    (X+1)^(R−1)/X^((R−1)/2) >= X^((R−1)/2).

The right side is an integer, so taking the floor preserves this lower
bound. It follows that

    Y>=2^[R(R−1)/2−1],
    A>=2^[R(R+1)/2−1].                              (11)

Since q>=16, R>=q^2 and u<2q, we have R>4u. Thus the exponent in(11)
is strictly greater than (2u−1)R. In particular

    A>||r||_1, A>||G_u||_1.

The leading integer coefficient of r dominates its lower coefficients
at this A, so r(A)!=0. Its degree and (10) give

    0<|r(A)| <= ||r||_1*A^(u−3) < A^(u−2).

Since G_u has leading coefficient at least2 and lower coefficient norm
less than A, likewise

    G_u(A)>A^(u−2)>|r(A)|>0.                         (12)

If G_u(A) divided G_R(A), identity (9) would make it divide r(A),
contradicting (12). This disproves (4). Every positive zero under the
full compiler contract would imply (4); therefore there are none.

## 5. Exact evidence and scope

The source guard checks the precise deleted gate, sole changed gate,
unchanged input product, witness interface, complete closure and literal
operation histogram. On arbitrary integers the new complete source equals
the parent source after `sigma_parent=rho*(sigma_candidate−1)`. This
identity is checked on384 assignments, including128 signed assignments
and32 positive assignments with sigma=1. The restored parent sigma can
be nonpositive; this identity is not used as an unconditional positive
embedding or completeness argument.

The checker independently constructs the Pell projection polynomials by
multiplication in Z[A,sqrt(A^2−1)] and compares them with (5) through
index99. It checks exact rational endpoints for the separating-root
argument, independently verifies the pseudo-division identity and
rational remainders, and evaluates (9)–(12) at21 explicitly materialized
half-binomial parameters. Independent Pell exponentiation checks both
projection values in each numerical case. Compiler range inequalities
are also checked without materializing their astronomical parameters.

These finite fixtures test source accounting and exact algebra. The
all-index empty-slice conclusion is the proof in Sections1–4, under the
inherited complete compiler hypotheses. The fixtures are not complete
positive compiler zeros. The established87-operation universal polynomial
and75-operation comparison certificate remain unchanged.

```sh
python3 complete75_multiplicative_gamma86_obstruction.py
```

The author writer and fresh replay pass. Native and Franklin independently
reviewed the complete proof, literal source and inherited dependencies,
including the sigma=1 boundary, and each passed a fresh replay without
findings. Native independently constructed the Chebyshev projection
polynomials through index163, checked30 additional exact pseudo-remainders
for u=21 through39 with coefficient bounds, and checked192 complete
source/output identities (96 signed, including32 sigma=1 boundaries).
Franklin independently generated74 projection polynomials from explicit
binomial formulas, checked366 rational remainders without the author's
pseudo-division helper, and verified seven further exact half-binomial
parameter/Pell-quotient cases and218 compiler-growth inequalities. These
independent exact computations support, rather than replace, the all-index
proof. Local links and whitespace checks pass.
