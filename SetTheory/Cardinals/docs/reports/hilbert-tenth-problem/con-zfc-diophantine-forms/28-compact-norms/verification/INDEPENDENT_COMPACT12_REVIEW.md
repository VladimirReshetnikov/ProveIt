# Independent review of the compact twelve-variable construction

## Result and scope

The proposed positive-domain construction passes this independent mathematical
and exact algebra review. It has twelve strictly positive supplied unknowns,
three equations of maximum degree 1072 with 112 binary arithmetic gates, or
one product polynomial of degree 1081 with 116 gates. The alternative sum of
squares has degree 2144 and 119 gates. The counts include multiplication by
fixed numerical constants.

The substantive new argument is the simultaneous reduction of the separating
weight and the first-root coefficient. The resulting degree improvement does
not assume that a root supplied by a resultant is already rational or real.
The construction imports the existing signed Pell/compiler equivalence and
the fixed K215 halting/refutation calibration. This review is not a new
proof-assistant certification of those imports.

The proof was reviewed against `proofs/COMPACT12_PROOF.md`, the literal
`circuits/compact12_system.json`, `circuits/compact12_product.json`, and `circuits/compact12_sos.json`,
and the inherited `21-norm12/proofs/NORM12_PROOF.md` and
`21-norm12/upstream/ORDINARY_BLANK_PROOF.md`. The source repository is
VladimirReshetnikov/ProveIt at commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

## 1. The positive-domain separation proof

Use the definitions from the construction, in particular

    I=i c^2, D=1+Delta I^2, G=1+Delta c^2,
    Q=(Delta I)^2, d=Q-1, v=cT, b=c+RD,
    W=T^2+X I^2, L=1+HW, Jtau=4HW,
    S=X+ac+Hr.

Every supplied unknown is positive. The inherited weak transport argument,
which is valid for both common unit signs of the two outer factors, gives

    q>=16, X>=16, Y>=4096, E>=q^4>R+2, R>0.

Since h>=1 and k=hE+R+epsilon with epsilon in {1,-1}, it follows that
k>=E+R-1>2R. This is available before any radical has been proved rational.
The strict inequalities c>1 and I=i c^2>c are likewise immediate.

For any coherent norm branch, the auxiliary root satisfies

    d y^2=Q(vf-b)^2-1, f^2=D.

The absolute-value bound remains valid for every embedding into the complex
numbers. Both possible values of f are real. If y^2 is negative, its
absolute value is at most 1/d; the positive extreme corresponding to
v sqrt(D)+b is larger than that. Consequently

    |y'| < sqrt(Q/(Q-1)) (v sqrt(D)+b).

All inequalities needed to normalize this estimate are elementary:

    D/G < I^2/c^2,
    sqrt(D)<(a+2)I,
    sqrt(G)>ac,
    R(a+2)/c < (X+2)/2.

The first uses I>c; the last uses R/k<1/2, c>kY, and
(a+2)/Y=X+1+2/Y<X+2. Since Q>=2, sqrt(Q/(Q-1))<3/2. Therefore

    |y'|/sqrt(G)
      < (3/2)TI + 3/(2a) + (3/4)(X+2) I^2.

There is ample strict slack in the claimed domination by W. Subtracting
the right side from W gives

    (T-3I/4)^2 + (X/4-33/16)I^2 - 3/(2a),

which is strictly positive already for X>=16, I>=1, a>=2: the second
term is at least 31/16, whereas the final magnitude is at most 3/4.
Thus |y'|<W sqrt(G) uniformly over all embeddings.

The comparison between the other two radicals is also independent of root
recovery. Because sqrt(A)>ell=kXY^2, c<k(Y+1), and
sqrt(G)<(a+2)c, one has

    sqrt(G)/sqrt(A)
      < ((X+2)/X)((Y+1)/Y)
      <=153/128<4/3.

Hence Jtau sqrt(A)>3HW sqrt(G)>(L+HW)sqrt(G), since HW>1.
The other domination is L sqrt(G)>HW sqrt(G)>H|y'|.

## 2. Rationality, integrality, and congruence

The finite norm vanishes only if one coherent choice of u, tau, f, y obeys

    u^2=G, tau^2=A, f^2=D,
    d y^2=Q(vf-b)^2-1,
    S=L u+Jtau tau+H y.

If tau is irrational, its sign-changing embedding extends to an
automorphism of a finite normal splitting field. Subtraction of the two
linear identities contradicts the first strict domination above. Thus tau
is rational. Its square is an integer, so tau is an integer. Repeating the
argument for u while fixing rational tau proves that u is an integer.

The linear identity then makes y rational. The coefficient
Baux=2Qvb is positive, so the expanded auxiliary identity recovers

    f=(e-d y^2)/Baux

as a rational number. Since f^2=D is integral, f is integral. At this stage
vf-b is integral and Q=(Delta I)^2 with Delta I>=2. The specialized
rational Pell saturation lemma is applicable and proves y integral. This
step is necessary: rationality of y and integrality of Hy alone would not
be sufficient.

Finally L=1 modulo H, Jtau=0 modulo H, and S=X+ac modulo H. Thus
gamma=(u-X-ac)/H is an integer, giving the main-root coordinate required by
the inherited signed interface. Substitution of f^2=D changes vf-b into
c(Tf-1)-Rf^2, exactly the original auxiliary expression. No positivity
assumption on these recovered roots or gamma is smuggled into this step.

Conversely, on a canonical positive normalized compiler witness, define

    r=gamma+W u+4W tau+y.

It is positive, and direct substitution gives S=L u+Jtau tau+H y. The
corresponding factor of the norm is zero. This proves the claimed
existence equivalence using the inherited compiler theorem.

The proof as reviewed applies to the twelve-positive-variable domain.
It must not be used unchanged to claim a 26-integer-variable version.
In particular, replacing h by an unrestricted integer invalidates the
immediate pre-recovery bound k>2R when h=0. That variant requires a
separate argument or a different weight.

## 3. The product finalizer has a simpler parity justification

The circuit writes N=N0^2-G N1^2. Since
Delta=(a+2)^2-1 is 0 or 3 modulo 4, G=1+Delta c^2 is 0 or 1 modulo 4.
A square minus either zero or a square is never 2 modulo 4. Therefore
N cannot equal -2, and 1+N cannot equal -1.

At a zero of Nk Nt(1+N)-1, all three factors are integer units. The last
one must be +1, so N=0 and Nk=Nt are equal unit signs. These are precisely
the hypotheses used by the preceding weak-sign proof. The inherited
stronger divisibility statement N1=0 modulo 8 is correct and was checked
as well, but the elementary quadratic-norm parity argument suffices.

## 4. Exact circuit and degree checks

`verify_compact12.py` imports no emitter, no external package, and no
compiler source. It reads the three literal JSON circuits and independently
performs the following checks:

1. Every register is defined once; each operation is binary +, -, or *;
   all inputs and registers are live; all three ledgers are recounted.
2. The entire norm kernel is expanded as a sparse polynomial over Z in
   ten independent formal parameters. Independently, the program multiplies
   the four conjugate quartic factors in the quotient ring
   Z[parameters][u,t]/(u^2-G,t^2-A). All nonconstant quotient-ring
   coordinates vanish, and the scalar coefficient agrees identically
   with the emitted kernel. This is full symbolic coefficient equality,
   not interpolation or random testing. The expanded identity has 295
   monomials.
3. The highest homogeneous part is propagated with all four coefficient
   ports kept as formal degree-zero indeterminates. Exact coefficient
   comparison verifies the 1649-monomial expansion of

       N_top=2^32 i^48 (eta+zeta)^96 w^80 s^176
             (beta J)^656 (beta J-F)^16.

   This is nonzero for every fixed beta>0. The norm has degree1072, the
   product degree1081, and the sum of squares degree2144.
4. Twenty-four signed integer and twenty-four signed rational assignments
   check the finalizers and the rewritten strong/weight blocks. Integer
   assignments also check both parity statements.

An explicit nonvanishing coefficient of the product is useful independently
of the script. Its monomial

    J^677 h z i^48 eta^96 w^81 s^177

has coefficient 2^32 beta^677. Thus the degree1081 statement is uniform
over all certified coefficient tuples, rather than a degree observed only
after substituting a small numerical test tuple.

The resulting receipt is `verification/INDEPENDENT_COMPACT12_CHECKS_OPTIMIZED.json`. All checks
pass. They establish the circuit identities and size claims; the
mathematical arguments above, together with the explicitly imported
Pell/compiler results, establish the semantic equivalence.
