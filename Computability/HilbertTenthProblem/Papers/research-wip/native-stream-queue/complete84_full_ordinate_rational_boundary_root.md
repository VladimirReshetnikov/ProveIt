# Rational reconstruction of the auxiliary ordinate on its full independent boundary

Every fixed rational formula for the auxiliary ordinate y, using all99
existing y-independent values of the complete84 source, can hold at full
positive parent zeros for only finitely many ordinary inputs on a fixed
valid compiler slice. The statement includes the auxiliary quotient T and
all five computed T-dependent values in that boundary. It extends the
prior93-value polynomial ordinate theorem; it does not change the source,
operation count, witness count or degree.

For a literal rational substitution, the same conclusion applies at zeros
where its denominator is nonzero and its reconstructed ordinate is an
integer, even if that integer is negative. These domain conditions are
explicit. Arbitrary zeros after clearing a denominator are not asserted
to satisfy them.

## 1. Actual source interface and precise bound

Use the unchanged source in complete84_scaled_strong_output.json. Its
25 supplied ports include the strictly positive witnesses
T=auxiliary_quotient and y=y_aux. Its mathematical abbreviations are

    c=R10a, R=r_lhs, Delta=A,
    S=aux_coefficient_root=Delta*i*c^2, Q=R16=S^2,
    V=aux_u_rhs=c*T*f-c-R*f^2,
    Na=Q*V^2-(Q-1)*y^2,
    Ns_scaled=Delta*f^2-Q,
    F84=P5*Na*Ns_scaled-Delta.                         (1)

P5 denotes the product of the five unchanged first/main/input/index/
transport factors. These are proof abbreviations for paid definitions.
The full source is still84=47M+37A with18 positive witnesses.

The existing E93 boundary has70 computed and23 supplied values independent
of both T and y. Removing only y leaves75 computed and24 supplied values:
E99 consists of E93 together with T and exactly these five extra rows:

    auxiliary_Tf           = T*f,
    auxiliary_Tf_minus_one = T*f-1,
    auxiliary_c_Tf         = c*(T*f-1),
    aux_u_rhs              = c*T*f-c-R*f^2,
    H2                     = (c*T*f-c-R*f^2)^2.          (2)

The old E93 already includes auxiliary_R_f2=R*f^2. None of the99 named
arguments is a new free port, and their literal dependencies are retained.
The accompanying metadata checks every row's dependency names, the two
censuses and the exact five added records, without evaluating arithmetic.

Fix integer polynomials P,H in these99 formal arguments. H must evaluate
to a nonzero integer at each considered tuple. Let

    t=max(deg(P),deg(H)),
    Lp=sum of absolute coefficients of P,
    Lh=sum of absolute coefficients of H,
    K=4^(2t)*(Lp^2+5*Lh^2)+1,
    C=12t+13+ceil(log2 K).                              (3)

Combine formal like monomials before measuring these quantities. Give the
zero polynomial degree0 and norm0. H(actual)!=0 implies H is not formally
zero, so Lh>=1 and K>=6. Coefficients and the two formulas are fixed as
ordinary input and witnesses vary; they may depend on the fixed compiler.

**Theorem.** At any full positive parent zero satisfying

    H(E99)!=0,    y=P(E99)/H(E99),

one has

    2*d_native*x+b_source < R < C.                       (4)

The same bound holds if y=abs(P/H) instead. Thus a fixed finite family
of such formulas has finite ordinary-input projection. There is no claim
that C is sharp or that the possible finite input range is empty.

## 2. Inherited positive-zero facts and exact source growth

The accepted ordinate theorem and its independent review establish at
every full positive parent zero on the unchanged valid compiler slice:

    Na=1, Ns_scaled=Delta,
    2*d_native*x+b_source<R, R<c<f, Delta<c<f,
    f>=2, Q< f^3,
    abs(E_j)<=f^3 for every E93 value E_j.               (5)

The actual positive domains and fixed mask recipe are required here.
The signed-quotient theorem, which includes these positive tuples, also
proves

    T > f^(R-4).                                       (6)

Its proof uses the auxiliary index ell>=R and |V|>f^(R-1), together
with |V|<f^2*|T|+f^3. The authentic index has R>=5; if
|T|<=f^(R-4), these inequalities would force
|V|<f^(R-2)+f^3<=2f^(R-2)<=f^(R-1). Thus (6) concerns every auxiliary
completion, not a chosen canonical lift. No power in this argument is
claimed as a free source operation.

Freeze the actual E93 integer values at this particular parent zero and
write z for the formal variable replacing T. This is a proof construction;
it does not claim source equations hold after varying T. Put

    a0=c*f, b0=c+R*f^2, v(z)=a0*z-b0.

By integrality in (5), c,R<=f-1, so

    0<a0<f^2, 0<b0<f^3, ||v||_1=a0+b0<2f^3.             (7)

Replace T and the five displayed arguments (2) by their explicitly
written integer polynomials in z. All93 other arguments stay fixed.
Every one of the99 resulting polynomials has coefficient norm at most
4f^6: old constants have norm<=f^3; z has norm1; the first three new
polynomials have norms at most f+1 or cf+c; v has norm<2f^3; and v^2
has norm<4f^6. All coefficients are integers.

Applying this handwritten substitution to the fixed formal P,H gives
integer polynomials p(z),h(z) with

    ||p||_1 <= Lp*4^t*f^(6t),
    ||h||_1 <= Lh*4^t*f^(6t).                           (8)

Coefficient cancellations and dependencies among the source arguments
can only decrease these upper bounds. As h(T)=H(actual)!=0, h is not
the zero polynomial even when specializing the dependent ports lowers
its degree. The source arrays themselves need not be expanded to prove
(7)--(8).

## 3. A nonzero integer root polynomial

The auxiliary unit in (5) gives

    (Q-1)*y^2 = Q*v(T)^2-1.

Thus the positive integer T is a root of

    J(z)=(Q-1)*p(z)^2-[Q*v(z)^2-1]*h(z)^2.              (9)

This also holds when y=abs(P/H). The polynomial J is nonzero.
Indeed Q=S^2 with integer S>1 and a0>0. The quadratic Q*v(z)^2-1
has the two distinct rational roots

    z=(S*b0+1)/(S*a0),   z=(S*b0-1)/(S*a0).

Each root is simple. If J vanished identically and p were nonzero,
at either root the left side (Q-1)*p^2 would have an even zero order,
while [Q*v^2-1]*h^2 has odd zero order. Equality is impossible. If p
is the zero polynomial then the right side is a nonzero product,
also impossible. This argument works after every allowed specialization;
it does not assume a generic numerator, denominator or exterior tuple.

From (7), Q<f^3 and f>=2,

    ||Q*v^2-1||_1 <= Q*||v||_1^2+1 <4f^9+1<=5f^9.

Using (8) and Q-1<f^3 in (9) therefore gives

    ||J||_1 <= 4^(2t)*(Lp^2+5*Lh^2)*f^(12t+9).

A nonzero integer polynomial has leading coefficient of absolute value
at least1. The elementary Cauchy root bound gives

    T <= 1+||J||_1 <= K*f^(12t+9).                       (10)

For completeness, if M is the largest absolute lower coefficient divided
by the leading coefficient and r>1+M, the sum of lower absolute terms
is at most |leading|*M*(r^n-1)/(r-1)<|leading|*r^n; such an r cannot be
a root. A constant nonzero polynomial has no root, so that degree-drop
case is already excluded when applying (10).

Combining (6) and (10), if R>=12t+13+ceil(log2 K), then

    f^(R-4) >= f^(12t+9)*2^ceil(log2 K)
             >= K*f^(12t+9) >= T,

contradicting (6). This proves (4).

## 4. Literal substitutions, signs and the pole boundary

For a literal replacement y=P(E99)/H(E99), keep every other original
supplied witness positive and consider only tuples at which H!=0 and
the quotient is integral. If its value g is nonzero, the source's sole
direct y consumer is y*y. Replacing g by |g| gives a full positive
parent zero and leaves every E99 argument unchanged. The theorem then
applies through the squared relation (9).

If g=0, the accepted source-specific zero-ordinate identity is

    F84|y=0 = Delta*(Delta^2*i^2*c^4*V^2*P5
                    *(f^2-Delta*i^2*c^4)-1).

Delta>=8 before any equation, and all bracketed terms are integers.
Its product before subtraction is divisible by Delta^2 and cannot equal1.
Thus this zero sector is empty without invoking parent soundness at y=0.
For H=1, integrality is automatic, so every fixed integer-polynomial
substitution on the full99 boundary has finite whole input projection.

**Remark 1 (clearing a denominator does not restore its domain).** No
claim about all zeros of a denominator-cleared polynomial follows merely
from (4). Even the elementary relation y=1/u has empty defined domain
at u=0, while multiplying a constraint by u can add every tuple with
u=0: for example u*(y-1)=0 allows u=0,y=2 although y-1 is nonzero.
A proposed division-based compiler must retain its nonzero-denominator
and integral-output obligations. They are not paid by this theorem.

**Remark 2 (the ordinate result does not extend to every witness).**
The existing all91 rational-root scout gives a fixed rational formula
recovering f at every original positive zero by using T,y,y^2. Its
subsequent complete elimination yields the separate90-operation,
17-witness construction. Thus a blanket assertion that no witness has
a fixed rational reconstruction would be false. Here y is excluded from
all99 arguments; the simple-root argument applies to this exact interface.

**Open question 1.** A cheaper complete compiler could change the auxiliary
equation, replace several coordinates together, or add different unbounded
structure. This theorem does not address those possibilities or supply an
operation lower bound. It excludes fixed finite rational reconstructions
of this ordinate on the retained99-value interface as a route preserving
an unbounded input language.

## 5. Evidence scope

The proof uses the full positive-zero interfaces of the frozen
complete84_auxiliary_ordinate_absorption.md and its independent review,
and the signed-quotient growth theorem. The preceding strong-root
rational E88 argument already appears inside Section7 of
complete84_full_independent_root_absorption.md; it is not claimed as a
new result here. The present boundary and eliminated ordinate differ.

Only fresh inline source-name/dependency/consumer/count metadata is used
to authenticate E99 and (2). Saved source instructions are never
numerically or symbolically evaluated, and no degree is propagated.
No supplied, predecessor, archived, committed or frozen scientific helper
is executed or imported. No large native witness or compiler zero is
materialized. Dependency hashes and exact read spans are recorded in the
companion metadata receipt, separately from the all-size mathematical proof.
