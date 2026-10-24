# Project first, pad second, and flatten last

This note proves the new source transformation used by `build_direct.py`.
It concerns the direct C222 proof-rule compiler, not a Turing-machine encoding
or a universal Diophantine polynomial. The inherited source is the supplied
`horn_shared_source.json`, whose twelve branches are independently bound to
`Code254`/`KCode222` in the round-12 source audit. All variables before the
final unrestricted-integer conversion range over the nonnegative integers.

## 1. Deterministic coordinates should not cross the bounded quantifier

Suppose a disjunctive polynomial presentation is

    exists z: product_b [ sum_j (z_j-F_bj(parameters,z_<j))^2
                         + sum_l G_bl(parameters,z)^2 ] = 0,

where each branch's F_bj is a nonnegative polynomial in earlier coordinates.
Different branches may share the same existential names. Because a product
of integers is zero precisely when a factor is zero, the existential
quantifier distributes over the finite disjunction. In a chosen branch its
defining equations determine the z_j uniquely and give natural values by
topological induction. Therefore one may substitute those values into that
branch and delete every defining equation. Conversely any zero of a
substituted branch lifts by its canonical constructor values. Values of
unselected branches impose no constraint.

The old C222 row had thirteen shared constructor coordinates. This lemma
removes all thirteen before CRT compilation. Keeping these intermediate
values at that stage was expensive: every bounded coordinate required a
binomial certificate and three power representations. The eventual quartic
compiler introduces ordinary arithmetic wires only after the bounded family
has been eliminated. Thus projecting these coordinates does not sacrifice
degree four in the final equation.

## 2. Premise and conclusion labels are also deterministic

Write I(a,b)=2(a+b)(a+b+1)+4b, and A(a,b)=I(a,b)+2. Let h_b denote the
explicit conclusion polynomial of an axiom branch after its constructor
substitutions. Each C222 rule can be parameterized using only the four
shared parameters a,b,c,d as follows:

| Branch | First premise p | Second premise q | Conclusion v | Remaining guard |
|---|---:|---:|---:|---|
| truth | 0 | 0 | 0 | none |
| rho1,...,rho6,growG,rho8 | 0 | 0 | h_b(a,b,c,d) | none |
| bundle | 0 | 0 | h_bundle(a,b,c,d) | ((c-a)(c-b))^2=(d+1)^2 |
| modus ponens | a | I(a,b) | b | none |
| generalization | b | 0 | A(a,b) | none |

This is a reparameterization of exactly the original rules. In particular,
the generalization parameter is independent of its premise, and the bundle
condition has not been weakened to an inequality of arbitrarily chosen
sign. Its square equation is equivalent to c!=a and c!=b for some natural
d, including both signs of (c-a)(c-b).

The labels p,q,v can now be substituted in each branch's accumulator
equation. The two beta reconstructions do not depend on which branch is
selected, so remain outside the disjunction. Each branch contains only
its guard and its particular accumulator equation. This deletes the three
label coordinates while preserving both directions of the existential
source equivalence.

Every remaining label polynomial has nonnegative integer coefficients.
This follows directly from the displayed I and A constructors and the
positive constructor-wire coefficients, and is verified structurally for
all twelve literal branches by `check_projection.py`.

## 3. A zero-balance rule makes the horizon a parameter bound

Let a finite C222 derivation of the target label 1 be fixed. Expand it to
a finite proof tree and list its rule instances in an order that expands
an outstanding conclusion to its premises. There are finitely many rule
parameters a,b,c,d in this list. Choose N at least the number of these
instances and at least every parameter value. Pad the list to exactly N
instances with the truth rule (p,q,v)=(0,0,0), taking its four parameters
to be zero. This rule has zero balance when label zero is ignored. It also
leaves the product accumulator unchanged.

For each rule b, let p_b(t),q_b(t),v_b(t) denote its three label
polynomials evaluated at a=b=c=d=t, and define the explicit nonnegative
polynomial

    H(t) = sum_b [p_b(t)+q_b(t)+v_b(t)].

Whenever the four parameters of a rule are bounded by N, monotonicity gives
each of its labels <= H(N). We choose

    M0 = 2^(2 H(N) N + 1),       M = M0+1.

The exponentiation here is only explanatory notation: the emitted ordinary
polynomial uses the inherited finite power certificate. This choice is
made after the padded horizon N and before the accumulator trace. The
old outer label-bound variable m and all three per-row label-bound slacks
are unnecessary. At this intermediate stage the local row has ten coordinates. Section 6
removes two beta-bound slacks, leaving eight coordinates in the released form.

This is an existence-preserving padding argument, not an assertion that
an arbitrary original certificate already satisfies the new bounds. In
particular, there is no bound on the length or parameter size of a possible
refutation, and no bounded-consistency substitute for Con(ZFC).

## 4. The large-base balance test remains exact

For a candidate sequence of N valid rule instances write their labels as
p_i,q_i,v_i, and put

    A(X) = product_i (1+v_i X),
    B(X) = (1+X) product_i (1+p_i X)(1+q_i X).

If all labels are at most h=H(N), then A(1)<=(h+1)^N and
B(1)<=2(h+1)^(2N). The elementary inequality h+1<=2^h for every natural h
shows that every coefficient of A-B has absolute value at most M0<M.
Consequently A(M)=B(M) implies the polynomial identity A=B: if the least
nonzero coefficient has index j, divide the evaluation by M^j and reduce
modulo M. This would make that nonzero coefficient divisible by M,
contradicting its magnitude bound.

The accumulator starts S_0=M+1, ends S_N=1, and each selected row imposes

    S_(i+1)(1+v_i M)=S_i(1+p_i M)(1+q_i M).

All label factors are positive. Since S_0>0, induction gives every S_i>0.
Telescoping therefore yields A(M)=B(M). Distinct positive labels j give
distinct roots -1/j of the primitive linear polynomials 1+jX. Comparing
their multiplicities in A=B gives the exact nonnegative Horn balance

    sum_i (e_(v_i)-e_(p_i)-e_(q_i)) = e_1,

where e_0 is interpreted as zero.

For completeness, let D be the least closure of the finitely supported
selected rule instances, with zero available as the truth label. If 1 were
outside D, apply the linear functional summing balance coordinates outside
D. Every rule contributes at most zero: an outside conclusion must have
at least one outside premise, while an inside conclusion contributes no
positive term. The target contributes one, contradiction. Thus the target
is derivable. This argument explicitly allows cycles, repeated premises
and self-loops, and requires single-conclusion rules and nonnegative rule
multiplicities, both of which hold here.

Conversely a proof-tree expansion gives integral S_i as the product of
1+jM over currently outstanding nonzero obligations. Expanding one
obligation replaces its factor by those of its premises, so the displayed
update holds. At the end the empty product is one. Padded truth rows leave
this value unchanged. This proves exact equivalence between refutability
and the new bounded-family certificate.

## 5. Fixed coordinate bounds: the sharpened CRT lemma

Let e,f be polynomials with nonnegative integer coefficients in an index k,
fixed outer parameters, and r natural row coordinates. Let N and a specified
bound vector u=(u_1,...,u_r) be fixed. Choose any natural
L>=e(N,u)+f(N,u)+N, and put

    T=L!,
    d_k=1+(k+1)T,           B=product_(k<N) d_k.

Then the following are equivalent:

1. For each k<N there is w with 0<=w_j<=u_j and e(k,w)=f(k,w).
2. There are natural encoded coordinates a_j and an index c such that
   B divides (u_j+1)! binomial(a_j,u_j+1) for every j,
   B divides 1+(c+1)T, and e(c,a)=f(c,a) modulo B.

Proof of soundness. For k<N choose a prime p dividing d_k. The case N=0
is vacuous. Since d_k=1 modulo T, p does not divide T and hence p>L.
The falling-factorial condition gives t_j<=u_j for which p divides the
natural truncated difference a_j-t_j. Set w_j=min(a_j,t_j). Then
w_j<=u_j and a_j=w_j modulo p. The index condition, together with
d_k=0 modulo p and the invertibility of T, yields c=k modulo p. Hence
e(k,w)=f(k,w) modulo p. Monotonicity gives
e(k,w)+f(k,w)+N<=L<p, so these two nonnegative values are actually equal.
The minimum in the definition of w_j is essential when a_j<t_j; it
avoids silently replacing truncated subtraction by signed subtraction.

Proof of completeness. The d_k are pairwise coprime: any common prime
dividing d_i,d_j divides (j-i)T but not T, hence divides 0<j-i<N<=L and
therefore divides T=L!, contradiction. Choose c=k modulo d_k and
a_j=w_(k,j) modulo d_k by CRT. Each falling factorial has the factor
indexed by w_(k,j)<=u_j, hence is divisible by d_k; if the encoded value
is smaller than that index, the natural factor is zero and divisibility
still holds. Polynomial evaluation preserves the congruences, so all
required divisibilities hold modulo the product B.

This bounded-vector refinement is proved by the same decoding argument as
the inherited `boundedForallCertificate`; its explicit coordinate bounds
are needed here to justify H(N). Merely citing that theorem's weaker
unbounded conclusion would omit a required step.

## 6. Eliminate the beta slacks and cancel the factorial factors

The released local row has eight coordinates, ordered as

    (a,b,c,d,S,q,S_next,q_next),

with the fixed heterogeneous bound vector

    u=(N,N,N,N,y,U,y,U).

The two beta reconstruction rows are only

    x=q(1+(i+1)y)+S,
    x=q_next(1+(i+2)y)+S_next.

No per-row remainder-bound slacks remain. Indeed the fixed-vector CRT
lemma yields S,S_next<=y, and y<1+(i+1)y for all natural i,y. Thus the
reconstructions already give the unique ordinary remainders. This also
covers y=0. Both adjacent rows recover the same accumulator entry, and
the separately represented endpoints recover S_0=M+1 and S_N=1.

For completeness, once the proof, padded N and M have been fixed, choose
y strictly above all accumulator entries and divisible by N!. CRT supplies
a natural x representing the complete finite trace. Its canonical
remainders are all at most y. Choose U above the finitely many quotient
values. The dependency order remains

    proof tree and parameters -> padded N -> H(N), M -> accumulator trace
    -> y and x -> U -> T, B and encoded columns.

In particular U does not determine M. This replacement may select a
larger y than in an arbitrary earlier certificate; the completeness
construction recomputes the beta code accordingly.

Now choose the slightly larger factorial argument

    L=e(N,u)+f(N,u)+N+U+y+1,    T=L!.

It still satisfies the hypotheses of Section 5. For each coordinate bound
b in {N,U,y}, one has b+1<=L, hence F_b=(b+1)! divides T. Every modulus
d_i=1+(i+1)T is 1 modulo T, so their product B is also 1 modulo T.
Consequently B=1 modulo F_b and gcd(B,F_b)=1. Euclid's lemma gives the
exact cancellation

    B | F_b binomial(a,b+1)  iff  B | binomial(a,b+1).

The released range certificates use the right-hand side. The inherited
prime extraction argument can be applied after restoring the harmless
factor F_b by multiplication. Conversely the CRT-constructed certificate
from Section 5 has the left-hand divisibility and therefore the cancelled
one. No statement about the size or primality of B is assumed. The case
B=1 is included.

The CRT product formula remains

    Q=(1+(N+1)T)^N+2,
    B=(T^N N! binomial(Q+N,N)) mod(TQ-1).

Its divisor is positive. The only remaining factorial calls are T=L! and
N!, which is required by that product formula. In particular no factorial
(U+1)! or (y+1)! is represented. The ability to enlarge T in a controlled
way removes an entire factorial graph as well as the two bounded columns.

## 7. Literal evidence and quantitative scope

The natural circuit has 1,469 semantic inputs, 40 power calls, 40 Pell
calls, 27 division calls, 11 binomial calls and two factorial calls.
The old fixed-base circuit had 3,960 semantic inputs and 108 power calls.
These are literal compiler counts, not asymptotic complexity or a claim
about a smallest possible Diophantine equation. Final signed-compiler and
quartic counts are measured separately.

`check_projection.py` imports no builder. It checks the defining rows,
all twelve canonical rule substitutions, the retained bundle guard, the
entire local polynomial, the explicit majorant, all three coordinate-bound roles and both evaluation
environments, endpoints, the enlarged factorial argument and every
cancelled-factorial coordinate certificate, and the factorial,
power, division and congruence interfaces by exact compositional identities.
It does not enumerate tuples to infer a universal theorem. Its result is
`PROJECTION_CHECK.json`. The source's high local degree is harmless to the
final graph quartic, but does affect the semantic magnitude of witnesses;
no claim of small refutations or small witness heights is made.

Composing this source transformation with the inherited arithmetic
representation theorems and the exact C222-to-ZFC refutation bridge gives
the required ordinary proof, formalizable in ZFC, of the no-zero/Con(ZFC)
biconditional. This does not claim an emitted object-language proof file
or a new Lean/Rocq kernel certificate.
