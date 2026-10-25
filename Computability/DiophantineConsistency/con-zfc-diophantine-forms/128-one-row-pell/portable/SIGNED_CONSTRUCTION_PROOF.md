# The 378-integer construction: exact proof schedule

## Literal objects and inherited boundary

The final polynomial is the sum of the squares of all 230 rows of
`integer378/equation.json`, in the exact order of its 378 unrestricted
integer coordinates. The complete collected polynomial is
`integer378/expanded_polynomial.json`. Its degree is four, it has 9,421
nonzero monomials, and its coefficient height is 3,054,220.

The immediate natural arithmetic body has 359 coordinates and 307 rows;
it is supplied in `integer378/natural_raw/equation.json`. It contains six
exact-power requests, eleven modular numerator requests, one exact binomial,
one factorial fixed point, and fifteen independent Pell indices. Its
factorial binomial is literally the reciprocal CRT product binomial. The
retained shared-binomial proof supplies the arithmetic and C222/refutation
interpretation once these finite requests have their stated meanings.
The new cap replaces its private simultaneous indexed-Pell certificate.

The logical boundary is the inherited ordinary interpretation associated
with `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. This packet does not
assert a newly compiled Lean or Rocq endpoint. All new arguments use integer
polynomials, induction, elementary Pell theory and finite arithmetic, and
are formalizable in ZFC. No consistency assumption is used.

## 1. The signed source and its domains

`integer378/source.json` has exactly the same variables and residuals as the
359-variable natural body, with their domain changed to unrestricted integers.
It is not asserted equivalent merely by this domain change. We append exactly
36 scalar nonnegativity graphs and twelve product nonnegativity graphs.
Every graph is the quadratic identity

    H = a^2 + b^2 + c(c+1),       a,b,c in Z.

The right side is nonnegative. Conversely it represents every nonnegative
integer: apply Legendre's three-square theorem to 4H+1, whose square roots
have one odd and two even parities, and divide the resulting identity by four.
Thus it realizes H>=0 existentially, using three private integer variables.

For a scalar graph, H is the selected old coordinate. For a pair graph,
H=rs is the product of the remainder and complementary slack of one
factorial or modular remainder bound. The complete row/coordinate lists are
`integer378/signed_certificate.json` and `GUARD_TABLE.tsv`. There are no
implicit sign assumptions. The guarded source has 503 variables and 355 rows.

## 2. Noncircular prefix

The ordinary arithmetic frame is doubled:

    W = 2 (2 + sum of all distinct semantic atoms).

The atoms include the bases, exponents and outputs of the six exact powers,
and the upper indices of every modular numerator. Those modular indices must
be included: their magnitudes are not bounded by the old exact-power frame
before the powers have been interpreted.

All six proposed power outputs retain scalar nonnegativity guards. Four of
these guards become essential when the denominator remainder signs are
postponed: otherwise those signs would have been used to deduce that the
denominators, and hence the frame, were nonnegative. This would be circular.
The four added guards are explicitly recorded in the certificate.

The literal sign-inference certificate has 250 exact identities. Before
using any seed-root or quotient semantics, 226 source coordinates are proved
nonnegative from the retained scalar guards. Each deduction is either
cv=P with c>0 and P a positive-coefficient polynomial in already
nonnegative odd-power factors, or cv=L^2 for an exact affine L. The
independent audit also checks the actual frame-atom expansions and positive
seed expressions. In particular every requested seed k satisfies

    1 <= k < W/2,        m=15 <= W-2,

and W is even. The private scale and single-anchor certificate keep their
ordinary nonnegative domains throughout this prefix.

Writing A=L+sigma, with sigma>=0, the scale norm is

    L^2 - ((W+1)^2-1) (W Z)^2 = 1,       Z>=1.

Pell classification and the congruence Y_j(W+1)=j modulo W give
L>=X_W(W+1)>=(W+1)^W. Consequently A-1>W^3. The target source has
t>=16, so all small-W exceptions are excluded.

## 3. One anchor recovers both signs of every seed pair

The principal seed norms are

    X_i^2 - (A^2-1) Y_i^2 = 1.

No separate sign graph is attached to any of the thirty coordinates X_i,Y_i.
Instead one complete ordinary indexed-Pell certificate at W supplies an
anchor ordinate V, and the new single row is

    V = W + sum_i ((X_i-1)^2 + (Y_i-k_i)^2) + (A-1) Q,
    Q >= 0.

The Q sign is one of the retained scalar guards. This row gives V>=W,
the only lower-bound premise the anchor's indexed certificate needs. Its
other natural domains were already established, so V=Y_W(A).

The full-root cap lemma proves

    X_i=X_(k_i)(A),       Y_i=Y_(k_i)(A)>0.

For clarity, its mechanism is as follows. Write W=2B. Pell classification
represents an arbitrary signed principal pair by signs times the canonical
pair at some j>=0. The error bound supplied by the single row excludes
j>B: (Y_(B+1)(A)-k_i)^2>Y_(2B)(A). Reducing modulo A-1 turns the
error summands into (epsilon_X-1)^2+(epsilon_Y*j-k_i)^2, with the
usual harmless j=0 convention for the zero ordinate. Their nonnegative
sum is smaller than W^3<A-1 and is divisible by A-1. It must vanish.
Thus the abscissa sign is positive and epsilon_Y*j=k_i>0.

Completeness follows by taking the canonical pairs. Their squared errors
are congruent to zero modulo A-1. Pell growth makes their sum plus W
strictly smaller than Y_W(A), so the displayed row defines a nonnegative
integer Q. The complete inequalities are given in the manuscript and
the separate cap-lemma proof. The residue condition and its size bound
are both necessary; neither finite testing nor a small-residue assumption
on the enormous Pell ordinates is used.

## 4. Recover the six exact powers before remainder signs

All proposed power outputs m are nonnegative and are frame atoms. A request
has the two literal equations

    T_n = 2 A n - n^2 - 1,
    X_k(A) + (n-A) Y_k(A) = m + T_n h.

The quotient h is currently unrestricted. Once n>=1, the large-frame
inequality implies T_n>W^W+W. The recurrence gives the residue n^k
modulo T_n. Both m and n^k are nonnegative and smaller than T_n;
therefore m=n^k. Moreover X_k+(n-A)Y_k>0, since
X_k>(A-1)Y_k. The equation then forces h>=0: h<=-1 would make the
right side at most m-T_n<0. This proves the signs of the four distinct
base moduli and all six power quotients without their old scalar guards.

Positivity of the bases is recovered in an explicit order. The first two
bases are F^2+1>=1 and B=b0+2>=2. Hence the power N=B^K is positive.
The third request then gives q=N^K>0. The remaining three requests,
all at base q, give the positive denominators q^t,q^(y+1),q^(x+1).
The extra q^(t+1) denominator is their retained multiplication q*q^t.
All exponents are positive from the prefix, independently of factorial or
binomial meanings.

In particular q=B^(K^2), with K>=2 and B>=2, so q>B+1. The ordinary
output-bound row q=B+o+1 therefore implies o>=0. Its scalar guard was
removed, but its defining row was retained.

## 5. Recover twelve pairs of remainder signs

Each modular remainder pair satisfies a literal bound

    d = r+s+1,

where d is one of the positive exact denominators just recovered.
The factorial pair has the same identity with d=B>=2, independently
of B's future binomial interpretation. Each pair has its own retained
product guard rs>=0. Since r+s=d-1>=0, these two facts force
r,s>=0: if either were negative, the other would be positive and their
product negative. This argument restores all 24 omitted scalar signs.
There is one factorial pair and eleven modular pairs. Their product
predicates are separate; their twelve products are not combined into
one product.

## 6. Restore the modular quotient signs

Put b=q+1. The common-root row is

    2 A b = b^2+1+M h0.

Here M is a product of positive exact denominators. Since A>W>b,
its numerator 2Ab-b^2-1 is positive, and h0>0 follows. Thus that
discarded scalar sign is restored without using any binomial semantics.

For a modular numerator, the canonical Pell pair gives

    R_n = X_n(A)+(q+1-A)Y_n(A)>0.

In the exact digit row, the candidate residue is r+dB with
0<=r<d and 0<=B<q; it lies in [0,qd). In a divisibility row,
the candidate residue r lies in [0,d), hence in [0,Nd), since N>=1.
The quotient equation R_n=residue+modulus*h now forces h>=0.
This recovers all eleven modular quotient signs from the already recovered
denominators, the twelve pair predicates and the output-bound identity.
No carry-free binomial argument is needed for this sign step.

## 7. Restore the whole old natural body

After adjoining precisely the signs proved in Sections 3-6, the same 250
literal sign identities recover every one of the 359 source coordinates
as nonnegative. Thus an arbitrary integer solution of the new guarded
source is an actual solution of the full natural arithmetic body, with
the same body coordinates. The proof uses the full source, not an
informal subset of intended interface values.

That body now has its six exact powers and all canonical modular Pell
pairs. The inherited shared-binomial argument recovers the exact
binomial B, the factorial F=t!, the reciprocal CRT product, every range
condition, and the bounded C222 refutation. Its calibration gives a ZFC
refutation. Conversely a finite refutation supplies the semantic values;
choose the doubled frame, a cofinal common Pell base satisfying the root
congruence, canonical seed pairs, the one-anchor witnesses and Q. Every
scalar and product predicate is then nonnegative, so fresh Legendre
triples extend the body to the guarded integer source.

## 8. Complete polynomial contraction

The final compiler performs 125 monic integral substitutions z=P. Every
P is an integer polynomial of degree at most two; its substitution into
every retained row keeps that row quadratic. The supplied inverse
certificate restores every deleted coordinate. There are no unconstrained
deletions in the selected 378-variable projection. The subsequent integral
translation is a polynomial bijection, with its shifts supplied literally.

Consequently the new guarded source, the projected system, and the final
230-row system have equivalent integer solvability. A sum of integer
squares vanishes exactly when each residual vanishes. Composing the two
directions above proves in ZFC that absence of integer zeros of the
explicit quartic is equivalent to Con(ZFC).

The finite checker reconstructs every inverse, every translated row, all
250 sign identities and every coefficient of the quartic. These finite
checks support the exact emitted object; the unbounded arithmetic proof
and named logical calibration supply its meaning.
