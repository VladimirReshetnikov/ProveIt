# One certificate for the Pell cap and every normalized digit remainder

Prepared 25 October 2026 for the ProveIt research task. This is an ordinary
unbounded arithmetic proof, together with a separate exact finite circuit
transformation. It proves an existential equivalence by canonical-witness
completeness. It does **not** assert a bijection between every old zero and
every new zero.

## 1. A general reciprocal-budget lemma

For integers a,b,c put `G(a,b,c)=a^2+b^2+c(c+1)`. This is nonnegative for
every integer triple, and every nonnegative integer has such a representation.
For the latter assertion, apply the three-square theorem to `4n+1`: it is
not of the excluded form `4^r(8s+7)`. Exactly one of its three square terms
has an odd root, by reduction modulo four. Writing the roots as `2a,2b,2c+1`
and dividing by four gives the assertion. This representation theorem and
the elementary argument are formalizable in ZFC.

Let U,V,E,R be integers with U>=0, V>=0, E>=1 and R>=0. Define

    H = U*V - U*E - V*R - 1.

If H>=0, then U,V are both positive. Indeed, U=0 gives `H=-V*R-1<0`, and
V=0 gives `H=-U*E-1<0`. Consequently

    U*(V-E)=V*R+1+H>0,
    V*(U-R)=U*E+1+H>0.

It follows that V>E and U>R. Since these quantities are integers, this
implies the two old requirements

    V-E >= 0,       U-R-1 >= 0.                         (1)

Conversely, for positive U,V the exact identity

    H/(U*V) = 1 - E/V - R/U - 1/(U*V)                  (2)

shows that H>=0 whenever the three fractions on the right sum to at most
one. Thus one ternary representation `H=G(a,b,c)` can replace two ternary
representations of the quantities in (1), provided the existence proof
supplies witnesses with the stronger joint budget. A negative or zero
denominator has not been assumed away: its exclusion follows from H>=0.

The strict constant `-1` is necessary to this bootstrap. Without it,
`U=V=0` would satisfy the nonnegativity condition and would not restore
either original lower bound.

## 2. Exact source instance

Source indices below refer to the frozen 219-coordinate equation
`sources/anchor219.json`. The following are actual semantic values, with
the translated ordinate explicitly identified:

    C=2*x16,       Q=x126,       Y=x184,
    U=Q^2,         V=Y^2,

    (y_1,...,y_13)=
      (x142,x151,x154-1,x157,x160,x163,x166,
       x169,x172,x175,x178,x181,x187),

    (r_1,...,r_10)=
      (x104,x108,x111,x114,x117,x121,x124,x128,x132,x135),

    E=C^2+1+sum(y_i^2),
    R=4*sum(r_j^2).

These definitions give U,V>=0, E>=1 and R>=0 without interpreting any
Pell pair, power, sign or digit. The exact literal source residuals 150
and 151 are

    V-E-G(x207,x208,x209),
    U-R-1-G(x210,x211,x212).                              (3)

The finite checker authenticates these identities coefficient by
coefficient against the frozen source. All six guard coordinates are
private to their respective rows; none occurs in a semantic coordinate
reconstruction or in any retained residual. This privacy is also checked.

Delete source coordinates 210,211,212. Reuse 207,208,209 as the sole new
ternary representation and replace the two rows (3) by

    U*V-U*E-V*R-1-G(x207,x208,x209)=0.                    (4)

The final polynomial is the sum of the squares of (4) and every retained
residual, after the parent's existing acyclic integral substitutions. It
has exactly three fewer independent integer variables and one fewer
squared residual. All new named values are polynomial expressions, not
additional quantified variables.

## 3. Soundness and noncircular restoration

Any integer zero of the new sum of squares makes (4) zero. The general
lemma yields (1) before any interpretation of the arithmetic front. The
three-square representation supplies a triple for V-E and another for
U-R-1. Replace the values of all six old guard coordinates by these two
triples. Their privacy leaves every other old equation unchanged; the two
equations (3) now hold.

For an already projected parent, its checked acyclic unit-pivot
reconstruction restores every eliminated source coordinate. None depends
on the six private guard coordinates. Hence this argument restores a zero
of the parent's literal source equation, including its Pell cap. The
parent's sign and index bootstrap is therefore available in its original
order. In particular, this proof never uses the cap's semantic conclusion
to justify the cap inequality itself.

The existing calibrated parent soundness theorem then gives a finite C222
refutation, and its named C222/ZF/ZFC calibration gives a finite syntactic
ZFC refutation. The new argument introduces no restriction to externally
standard codes and no assumption that ZFC is consistent.

## 4. Canonical-witness completeness

Start with a finite C222 refutation. Use package 173's canonical
completeness construction, followed by the parent's simultaneous
orientation-and-power certificate and selected unit projections. The
choices made before the main Pell frame give:

* a positive even anchor index C, strictly larger than every other
  principal index k_i;
* a positive main Pell center A and a square frame W, with W>=258,
  `A>W^W`, and `C^2<W`;
* `Y=Y_C(A)` and `y_i=Y_(k_i)(A)`, with `0<=k_i<C`;
* `Q=q^x>=2` and each canonical normalized remainder `0<=r_j<Q/32`.

The final bullet is part of the parent digit construction: true low
binomial tails are strictly below one thirty-second of their denominator,
and normalization multiplies each by the exact ratio between Q and its
denominator. The ten literal remainder ports are listed in Section 2.

Write `Z=Y_(C-1)(A)`. Since C>=2, one has Z>=1. The Pell recurrence gives

    Y_C(A) >= (2*A-1)*Y_(C-1)(A),

and monotonicity gives `0<=y_i<=Z`. Because `C^2+1<=W`, it follows that

    E/V <= (W+13*Z^2) / ((2*A-1)^2*Z^2)
        <= (W+13)/(2*A-1)^2
        < 1/2.                                         (5)

For the last inequality it suffices that A>W>=258, since then
`2*A-1>=2*W+1` and `2*(W+13)<(2*W+1)^2`. This does not require choosing
an additional asymptotic limit or modifying any earlier CRT witness.

The ten normalized remainders give

    R/U < 4*10/32^2 = 5/128.                            (6)

Finally `Q>=2` implies U>=4. Since C>=2 and A>=2, the recurrence gives
`Y_C(A)>=Y_2(A)=2*A>=4`, so V>=16. Consequently

    1/(U*V) <= 1/64.                                   (7)

Combining (5)--(7),

    E/V+R/U+1/(U*V) < 1/2+5/128+1/64 = 71/128 < 1.

Equation (2) now gives H>0, in particular H>=0. Represent H by one
ternary G. This supplies the sole new guard triple and hence a zero of
the new equation. Every parameter is chosen in the original acyclic
completeness order: the CRT representatives and powers first, the main
Pell frame after them, and the new ternary representation last.

## 5. Consistency equivalence

Sections 3 and 4 prove, in ordinary mathematics formalizable in ZFC,

    exists integer zero of the new polynomial
      iff exists a finite C222 refutation
      iff exists a finite syntactic ZFC refutation.

Negation gives the requested equivalence between lack of integer zeros
and Con(ZFC). The last equivalence uses the inherited declarations
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The new bridge is
an ordinary mathematical proof; no new end-to-end proof-assistant build
or emitted object-language ZFC proof is claimed.

The change is a strict strengthening of the simultaneous numerical
inequalities at a particular old witness. Therefore canonical-witness
completeness is material: merely multiplying the old two slacks would
not prove the result, and a pointwise polynomial inverse is not claimed.

## 6. Explicit projected endpoints and verification

The source byte bindings, complete finite arithmetic circuits and all
independent-variable orders are in `equations/`. Each circuit has only
integer literals, independent integer variable leaves and binary addition,
subtraction and multiplication. Its `output` node is the single polynomial;
its `residual_roots` are the polynomial expressions whose squares are summed.

|Integer variables|Exact degree|Residuals|Live binary operations|
|---:|---:|---:|---:|
|106|32|47|1830|
|82|16964|23|1723|
|81|2097732|22|1711|

These figures compose guard fusion with the separate linear-orientation
refinement. Its complete proof is `LINEAR_ORIENTATION.md`. The new seed identity and
its exact pullback through every inherited unit pivot are independently
verified before the guard-fusion check. The maximum literal absolute value and conservative
expanded coefficient-height bounds of these profiles remain
the parent's values. They are not global minima. Other repository
architectures use far fewer variables with much larger literal constants.

The independent checker imports neither producer nor parent search code.
It checks source guards, private-coordinate occurrence, every preserved
polynomial expression, the literal new guard, output square list, degree
upper bounds, a nonzero top homogeneous coefficient modulo 1000000007,
and nonzero partial derivatives proving every declared input actually
occurs. Forward differentiation in the checker is independent of the
producer's reverse differentiation. Fifteen altered artifacts are rejected.
Normal and optimized Python runs perform the same substantive checks.

The finite checks complement the unbounded proof above. They do not
decide consistency or establish number-theoretic theorems by examples.

## 7. Scope of novelty and inherited dependencies

This note combines the previously separate signed Pell cap and normalized
digit-remainder budget by one strictly positive reciprocal budget. The
idea is independent of the particular numerical calculus. The inspected
sources already contain pooling among remainder predicates and pooling
among power predicates. The claimed new repository contribution is this
cross-stage cap/remainder application and its explicit projected outputs.
No literature-wide priority claim or global simplest-equation theorem is
made. The complete historical dependency closure belongs to the pinned
ProveIt sources; the new finite checker authenticates the immediate
parent artifacts without pretending to reprove their unbounded calibration.
