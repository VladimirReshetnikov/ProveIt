# Canonical membership vacuity does not recover full logical vacuity

## Proposition

Let kappa(a,b)>max(a,b), including kappa(a,b)=a+b+1 or any of the
positive native-tag constructors. Retain all eight logical rho rows,
modus ponens, theorem GEN, and even full primitive equality vacuity.
Replace membership vacuity by only

    R(a,b) -> All_kappa(a,b) R(a,b).

Then full membership vacuity is not derivable from this logical basis.
The same conclusion holds if several such large-binder builders are supplied.
It even holds after adding own-formula-code vacuity A->All_enc(A) A
for finite encoded formulas, with the native code-zero case treated as Truth.

This is an obstruction to a proposed logical bootstrap. It is NOT a
countermodel of the K axioms, and it does not prove that the full modified
K proof-search calculus has smaller consistency strength. A K-dependent
repair would require a new argument.

## Countervaluation

Take the nonempty domain D={0,1,2}. Worlds are assignments v:N->D.
Quantifier All_i is ordinary universal quantification over coordinate i.
Equality is ordinary equality of the coordinate values. Interpret the
membership atom by the assignment-dependent clause

    val_v(R(i,j)) iff v_i != v_j and v_i != v_0 and v_j != v_0.

Implication is material implication. Thus F=R(0,0) is false at every
assignment. The literal derived negation, conjunction, and existential
constructors therefore have their usual Boolean meanings. Native truth
code0 is interpreted as True.

This is a semantics for the numerical logical schemas. It deliberately
is not ordinary first-order semantics for a fixed binary membership
relation: membership also has a hidden coordinate-0 parameter.

At a fixed assignment let S_v(x,y) denote x!=y, x!=v_0, y!=v_0.
Then R(i,j) is S_v(v_i,v_j). Consequently both equality-congruence
schemas hold: substituting an equal coordinate value in either endpoint
leaves the current binary relation's truth unchanged. Euclid/rho7 and
rho1 are true under ordinary equality and coordinate quantification.
Rho2, rho4, and rho6 are the standard laws of nonempty coordinate
quantifiers on arbitrary predicates of the assignment. Rho8 is a
classical tautology. Full equality vacuity holds whenever its binder is
distinct from its endpoints. Validity at every assignment is preserved
by MP and theorem GEN.

For canonical membership vacuity there are two cases.

- If a=0 or b=0, R(a,b) is always false, so its vacuity implication is true.
- If a,b>0, kappa(a,b)>max(a,b)>0. Changing coordinate kappa changes
  neither endpoint nor the hidden coordinate0. Hence R(a,b) is unchanged.

So every canonical membership-vacuity axiom is valid.

But full membership vacuity at the perfectly fresh label0 fails. At an
assignment with (v_0,v_1,v_2)=(0,1,2), R(1,2) is true. Universal
quantification of coordinate0 includes the assignment v_0=1, where
R(1,2) is false. Thus

    R(1,2) -> All_0 R(1,2)

is false. It cannot be proved from the displayed logical basis.

For the own-formula-code extension, every positive finite formula code
strictly exceeds all its explicitly occurring variable labels. It is
also positive, so quantifying at that code changes neither explicit
coordinates nor the hidden coordinate0. Induction on the formula
therefore validates its canonical vacuity. The code-zero Truth case is
valid independently.

## Consequence for an implementation

Replacing full Rel-vacuity by the current large canonical binder does
not permit reusing the existing equality-helper proof. That proof's
membership-only fresh-vacuity induction actually needs all fresh
binders, and the countervaluation separates that requirement from the
weaker canonical family. Quantifier interchange alone does not repair it.

The separate conditional fixed-input0/output1 K construction does cover
all matrix codes c without a runtime c>=2 gate. Its proof handles c=1
through the false root premise and c=0 through the raw-nonempty upper
interpretation. The original a,b,c gate remains needed for its retained
ordinary logical vacuity families, so this fact by itself does not remove
the machine's comparison gate.
