# Independent audit of the native syntactic obstruction

Reviewer: opening_encoder, 20 October 2026. This is a mathematical source
review of drop_contract's `invariant.md`, not a Lean check or a search run.
I independently found and communicated the retained-rho6-to-rho8 detachment
before reading that draft; I did not author its auxiliary-class proof.

Write `I,R,Q,E` for the four exact Code254 constructors, `T=0`, `F=1`.
Their tags are 0,1,2,3. Pair injectivity holds even for `I(0,0)=0`.
We use `I(x,y)>=x,y`, `R(x,y)>x,y`, and
`R(x,y)=1 iff x=y=0`. There is no syntactic renaming or substitution premise.

The reviewed class S admits the literal r1--r6, merged G, modified H and
bundle axioms, all identities, GEN, and quantified monotonicity. It does
not admit MP in its definition. Allowing all bundle triples, including
disabled ones, only strengthens the obstruction.

## Exhaustive last-rule checks

Every S rule produces tag 0 or 2, so no membership/equality atom is in S.
An S witness for `Q_i p` must end in GEN. None of the axioms, identities or
monotonicity outputs has tag 2. Thus stripping one Q removes one GEN node.

The remaining forbidden shapes are checked against every generator below.
Here `V=I(R(a,b),Q_c R(a,b))` and `D=nks(a,b,c)` is Q-headed.

| Desired S formula | Identity | Monotonicity | r1/r2/r4 | r3/r5/G | r6 | H | Bundle |
|---|---|---|---|---|---|---|---|
| `I(E(i,j),F)` | E cannot equal F | left Q, not E | left Q | right I, not F | left I | left I | left I |
| `I(Q_i I(Q_i p,F),F)` | left Q cannot equal F | right Q, not F | r1 would identify E with Q; r2 right I; r4 right Q | left E, not Q | left I | left I | left I |
| `I(V,D)` | V has tag I, D tag Q | left Q, not V | left Q | left E | matching V's first field would equate R and Q | matching V's first field would equate R and I | matching V's first field would equate R and I |

GEN is separately excluded in each row by the outer I tag. Every desired
formula above is positive: none is the exceptional zero identity.

For an H trigger `I(I(c,R(a,b)),a)`, GEN has the wrong outer tag;
monotonicity and r1/r2/r4 have Q left fields; r3/r5/G have E left fields.
Identity matching requires `a=I(c,R(a,b))>=R(a,b)>a`.
Bundle matching requires its Q-headed D to equal R(a,b).
A minor H(x,y,z) requires both `x=R(a,b)` and
`a=I(I(x,z),I(y,z))>=x`, contradicting strict growth.
The only remaining constructor is r6(i,p). Its fields force
`p=a`, `R(a,b)=F`, hence a=b=p=0, and
`c=Q_i I(Q_i 0,F)`. No possibility is lost at code zero.

This surviving case really occurs: r6(i,0), followed by H(0,0,c), derives
`I(I(0,c),I(0,c))` in one MP. Therefore the argument does not falsely claim
that no MP between primitive axioms is possible.

## MP closure and effective strength

Induct on the S witness for the major `I(p,q)`, with an arbitrary S witness
for p as an additional parameter.

* Identity returns the minor, including the case p=q=0.
* GEN cannot supply an I-headed major.
* Monotonicity writes p=Q_i u and q=Q_i v. Strip the minor's GEN, recursively
  use the strictly shorter major witness for I(u,v), then add GEN to v.
* r1 requires the first forbidden shape after stripping its minor's Q.
* r2 strips Q from its minor and adds the S monotonicity constructor.
* r3/r5/G have an impossible E-headed minor.
* r4 strips the two Qs and adds them in swapped order.
* r6 requires the second forbidden shape.
* Bundle requires the third forbidden shape.
* H has a=b=0 by the trigger inversion; its conclusion is an admitted identity.

These operations are primitive recursive on explicitly coded finite witness
trees. The only recursive MP-elimination call descends into the major's
monotonicity premise; its minor simultaneously loses one GEN. A useful bound,
counting constructor nodes and treating the numeric labels separately, is

    size(mpS(major,minor)) <= size(major) + size(minor).

The r2 and r4 cases preserve the minor's node count, H returns one identity,
and the monotonicity case satisfies the bound by induction. Consequently a
tree-form modified derivation can be transformed into an S witness with no
more constructor nodes than the original derivation tree. A shared-DAG proof
can first be unfolded; no polynomial bound in DAG size is claimed.

All numeric inspections are primitive recursive operations on constructor
codes. ZFC can formalize the finite witness transformation and the tag
invariant. No general model existence or consistency assumption is used to
prove absence of F. A proof assistant formalization has not been supplied
by this reviewer; no exact minimal arithmetic base is asserted here.

Therefore the ordinary proof does establish that ZFC proves consistency of
this exact modified calculus. If ZFC is consistent, this rules out a
ZFC-provable equivalence with Con(ZFC), by the usual second-incompleteness
argument. It makes no claim about a raw machine without the separate machine
and calculus correspondence. The original unrestricted K219 is unaffected.

## Two further orientations covered by the same proof

The same argument works for U=R(B,A): strict growth over A still applies,
and U=F again forces A=B=0, giving an identity.

For U=R(A,C) and U=R(C,A), strict growth over A still excludes identity
and H triggers. A minor r6 would force U=F, hence A=C=0. But matching its
left field also forces C=Q_i I(Q_i A,F)>0. Thus H cannot fire at all in S.
All other inversion cases are unchanged. These two orientations are also
provably consistent by this syntactic argument.

U=R(B,C) and U=R(C,B) are not covered: growth over A is missing. There are
actual H-to-H detachment instances, and they must be studied separately.
