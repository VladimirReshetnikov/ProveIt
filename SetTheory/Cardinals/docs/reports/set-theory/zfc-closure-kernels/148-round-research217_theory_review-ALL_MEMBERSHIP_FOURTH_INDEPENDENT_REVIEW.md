# Independent review: arbitrary membership-headed fourth codes

Date: 2026-10-20.

## Verdict

**PASS as an ordinary, unbounded syntactic proof.** The identity-free invariant
is MP-closed and excludes both F and every implication whose immediate
antecedent is membership-headed. The new M-family and its quantified-
monotonicity branch are correctly handled. No mathematical gap was found.

Reviewed file:
`research218_round2_rho8/ALL_MEMBERSHIP_FOURTH_OBSTRUCTION.md`

Reviewed SHA-256:
`1525871efd5611ddf13d77f8b8fafb975ff1cf24065134dec9c7f77034a1dd39`.

No received code, search, checker, or machine was executed. This is not a
Lean/Rocq certification or a machine-size/runtime result.

## Native binding and identity-free definition

The native rows, truth, MP, GEN, bundle gate, and entire literal nks222 body
were checked against the native source files listed in the earlier
`MIXED_ORIENTATION_UNION_INDEPENDENT_REVIEW.md`. Thm222 has no separate
identity rule. Therefore omitting arbitrary identities from the auxiliary
class is legitimate. Identities that happen to coincide with some actual
generator remain covered through that generator; no syntactic disjointness
between generator families is assumed.

The strengthened bundle I(I(V(a,b,c),Q_k z),1) contains the full actual
bundle by setting k=c and z to the complete literal nks222 body. It does not
remove any support content. Allowing disabled gate triples only enlarges
the invariant.

All generated outputs have residue 0 or 2. Q-headed witnesses end in GEN.
All I-headed generators have a non-R immediate antecedent, including truth
0=I(0,0). Thus the stated root and immediate-antecedent invariants hold before
MP closure is considered.

## Exhaustive H and D inversions

For an H(a,b,c;v) major the required minor is I(I(c,v),a), with v positive
and R-headed. Truth is impossible because I(c,v)>0. GEN and the Q/E-
antecedent generators fail by tags. Bundle, D, and M minors force their
respective Q core, I-headed p, or Q-headed C to equal v. Only two cases remain:

- r6(i,x) forces x=a, c=C_i(a), v=1, giving exactly M(i,a,b).
- H(x,y,z;w) forces c=I(z,w), x=v, and
  a=I(I(v,z),I(y,z)), giving exactly D(y,z,b;w,v).

The order of the two independent membership parameters in D is correct.
No J family or assumed identity is needed.

For a D major the minor is I(h,p), where p=I(c,v)>0 and
h=I(I(w,c),I(b,c)). Truth, GEN, and Q/E-antecedent cases fail. Bundle gives
p=1; r6 gives I(b,c)=1; H gives I(y,z)=v; D gives an I-headed p'=v; M gives
a Q-headed C=v. Every case is impossible by residue. These are all witness
constructors, so D is inert.

## The essential M/monotonicity branch

For M(i,a,b), the required minor is I(a,C_i(a)), with
C_i(a)=Q_i N(Q_i a). Most generators fail because their consequent is 1 or
I-headed rather than Q-headed. Truth and GEN fail by positivity/outer tag.

The remaining retained possibilities are:

- r4(j,k,x) forces a=Q_j Q_k x and Q_i N(Q_i a)=Q_k Q_j x.
  Injectivity gives k=i and N(Q_i a)=Q_j x, an I/Q collision.
- r6(j,x) forces x=C_i(a)>a and a=X_j(x)>x, a growth cycle.

A monotonicity witness has conclusion I(Q_j r,Q_j s). Matching gives
j=i, a=Q_i r, and s=N(Q_i a)=N(Q_i Q_i r). Its premise is therefore
exactly

    Z_i(r)=I(r,N(Q_i Q_i r)).

This is not merely a tag exclusion; the separate Z lemma is needed and is
correct.

## Exhaustive Z exclusion

Write the right field of Z as I(Q_i Q_i r,1). Truth is impossible because
that field is positive; GEN has the wrong outer tag. Monotonicity and r4
have Q consequents; r1 and Bundle have consequent 1. For r2, the right
inner field would be Q_j y=1. For r3/r5 the first inner field would equate
R with Q. For G the right inner field would equate Q with 1. For H, D,
and M the right inner field would equate respectively an I code, an I code,
or a Q code with 1.

Only r6(j,x) survives these tag tests. It forces

    x=N(Q_i Q_i r),   r=X_j(x).

But x>=Q_i Q_i r>r and X_j(x)>x, contradiction. The strict bounds follow
from the actual native constructor domination; no induction hypothesis
about provability is used. This exhausts all generators and makes M inert.

## Inherited exclusions, closure, and aliases

The three old forbidden shapes I(E(i,j),1), X_i(a), and
I(V(a,b,c),Q_k z) remain excluded. Truth cannot equal them because each is
positive. The new H/D/M have I-headed antecedents and consequents, excluding
the first two by antecedent tags and the third by consequent tags. The
retained cases are unchanged: r1 matching X would equate E and Q, and r6
matching the bundle antecedent would equate Q and R. All other retained
cases fail immediately by tags. No MP argument is used in these inversions.

MP closure is a valid induction on the major's finite S witness. In the
truth case, I(u,v)=0 implies u=v=0. In monotonicity, Q-strip the minor,
apply the induction hypothesis to the strictly smaller premise witness,
and rebuild Q. Retained-row cases use the three forbidden shapes, absent
E-headed outputs, or Q stripping/rebuilding. H produces the admitted D or
M; D and M are inert. The witness induction is well founded regardless of
numeric aliases or equalities between outputs of different generators.

Actual derivations therefore embed into S. F has excluded residue 1.
Likewise, I(v,x) with membership-headed v cannot match any S generator:
truth would force v=0, GEN has a different outer tag, and every other
I-headed generator has a non-R antecedent. Thus neither I(F,F) nor I(F,0)
is derivable. The proof does not accidentally exclude truth's legitimate
self-implication alias I(0,0)=0.

## Consequence and limits

ZFC can formalize the finite constructor arithmetic and witness inductions,
so it proves consistency of the full independently-membership-headed
fourth-parameter calculus. All six orientations, their unions, F+Rbc, and
every membership-valued code-dependent subfamily are covered. Assuming
ZFC consistent, none can supply the desired ZFC-provable reverse
consistency implication. This is stronger than the earlier union result.

No unfulfilled ordinary proof obligation was found within this exact scope.
Adding a nonmembership fourth code, an independent identity schema, or
another propositional basis requires a new argument. Any connection to a
specific enumerator, blank machine, or state count remains separate.
