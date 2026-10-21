# A full countermodel to the T and dual-rho6 replacements of the K221/K220 calculus

## Result

Let C_T be the exact numerical calculus of the seed-K 222/221/220 program,
with the sole logical change

    rho6(a,A) = Ex_a(Q_a A) -> A

replaced by

    T(a,A) = Q_a A -> A.

Keep the current G row, all the other logical rows, the full gated
membership-vacuity/seed-K bundle, modus ponens, and theorem generalization.
Then **ZFC proves Con(C_T)**. The same conclusion holds for C_B, obtained by
replacing rho6 with its apparent classical dual

    B(a,A) = A -> Q_a(Ex_a A),

and even for the theory retaining both T and B. Consequently, if ZFC is
consistent, ZFC cannot prove consistency of any of these changed theories
equivalent to Con(ZFC).

This is a countermodel to the full changed theory, not merely a
non-derivability example for its logical rows. It closes the open T route
recorded in the K220 packet's `final_formalism_assessment.md`, section 3.
The construction below requires no model or consistency assumption about
ZFC. Its domain and complete satisfaction function are sets constructed
within ZFC. It also shows why the dual-rho6 proposal cannot be repaired
merely by announcing that explosion is refutation-conservative: unrestricted
generalization makes that assertion false for the complete native theory.

## 1. Native syntax and the literal K template

The numerical constructors are I(a,b)=4P(a,b), R(a,b)=4P(a,b)+1,
Q(a,b)=4P(a,b)+2, E(a,b)=4P(a,b)+3, where P is the usual Cantor pairing.
F=R(0,0)=1. Interpret native code zero as true; recursively decode every
positive code according to its residue and its two strictly smaller
fields. Write N(A)=I(A,F) and Ex_i(A)=N(Q_i(N(A))).
The only exceptional constructor equation is I(0,0)=0; it respects this
interpretation because true implies true is true. Thus the interpretation
is compositional for every native constructor, including this zero case,
and the native W_true rule is valid.

Every variable label in a positive decoded code c is below c. In particular,
the private label c is absent from its matrix chi=decode(c), including from
its bound-variable labels. For c=0 the matrix is constant true. For c=1 it
is the designated F.

For a,b,c with c different from a and b, the current bundle consists, at
ordinary false bottom, of membership vacuity and the following seed core.
These definitions are the literal nested relative-negation template from
`K221F.Codes222.nks222`, not an unverified simplification of the emitter:

    r = R(b,c)
    s = Q_c (R(c,a) -> R(c,b))
    w = Q_b (chi -> N(Q_b (chi -> N(r))))
    u = Q_a (s -> w)
    h = Q_b (r -> N(Q_a (chi -> N(u))))
    Seed = N(Q_c (h -> N(w)))

The entire numerical bundle is N(V -> Q_c(h -> N(w))), where
V=R(a,b) -> Q_c R(a,b). When F is false this is V and Seed.

## 2. The set-sized two-time model

Work inside ZFC. Put kappa=omega_1 and D=V_kappa. Every element of D has
countable rank. D is transitive and closed under singletons, transitive
closure, and the rank segments V_beta for beta<kappa. In particular, if
x is in D, there is a countable limit beta greater than rank(x)+1, and
V_beta minus {empty} is an element of D.

For each natural label j, set

    S_j = { omega*alpha + j : alpha < omega_1 }.

These are pairwise disjoint subsets of D, each unbounded in rank below
omega_1. Thus, for every B in D and distinct natural a,b, some element
of S_a belongs to neither B nor S_b. The S_j need not be elements of D;
they are sets in the ambient ZFC model, used to define an interpretation.

A world is (t,v), where t is 0 or 1 and v maps natural labels to D.

At time 0 interpret membership and equality ordinarily:

    R(i,j) is true iff v(i) is a member of v(j);
    E(i,j) is true iff v(i)=v(j).

At time 1 every equality atom is false. The atom R(0,0) is always true.
Every other membership atom has the interpretation

    R(i,j) is true iff v(i) is a member of v(j), or v(i) belongs to S_j.

The terminal membership relations may depend on the numerical endpoint
labels. This is permitted: the required object is a model of the numerical
calculus, and the user does not require ordinary first-order semantics.
Fresh-coordinate independence remains exact.

Implication is material implication at each world. Consequently F is false
at every time-0 world and true at every time-1 world.

Define Q_n as follows:

* If n=1 mod 4, Q_n varies coordinate n over D and leaves time fixed.
* Otherwise Q_n varies coordinate n over D and also ranges over the current
  and every later time.

All the quantifier relations are reflexive. They commute: coordinate
variations commute, time advancement is independent of every coordinate,
and its two possible relations (identity and the two-point order) commute.

## 3. Verification of all retained logical rows

The implicational Lukasiewicz axiom is a material-implication tautology.
Normal distribution and T hold for ordinary universal quantification over
the specified nonempty reflexive successor sets. Quantifier commutation
holds by the preceding product-relation calculation. Modus ponens and
generalization of formulas valid at all worlds preserve validity.

Both membership-congruence rows hold at time 0 by genuine equality, and at
time 1 because every equality antecedent is false.

Equality existence Ex_a E(a,b) holds at time 0: choose the value v(b) for
coordinate a at time 0. This makes E(a,b) true while F is false, so the
inner universal Q_a(E(a,b)->F) is false. At time 1 the outer relative
negation is automatically true, because F is true.

The merged equality axiom is

    G(a,b,c) = E(c,a) -> (E(c,b) -> Q_{RCode(a,b)} E(a,b)).

At time 0 its antecedents imply v(a)=v(b). The binder RCode(a,b) is
strictly greater than a,b and is congruent to 1 modulo 4. Its quantifier
therefore only varies a fresh coordinate, without advancing time, and
preserves E(a,b). At time 1 the antecedents are false.

For the full required gated membership-vacuity family, take c different
from a,b. Its initial atomic membership depends only on coordinates a,b;
terminal membership also depends only on these coordinates and contains
the initial membership relation. Thus R(a,b)->Q_c R(a,b) holds at both
times, whether or not c advances time.

This covers every logical row in C_T. In particular, no unproved recovery
of reflexivity, substitution, negative vacuity, or ordinary predicate
calculus is being assumed.

### The same model validates the dual B row

Suppose a native formula A is true at an initial world (0,v). Every initial
Q_a-successor (0,v[a:=x]) can choose the original value v(a) as a witness
for Ex_a A: this returns to (0,v), where A is true and F is false. Every
terminal Q_a-successor satisfies Ex_a A automatically, because its outer
relative negation has F=true. Thus A->Q_a(Ex_a A) holds initially. At a
terminal world every Ex_a A is true and all successors remain terminal,
so B holds there too. This argument works for arbitrary decoded A,
including formulas with nested quantifiers and numerical endpoint markers.

By contrast, original rho6 fails at every terminal world for
A=E(0,0). Its antecedent Ex_a(Q_a A) is true because F is true, whereas
A is false by the terminal equality interpretation. Therefore the source
of the lost strength is precise: relative negation becomes a constant-true
operation in these terminal worlds, and the new B row does not exclude
them. The original rho6 does exclude them through its unnegated final A.

## 4. Exact reduction of the K template at time 0

At time 1 every relative negation N(A) is true. Direct inspection of the
literal formulas gives w=u=h=true there. Every extra terminal test inside
the quantifiers defining w,u,h, and Seed is therefore true and contributes
no further condition at time 0. The sole potentially nontrivial terminal
test is inside the raw subset formula s.

Fix all coordinates other than a,b,c. At time 0 write chi_0 for the
initial truth value of the decoded matrix. It can be an arbitrary relation
of its finitely many coordinates; no ordinary first-order definition in D
is required. Freshness makes chi_0 independent of coordinate c.

If a and b are distinct labels, write x for coordinate a, y for coordinate
b, and C for coordinate c. Directly expanding the literal relative
negations yields

    W(x,C) = [(there exists y with chi_0(x,y)) implies
               (there exists y in C with chi_0(x,y))],

    U(y,C) = for every x, [s_0(x,y,C) implies W(x,C)],

    H(C) = for every y in C,
             [there exists x with chi_0(x,y) and U(y,C)],

    Seed_0 = there exists C in D with H(C) and W(v(a),C).

The existential in Seed does not get to use a time-1 witness: its outer
relative negation has false F at time 0, whereas h->N(w) is true at time 1.
The countermodel works by changing the subset guard, not by treating a
terminal F-true world as an existential witness.

The formulas above follow directly by evaluating each material implication
and each defined Ex at both times. The accompanying BDD checker verifies
these local Boolean identities independently for two-element coordinate
domains, with all atomic values left symbolic. The unbounded-domain proof
is the displayed expansion and does not rely on the finite check.

## 5. Non-membership matrix codes

Suppose c is not congruent to 1 modulo 4 and a differs from b. The private
quantifier Q_c examines time 1. Since c differs from both endpoint labels,
the two terminal atoms in s use the unexceptional marker interpretation.
Choose z in S_a outside v(b) and S_b. Then at time 1

    R(c,a) is true and R(c,b) is false.

Therefore s_0 is false for every initial assignment, including every
choice of input x and container C. Thus U is true, and H(C) says only that
each member of C is supported by some input of chi_0.

If the current seed input has no output witness, choose C=empty. Otherwise
choose one witness y and put C={y}. This choice is in D, its only member
has the seed input as a support witness, and it satisfies the request W
for that seed input. Every non-membership matrix instance is valid.

## 6. Membership matrix codes

Suppose c is congruent to 1 modulo 4. Then the matrix is one atomic
membership formula R(i,j); at time 0 it has its ordinary set-theoretic
meaning. The private quantifier Q_c does not advance time, so s_0 is
exactly x subseteq y. The required atomic-K instances all hold in D.

If the matrix depends on at most one of the distinct input/output labels,
use an empty or singleton container. For output-only matrices, choose a
singleton containing any output witness, if one exists. For input-only
matrices, choose a singleton exactly when the seed input satisfies the
matrix; a nonempty container then fulfills every request at every input,
and the seed input supports each chosen member. Constant matrices are the
same two cases. A repeated atomic label i=j is always false and uses the
empty container.

Only the following two genuinely binary cases remain.

### 6.1 Matrix output in input

For chi_0(x,y) meaning y in x, take C=TC(seed), the transitive closure of
the seed set, here explicitly defined as the union of seed, union(seed),
union(union(seed)), and all further finite iterated unions. Thus
seed subseteq C. Every member y of C has a support
input {y}. If x subseteq y and y is in C, transitivity gives x subseteq C;
every nonempty x therefore has an output witness in C. This verifies the
request, support, and subset-closure clauses. TC(seed) belongs to D.

### 6.2 Matrix input in output

For chi_0(x,y) meaning x in y, choose a countable limit beta greater than
rank(seed)+1 and put C=V_beta minus {empty}. The seed request has output
{seed}, which belongs to C. Every member y of C is nonempty, so it has a
support input. If x subseteq y and y belongs to C, then rank(x)<beta and
{x} belongs to C, because beta is a limit. This singleton is the required
output witness containing x. The container C itself belongs to D.

Thus every membership-code matrix instance holds without assuming that D
satisfies full K or ZFC.

## 7. Coincident input and output labels, and low codes

When a=b, the literal subset test is an identity and is true at both times.
The request w is independent of that common coordinate, and u=w at time 0.
If chi_0 has no witness at that coordinate, choose C=empty. Otherwise
choose C={y} for one witness y. Direct substitution gives w=u=h=true at
time 0. This proves every coincident-label instance without assuming an
alpha-renaming or treating the two quantifiers as independent coordinates.

Code zero is constant true and uses the non-membership argument. Code one
is F, false initially, and uses the empty-container membership argument.
The source gate excludes c=a or c=b throughout; no prohibited instance is
silently added or needed.

## 8. Internal consistency conclusion

All objects used above are sets in ZFC: omega_1, D, the marker family,
the assignment space D^N, the two-time successor relations, and the
recursive satisfaction function on natural formula codes. The verification
establishes that every numerical axiom is valid at every world and that
the two rules preserve validity. Induction on a finite numerical proof
therefore establishes soundness inside ZFC.

F is false at every initial world, so no such proof derives F. This proves
ZFC |- Con(C_T), ZFC |- Con(C_B), and ZFC |- Con(C_T+B).
If ZFC also proved Con(C_T) <-> Con(ZFC), it would prove
its own consistency, contrary to the second incompleteness theorem when
ZFC is consistent. The same argument applies to C_B and C_T+B.

The theorem concerns exactly these T and dual-B replacements. It makes
no assertion about doubled-quantifier fusions or other modifications.
Those require their own proof or countermodel.
