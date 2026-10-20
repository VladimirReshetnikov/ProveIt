# Two precise obstructions to simplifying K230's closure schema

These are ordinary mathematical results about first-order axiom schemas. They
do not change the existing machine table or assert a new proof-assistant
endpoint. All structures have a nonempty domain, logical equality, and a
binary relation R written as membership. All schema matrices may have arbitrary
finite tuples of parameters.

Set

    p <=_R u  iff  forall z (R(z,p) -> R(z,u)),
    W_phi(p,C) := (exists y phi(y,p,q)) -> exists y (R(y,C) and phi(y,p,q)),
    H_phi(C) := forall u (R(u,C) ->
        ((exists p phi(u,p,q)) and forall p (p <=_R u -> W_phi(p,C)))).

The original ordinary K230 schema is

    forall a,x exists C ((phi(x,a,q) -> R(x,C)) and H_phi(C)).

IR denotes forall x not R(x,x).

## 1. Deleting support admits a rational-order model

Let K_weak delete only the conjunct `exists p phi(u,p,q)` from H_phi.
Then the structure (Q,<,=) satisfies every K_weak instance and IR.
The structure (Q_{≥0},<,=) does too and has an empty object, namely 0.
Thus adding an explicit empty-object axiom does not repair this deletion.

### Proof

In either dense rational order, p <=_R u iff p <= u. The forward direction
uses density: when p>u there is a rational z with u<z<p, contradicting
the displayed subset condition. The reverse direction follows from
transitivity of <.

Fix phi(y,p,q), a, and x. Choose a rational C strictly larger than x and
every parameter in the finite tuple q (and larger than 0 in the nonnegative
case). The seed requirement holds irrespective of the truth of phi(x,a,q),
because x<C.

Suppose u<C, p<=u, and phi(y,p,q) has a witness y. Then p<C. If y<C it is
already a witness inside C. If y>=C, choose

    t = max({p} union {parameters q} union {0 in the nonnegative case}),
    y' in Q with t<y'<C.

There is an order automorphism fixing every number <=t and sending y to y':

    f(z) = z                                      for z<=t,
           t+(y'-t)(z-t)/(y-t)                    for t<=z<=y,
           z+(y'-y)                              for z>=y.

It is a strictly increasing bijection of Q; in the nonnegative case it
preserves Q_{≥0} and fixes 0. It fixes p and all parameters q. Invariance
of first-order truth under automorphisms therefore gives phi(y',p,q).
Since y'<C, this is the required witness. IR is immediate. QED.

### Consequences

This is a full schema model, not a finite test of bounded formula complexity.
ZFC constructs the countable structure and proves its uniform satisfaction
by the standard induction on formula codes. Hence ZFC proves Con(K_weak+IR),
and also proves consistency after adding existence of an empty object.
If ZFC is consistent, it therefore cannot prove this consistency statement
equivalent to Con(ZFC), by the second incompleteness theorem.

No definable-domain or quotient interpretation recovering ZFC with a uniform
finite-refutation translation can bypass this obstruction: its composition
with the explicitly provable consistency would prove Con(ZFC).

There is nonetheless no finite model of K_weak+IR. In a finite domain of size
n, name all its elements with a parameter tuple and define a single n-cycle
f by a finite disjunction of equalities. Use phi(y,p): y=f(p), and seed any
x=f(a). A resulting C contains x. Whenever u belongs to C, p=u is eligible
by reflexivity of <=_R, so f(u) belongs to C. Finite iteration makes every
domain element belong to C, including C itself, contradicting IR. For n=1
the same argument applies directly. Thus the countable rational model is
the appropriate small countermodel; searching only finite models would miss
the obstruction.

## 2. Conditional seeding does not recover an empty object

Let K_cond retain full H_phi, including support, but replace the axiom by

    forall a,x (phi(x,a,q) -> exists C (R(x,C) and H_phi(C))).

K_cond+IR does not in general prove that an empty object exists. There is a
uniform relative interpretation in ZFC of K_cond+IR plus the assertion that
every object has a member.

### Explicit relation

In the universe of ordinary sets let e=emptyset and s={e}, and define

    R(x,y) iff (y=e and x=s) or (y!=e and x in y).

Only the membership profile of the ordinary empty set is altered. It now has
the single R-member s. The object s has its ordinary member e, creating a
two-cycle. Every object is R-nonempty. R is irreflexive: e!=s, and for y!=e
ordinary Foundation gives y notin y.

### Proof of each conditional instance

Fix phi in the R-language, its parameters q, and a,x with phi(x,a,q). Translate
R by the displayed ordinary set formula. By the Levy reflection schema choose
a sufficiently large limit ordinal lambda such that V_lambda contains
a,x,q,e,s and reflects this translated formula and its existential output
closure. Equivalently, for each p in V_lambda, whenever an output witness
exists in V, a witness in V_lambda exists and remains a true witness in V.

Every raw R-subset of u in V_lambda also belongs to V_lambda:

- If u!=e and p!=e, p <=_R u says exactly p is an ordinary subset of u.
  Hence rank(p)<=rank(u)<lambda.
- If u=e and p!=e, p <=_R e implies p is an ordinary subset of {s}.
  Such p lies in V_lambda because lambda was chosen above the finite ranks
  involved.
- If p=e, membership in V_lambda was already ensured.

By ordinary Separation form

    C = {y in V_lambda : exists p in V_lambda phi(y,p,q)}.

The assumed root witness gives x in C, so C is an ordinary nonempty set.
Consequently R(y,C) is exactly ordinary y in C. Every member y of C has a
supporting p by construction. If u in C and p <=_R u, then p lies in
V_lambda; if any output exists for p, reflection supplies y in V_lambda
with phi(y,p,q), and therefore y in C. Thus H_phi(C) and R(x,C) hold. QED.

This is a class interpretation, to be used on finite proofs or after passing
to a given model of ZFC. It does not assert that ZFC proves the existence of
a set model of all of ZFC. Each fixed conditional-schema instance is proved
by its finite reflection instance, which gives the usual uniform relative
consistency translation.

### Exact limit of this obstruction

The counterinterpretation refutes the proposed route
`K_cond+IR proves Empty; hence recovers unconditional K`.
It does **not** prove that K_cond is weaker in consistency strength than K.
A two-marker hereditary interpretation does establish equiconsistency
with ZFC; its complete proof is in `conditional_k_calibration.md`.
The raw-empty obstruction explains why that interpretation is needed.

The simple raw constructions are not all lost. For example K_cond+IR proves
exact singletons: use phi(y,p): y=a and root y=a. It also proves exact pairs
without an empty object. Given a,b choose a singleton s={a}; IR gives s!=a.
Use

    phi(y,p) := (p=s and y=a) or (p=a and y=b),

with seed input s and specified output a. Then a belongs to C. Taking the
eligible input p=a (a <=_R a) forces b into C, and support forces every member
to equal a or b. These facts are the first steps of the completed tagged
interpretation in `conditional_k_calibration.md`.

## Relation to the earlier results

The first argument is adapted specifically to K230's subset-input witness
closure. Rational-order countermodels for weaker collection versus supported
collection already occur in ProveIt's older closure-kernel work, so no claim
of novelty is made for the general model-theoretic technique.

The primary K definitions and the use of support to derive the empty object
are in Elliot Glazer's `k230-rocq` at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, especially
`coq/settheory/KPrimeCore.v`, `KP0.v`, `KPRaw.v`, and `KUpperCore.v`.
These obstruction proofs are independent ordinary arguments for the changed
schemas; they are not claims about a changed released machine.
