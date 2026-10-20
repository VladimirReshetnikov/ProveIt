# Fixed input 0, output 1: a calibrated conditional numerical family

## The result and its scope

Keep the eight logical rows rho1--rho8, the truth seed 0, modus ponens,
generalization, and both original atomic-vacuity families. Replace only the
set-theoretic core in each enabled bundle by the conditionally seeded core
with **input variable 0, output variable 1, and private variable equal to the
opaque matrix code c**. Keep the old bundle gate involving the original
enumeration parameters; do not add a gate excluding c=0 or c=1.

The resulting numerical proof calculus derives its halt code F=1 if and
only if ordinary ZFC is inconsistent. Both reductions are effective finite
proof translations and can be formalized in ZFC. This statement concerns
the mathematical numerical calculus. A particular machine still needs its
source, enumeration, compiler, runtime, and blank-start certificates.

The new ingredients are:

1. The two-marker interpretation in `conditional_k_calibration.md`, which
   gives Con(Kc+IR) iff Con(ZFC).
2. A ZFC interpretation of Kc+IR together with the assertion that every raw
   object has a member.
3. A complete treatment of the formerly dangerous low-code collisions:
   output/private collision c=1 has a false root premise, whereas
   input/private collision c=0 is supported by raw global nonemptiness.
4. A fixed-role padding and naming algorithm, with an optional literal
   decoder round trip and a simpler direct proof-translation route.

No reduced equality calculus is used. Equality is genuine equality, all
eight old logical rows are retained, and both full vacuity families remain
available. No new Rocq kernel check is claimed here.

## 1. Exact numerical definitions

Use the pinned K230 pairing and constructors:

    P(r,s) = (r+s)(r+s+1)/2 + s
    I(r,s) = 4 P(r,s)
    M(i,j) = 4 P(i,j) + 1
    A(i,r) = 4 P(i,r) + 2
    E(i,j) = 4 P(i,j) + 3
    F = 1
    N(r) = I(r,F)
    C(r,s) = N(I(r,N(s)))
    X(i,r) = N(A(i,N(r))).

Here C is numerical conjunction and X is numerical existential
quantification; neither is a new primitive machine operation. The symbol
C in this section is a constructor, not a set witness.

For a given opaque code c define

    S_c = A(c, I(M(c,0), M(c,1)))
    W_c = A(1, I(c, X(1,C(c,M(1,c)))))
    H_c = A(1, I(M(1,c),
                 X(0,C(c,A(0,I(S_c,W_c))))))
    J_c = I(c, X(c,C(M(1,c),H_c))).

Thus J_c is exactly the old full support-and-closure body, with the outer
seed implication moved outside the existential, and with active names
fixed to input 0 and output 1. The private name and all four opaque matrix
occurrences remain c.

The unchanged vacuity formula is

    V(a,b,c) = C(I(M(a,b),A(c,M(a,b))),
                 I(E(a,b),A(c,E(a,b)))).

The new bundle and old gate are

    B(a,b,c) = C(J_c,V(a,b,c))
    G(a,b,c) = 0                    if c=a or c=b,
               B(a,b,c)           otherwise.

For auditing the two exceptional cases, the small atomic values are

    M(0,0)=1, M(1,0)=5, M(0,1)=9, M(1,1)=17.

Therefore the literal low-code constructor expressions are

    S_0 = A(0,I(1,9))
    W_0 = A(1,I(0,X(1,C(0,5))))
    H_0 = A(1,I(5,X(0,C(0,A(0,I(S_0,W_0))))))
    J_0 = I(0,X(0,C(5,H_0)))

    S_1 = A(1,I(5,17))
    W_1 = A(1,I(1,X(1,C(1,17))))
    H_1 = A(1,I(17,X(0,C(1,A(0,I(S_1,W_1))))))
    J_1 = I(1,X(1,C(17,H_1))).

These are finite constructor expressions; expanding their enormous
integer values is unnecessary for either the proof or the machine.

The a,b occurring in V and in the gate are the ORIGINAL enumeration
parameters. They do not become 0,1. Consequently every original valid
atomic-vacuity instance remains a conjunction projection of an enabled
bundle. Every J_c is also a projection: for example use the original
parameters a=b=c+1. Equal original parameters are allowed; the gate tests
only whether either equals c.

An equivalent fused version of the root is

    J_c = I(c, N(A(c,I(M(1,c),N(H_c))))),

where equality here means derivable equivalence if the unfused numerical
constructor C is literally expanded. The exact fused source may also
cancel the two inner existential/conjunction pairs and the nested final
bundle pair. These are ordinary double-negation cancellations in the
retained numerical logical basis. The conditional-root movement itself
uses the theory calibration below, not propositional equivalence with the
unconditional schema.

## 2. Decoder conventions and exactness

The total decoder D has two deliberately exceptional cases:

    D(0) = T = (forall v0 (v0=v0)) -> (forall v0 (v0=v0))
    D(1) = R(v0,v0).

Code 0 is a closed tautology. Code 1 is both the machine's distinguished
halt/relative-falsity code and the code of the atom R(v0,v0). It is NOT
decoded as primitive ordinary falsity. Arrows whose numerical consequent
is 1 decode as primitive negation. IR, the axiom forall x not R(x,x), is
what validates that relative-falsity convention in the soundness proof.

For all c, J_c has the exact named decoding

    D(c) -> exists vc
      (R(v1,vc) and
       forall v1 (R(v1,vc) ->
         exists v0 (D(c) and
           forall v0 (
             (forall vc (R(vc,v0) -> R(vc,v1))) ->
             forall v1 (D(c) ->
               exists v1 (D(c) and R(v1,vc))))))).       (J)

Occurrences of D(c) are inserted as decoded matrices, with the ordinary
scope of the surrounding quantifiers. The bound names may coincide at
c=0 or c=1; those cases are not silently renamed away.

Why is this exact even at low codes? Every membership formula that serves
as an implication consequent outside the negative encodings has code
M(c,1) or M(1,c). Neither can equal 1, since neither pair of labels is
(0,0). Existential and conjunction codes are positive and never equal 1.
Therefore all uses of the exact D-I decoder rule satisfy its side
conditions. The explicit N, C, and X decoder lemmas apply to all arguments,
including opaque matrix c=0 or 1. The general lemma for unfixed KCore uses
the stronger sufficient condition c!=b; here the arithmetic check is
weaker and holds for b=1 even when c=1.

For positive c, every name occurring in D(c) is strictly below c. Thus c
is absent even as a bound name in D(c). At c=0 this stronger occurrence
statement fails, because T contains bound variable 0; the needed
free-variable statement still holds because T is closed. These are the
pinned lemmas D_names_below, D_positive_occ, D_private_fresh, and
D_zero_closed. Do not replace free freshness at 0 by total absence.

## 3. Ordinary theories used for the upper direction

Write

    Sub(p,u) := forall z (R(z,p) -> R(z,u))
    H_phi(C) := forall u (R(u,C) ->
      ((exists p phi(u,p,q)) and
       forall p (Sub(p,u) ->
         ((exists y phi(y,p,q)) ->
           exists y (R(y,C) and phi(y,p,q)))))).

The conditional schema Kc is

    forall a,x (phi(x,a,q) ->
                 exists C (R(x,C) and H_phi(C))).

It is equivalent to the emitted support body in which the support
existential is placed around the conjunction with the input-universal
closure: the support variable does not occur free in that universal
closure, because the latter rebinds the input role. First-order domains
are nonempty.

Let

    IR := forall x not R(x,x)
    NE := forall p exists y R(y,p)
    U  := Kc + IR + NE.

Kc proves raw singletons by using the constant-output matrix y=x.
Consequently it proves upward hosting, forall x exists C R(x,C). NE is
downward nonemptiness and is a separate assertion; no raw empty object is
postulated in U.

### All c>=2 are ordinary conditional instances

For c>=2, input 0, output 1, and private c are pairwise distinct; private
freshness holds. Abstract the free active roles of D(c) into output and
input positions and leave all other free names as parameters. The usual
named/de Bruijn environment calculation gives (J) from the corresponding
ordinary conditional instance. This is the same calculation as
KDecodeReverse.ordinary_to_named_source, with the implication introduced
before choosing the outer witness instead of inside its conjunction.

### The exact c=1 expansion

Put f=R(v0,v0). Formula (J) becomes

    f -> exists v1
      (R(v1,v1) and
       forall v1 (R(v1,v1) ->
         exists v0 (f and
           forall v0 (
             (forall v1 (R(v1,v0) -> R(v1,v1))) ->
             forall v1 (f ->
               exists v1 (f and R(v1,v1))))))).

The outer premise f is false by IR, under every environment. Hence this
whole formula is provable in U regardless of its inner binder collisions.
The proof does not assert that a self-membered container exists.

### The exact c=0 expansion

Here the matrix is the closed tautology T. Formula (J) becomes

    T -> exists v0
      (R(v1,v0) and
       forall v1 (R(v1,v0) ->
         exists v0 (T and
           forall v0 (
             (forall v0 (R(v0,v0) -> R(v0,v1))) ->
             forall v1 (T ->
               exists v1 (T and R(v1,v0))))))).

This is a direct, literal binder expansion; in particular the innermost
subset quantifier shadows the current input variable and the outer
container variable. It must not be mistaken for an ordinary subset
formula with three distinct names.

To prove it in U, choose the outer container using a singleton of the
specified output. For each member u of that container, choose any object
for the support existential. T holds. For each newly universally bound
input p, NE gives y with R(y,p), proving the requested inner existential.
The subset antecedent is immaterial to this proof. Thus the support and
closure hold. This uses only singleton hosting, NE, and the closed truth
of T; IR is not needed in this particular low-code proof.

These two low-code arguments are why constants 0,1 are special. With
output fixed to 3, c=3 has true matrix D(3)=(v0=v0) but demands a
self-membered outer container, contradicting IR. It cannot be admitted
ungated. Input 0/output 1 avoids that obstruction.

## 4. ZFC interprets U by changing one membership column

In ordinary ZFC let e be the empty set and s={e}. Interpret R by

    R(x,y) iff (y=e and x=s) or (y!=e and x in y).

Use all sets as the domain and ordinary equality. There is a two-cycle
e R s R e, but no self-loop. Foundation proves IR, while every nonempty
ordinary set has an ordinary member and e has the special member s, so
NE holds. Ordinary singleton {x} is always nonempty and has exactly x as
an R-member.

We prove each conditional schema instance within ZFC. Fix a translated
matrix phi_R(y,p,q), parameters q, and seed data x,a with phi_R(x,a,q).
By finite Levy reflection choose a limit ordinal lambda>4 such that
V_lambda contains x,a,q,e,s and reflects phi_R and its existential output
closure. More explicitly, for every p in V_lambda, whenever some y in V
satisfies phi_R(y,p,q), there is such a y in V_lambda; this follows by
reflecting the finite list {phi_R, exists y phi_R}.

Use Separation to define the ordinary set

    C = {y in V_lambda : exists p in V_lambda phi_R(y,p,q)}.

The seed puts x in C. Thus C is nonempty, so membership into C agrees
with ordinary membership. Each R-member u of C has the required support
input p in V_lambda.

If u is in V_lambda and Sub(p,u) holds for R, then p is in V_lambda:

- If p=e, this is immediate.
- If p!=e and u!=e, the raw subset assertion is the ordinary p subset u;
  rank(p)<=rank(u)<lambda.
- If p!=e and u=e, the ordinary members of p are all s, so p is a subset
  of {s}; it has finite rank and belongs to V_lambda.

Therefore a closure request at an R-subset p of a member u of C has its
input in V_lambda. Reflection supplies its output witness y in V_lambda;
the same input p shows y belongs to C. This proves all of H_phi(C).

Every displayed formula translation is effective and uses a finite list
of ZFC axioms for each input matrix. The argument is a class
interpretation, hence an effective translation of finite refutations.
It does not claim that ZFC proves the existence of a set model of all of
ZFC or of all of U. In particular, it gives the formal implication

    Con(ZFC) -> Con(U).

Conversely U contains Kc+IR, whose two-marker hereditary interpretation
recovers the original KPrime+IR. The pinned original calibration therefore
gives Con(U)->Con(ZFC). Thus U is equiconsistent with ZFC.

## 5. Fixed-role naming and padding for the lower direction

Let phi(y,p,q) be any ordinary conditional matrix, represented with de
Bruijn free index 0 for output y, index 1 for input p, and higher indices
for parameters. Use the injective free-name map

    nu(0)=1,  nu(1)=0,  nu(n)=2n-1 for n>=2.

Choose all bound names from the positive even numbers 2,4,6,..., fresh
within their scope. The pinned Std_tr depth-based choice bname(k)=2k+2
has exactly the needed separation from these free names. This gives a
capture-free named formula p with active names 1 and 0. Universal closure
of its derived conditional core will quantify the finitely many parameter
names as well as the active root names.

### Literal decoder route

Before naming, replace each syntactically diagonal membership atom
R(z,z) by ordinary falsity. IR proves equivalence of the old and new
matrix by induction on its syntax. Represent ordinary falsity by the
closed named formula not forall v0(v0=v0), whose native code is not 1.
Consequently the named p contains no atom Wel 0 0, including inside
implication consequents. Equality atoms with label 0 cause no problem.

Now set

    c = encode230(not not p).

The existing safe encoder theorems give c>3, D(c)=not not p, and the
private-name freshness needed by the ordinary named-core calculation.
By double-negation elimination and contextual congruence, the emitted
fixed-role conditional core supplies the conditional instance for p.
The ordinary matrix-equivalence proof under IR restores the original
phi. This obtains every ordinary Kc instance from the fixed family plus
IR. None is lost by freezing the active names.

The replacement is a metatheoretic proof-translation step; it does not
add a normalization routine to the tiny machine. The machine still
enumerates every natural c unchanged.

### Direct tau route, without diagonal replacement

The pinned completeness argument actually supports a shorter proof. It
uses Q(p):=thm(tau(p)), where tau is the homomorphic native encoder, and
does not require D(tau(p))=p. The retained logical rows and vacuity
projections prove every translated pure first-order logical theorem.
For every named p, safe or otherwise, put

    pp = not not p,
    c = tau(pp).

Then c>3 and tau(pp)=c is a literal constructor identity. The numerical
fixed core J_c is therefore exactly tau of the named conditional core
with matrix pp. Its derivability follows by projecting B(c+1,c+1,c).
Cancel pp to p by ordinary double-negation equivalence, transported to
the numerical calculus using the retained logic.

Freshness here does not require a decoder round trip. An elementary
induction on every named p proves the stronger unconditional statement

    every variable name occurring in p is < encode230(p).

For atomic formulas this follows from i,j<=P(i,j) and the positive tag.
For implication it follows from positivity of both subformula codes and
P(r,s)>=r,s; negation and universal quantification are the same direct
inequalities. Consequently c is absent from pp and from p, even if p
contains Wel 0 0. This strengthens the convenience lemma
encode230_private_fresh, whose pinned proof imposed no_relative_atom
only because it went through the total decoder.

Adapt named_source_to_kprime using the name map nu: assume the ordinary
root matrix first; instantiate the universally closed named core at its
root environment; use the matching matrix theorem to obtain the outer
existential; then copy the original environment proof for support and
subset closure. All active names and the private name are distinct here,
because c>3. Standard alpha equivalence and generalization handle the
original ordinary variable names and finite parameter tuple.

As in CompleteBase230.TB_IR, IR is available in the ordinary theory of
universally closed numerical theorems: not R(v0,v0) has native code
I(F,F), the identity theorem; its universal closure is IR. Thus the
ordinary conditional interpretation can be applied in this theory. The
unchanged TB_to_thm argument converts an ordinary finite contradiction
back into a numerical proof of F. This is why using numeric code 1 as
relative falsity in a lower proof translation is legitimate even when
the named formula contains the atom Wel 0 0.

## 6. Combining the finite refutation translations

For soundness, repeat the old Sound230 proof with the new decoded bundle
axiom. Every logical row is unchanged. The same relative-falsity lemma
under IR transports numerical implication and handles numeric 0. Each
enabled fixed bundle is provable in U by Sections 2--3 and ordinary
vacuity. Thus a numerical proof of 1 gives a contradiction in U, and the
ZFC interpretation of U gives a finite ZFC contradiction.

For completeness, a finite ZFC contradiction translates through the
pinned KPrime+IR calibration to a finite contradiction in KPrime+IR.
The two-marker interpretation translates it to Kc+IR. Section 5 embeds
every needed conditional instance and equality/IR premise into the
ordinary theory of closed numerical theorems. The retained completeness
infrastructure then gives a numerical proof of 1.

These are transformations of finite syntax and finite derivations. They
are formalizable in ZFC uniformly, including for nonstandard formula and
proof codes inside a model of ZFC. The proof should not be described as
merely an external truth equivalence or as automatically inherited from
the metatheory of Rocq.

## 7. Primary source anchors and verification status

All original sources below are in Elliot Glazer's k230-rocq repository,
commit 3142e4dd980f0be12f4abb636c4ae2528afc17eb:

- coq/settheory/KCode230.v: exact pairing, negative constructors, original
  closure body, vacuity, and old gate.
- coq/settheory/KDecoder230.v: total decoder, code 0, code 1, and exact
  constructor decoding side conditions.
- coq/settheory/KDecodeFresh.v: private freshness and exceptional zero.
- coq/settheory/KDecodeEncode.v: safe literal round trip and double
  negation padding c>3.
- coq/settheory/KDecodeTranslate.v and KDecodeEnv.v: original fixed-role
  naming and environment method.
- coq/settheory/KDecodeCore.v and KDecodeReverse.v: both directions of
  the ordinary/named core calculation.
- coq/logic/Comp_Prop230.v: all pure logic from rho1--rho8 and both
  vacuity projections; genuine equality remains present.
- coq/logic/CompleteBase230.v: ordinary closed numerical theorems, IR,
  and the finite contradiction-to-F translation.
- coq/logic/Complete230.v: direct tau method for the original family.
- coq/logic/Sound230.v: relative falsity, numeric 0, and finite numerical
  proof soundness.
- coq/settheory/KUpperConsistency.v: finite-refutation calibration of
  original KPrime+IR to StandardZFC.

The new conditional interpretation, membership-column interpretation,
fixed01 low-code arguments, and adapted completeness are mathematical
proofs given here. They have not yet been serialized and checked as new
Rocq theorem endpoints. The final artifact must separately report the
exact tested source and machine certificates; this note does not certify
any state count.
