# A finite class-coded closure theory with fifteen universal clauses

Research note, 17 October 2026 UTC. This note supplies ordinary mathematical
proofs, an exact clause specification, and a comparison with the previously
accepted FAK12 presentation. It does not supply a binary Turing machine or
claim a state record. The general finite class/assignment method is due to
Harvey Friedman. The present synthesis replaces FAK12's explicit set axioms
by a single class-coded empty-seeded positive subset-closure principle. Its
raw equality-free EPSC consistency calibration is an existing ProveIt result,
not a new theorem of this note. The displayed finite payload and its direct
model construction were not found in the inspected 34 reviewed sources or
three incoming archives at ProveIt commit
61e77836565f63582561f54745f633d50efd9c7d. No broader priority claim is made.

**Version note.** Sections 1--6 display a twelve-function unshared form to
make witness dependencies easy to audit. The recommended payload is the
nine-function guard-fused form with the derived member term in Section 7.
It has the same fifteen clauses and thirty-five literals; two pairs of
function names are identified and D is replaced by a core witness term.
The supplied countermodel checker evaluates that recommended form. A separate
note `extensional_control_proof.md` supplies the full direct lower proof for
the seventeen-clause extensional control.

## 1. Language and conventions

Use one nonempty first-order domain with genuine logical equality. All data
objects, assignment objects, selector values, class codes, and Skolem values
inhabit that domain. There are two binary predicates E and Inc and a binary
branch predicate G. The single constant is d. The proper function symbols are

| Function | Arity | Role |
|---|---:|---|
| V | 2 | assignment evaluation |
| C | 3 | assignment update |
| N | 2 | NAND class constructor |
| A | 2 | membership-atom class constructor |
| Q | 2 | existential class constructor |
| W | 3 | witness for existential class membership |
| F | 2 | bad input when local subset boundedness fails |
| Y | 3 | bad output for a proposed subset bound |
| Z | 3 | member outside that bound |
| H | 2 | closure hull when locally bounded |
| D | 1 | member selector for nonempty objects |
| S | 3 | supporting input for a hull member |

The abbreviation q means the term N(d,d), not a second constant. Put

    R(b,t,x,y) := Inc(C(C(b,d,x),q,y),t).

All variables displayed in each clause below are universally quantified.
Repeated variables may receive equal values. Quantification is over the one
common domain, not over separate finite label domains. All function symbols
are total. E need not be extensional, irreflexive, or well founded.

## 2. Exact fifteen-clause payload

The assignment and class clauses are:

    01. V(C(s,j,z),j) = z.
    02. k = j  OR  V(C(s,j,z),k) = V(s,k).

    03. Inc(s,N(a,b)) OR Inc(s,a).
    04. Inc(s,N(a,b)) OR Inc(s,b).
    05. NOT Inc(s,N(a,b)) OR NOT Inc(s,a) OR NOT Inc(s,b).

    06. NOT Inc(s,A(j,k)) OR E(V(s,j),V(s,k)).
    07. Inc(s,A(j,k)) OR NOT E(V(s,j),V(s,k)).

    08. NOT Inc(C(s,j,z),a) OR Inc(s,Q(j,a)).
    09. NOT Inc(s,Q(j,a)) OR Inc(C(s,j,W(s,j,a)),a).

The closure-versus-counterexample clauses are:

    10. G(b,t) OR R(b,t,F(b,t),Y(b,t,u)).
    11. G(b,t) OR E(Z(b,t,u),Y(b,t,u)).
    12. G(b,t) OR NOT E(Z(b,t,u),u).

    13. NOT G(b,t) OR NOT E(x,H(b,t)) OR NOT R(b,t,x,y)
                      OR E(y,H(b,t)).
    14. NOT G(b,t) OR E(D(x),x) OR NOT R(b,t,x,y)
                      OR E(y,H(b,t)).
    15. NOT G(b,t) OR NOT E(y,H(b,t)) OR R(b,t,S(b,t,y),y).

Call the theory FC15. Each of the nine core clauses is one piece of the four
familiar assignment/class axiom groups. The last six clauses are a finite
Skolem presentation of a fifth axiom group. Numbering axiom groups is a
presentation choice; the fifteen universal clauses and their expanded
symbols are the meaningful payload.

The literal counts are 1,2,2,2,3,2,2,2,2,2,2,2,4,4,3: total 35. There are one
constant, twelve proper functions, and three non-equality binary predicates.
Every clause has at most four universally quantified variables. The maximum
proper-function term depth is three, after fully expanding R and q. Equality
occurs in the first two clauses and retains its full logical interpretation;
the stated 15/35 counts do not include equality-as-predicate congruence rows.

## 3. Four immediate core consequences

### 3.1 Exact class operations

Clauses 03--05 say exactly

    Inc(s,N(a,b)) iff NOT(Inc(s,a) AND Inc(s,b)).

Clauses 06--07 give the exact membership-atom class. Clauses 08--09 say exactly

    Inc(s,Q(j,a)) iff there exists z Inc(C(s,j,z),a).

The existential direction in the latter statement has the actual witness
W(s,j,a); no independence of the assignment s is asserted.

### 3.2 Two different selector values without a disequality axiom

NAND gives Inc(d,q) iff NOT Inc(d,d). If q=d, equality substitution makes a
proposition equivalent to its negation, contradicting classical logic.
Consequently FC15 proves d != q. No nonempty E-set or set-theoretic Infinity
axiom is used here.

### 3.3 Explicit injective pairing and arbitrarily many selectors

Define the term

    P(x,y) := C(C(d,d,x),q,y).

By clauses 01--02 and d != q,

    V(P(x,y),d)=x,      V(P(x,y),q)=y.

Hence P is injective in its two arguments. Put a_0=P(q,d) and
a_(n+1)=P(d,a_n), for each finite numeral n in the metatheory. P(d,-) is
injective, and a_0 is outside its range: applying V(-,d) to a putative equality
P(q,d)=P(d,x) yields q=d. Therefore the a_n are pairwise different. This is a
uniform sequence of finite equational proofs, using only the two projection
identities, not an internal infinite sequence or any recovered set schema.

For every prescribed finite m, at most two of a_0,...,a_(m+1) equal d or q.
Elementary finite case distinction therefore proves the existence of m
pairwise different selectors different from d and q. This existential supply
is enough to instantiate class coding. The argument does not assert that a
fixed, uniformly chosen ground term a_n avoids d and q in all models.

### 3.4 Realizing ordinary finite assignments

If j_1,...,j_m are different selectors, successive C updates to an arbitrary
starting assignment set V(-,j_i) to arbitrary prescribed values. Each later
update preserves earlier coordinates by clause 02. Thus there is no assumed
sort of already valid assignment objects and no need for all external
infinite assignments to be represented. Every required finite coordinate
pattern has a representative.

## 4. The six closure clauses are exactly the required interface

Write Empty(x) for forall z NOT E(z,x), and Sub(y,u) for
forall z(E(z,y) -> E(z,u)). For a fixed b,t, define

    SB_R := forall x exists u forall y (R(b,t,x,y) -> Sub(y,u)),

    Hull_R(c) :=
       [forall x,y (((Empty(x) OR E(x,c)) AND R(b,t,x,y)) -> E(y,c))]
       AND [forall y (E(y,c) -> exists x R(b,t,x,y))].

**Lemma.** Every FC15 model satisfies SB_R -> exists c Hull_R(c), for every
b,t. Conversely, any expansion satisfying the nine core clauses and all these
class-coded closure instances has an expansion by G,F,Y,Z,H,D,S satisfying
clauses 10--15. The converse uses ordinary choice of witnesses in the ambient
ZFC metatheory; no definability of those Skolem functions is required.

**Proof, forward.** Suppose SB_R holds. If G(b,t) were false, clauses 10--12
would say, for x=F(b,t), that every proposed bound u has an output
y=Y(b,t,u) with member z=Z(b,t,u) outside u. Applying SB_R to that x yields a
bound u and an immediate contradiction. Thus G(b,t) is true.

Set c=H(b,t). Clause 13 gives closure from recurrent inputs in c. If Empty(x),
then E(D(x),x) is false regardless of how D(x) was selected; clause 14 gives
closure from every empty input. Clause 15 supplies the supporting input
S(b,t,y) for every member y of c. Thus Hull_R(c) holds. Notice that no extra
axiom about D is needed for this direction.

**Proof, converse.** Set G(b,t) true exactly when SB_R holds. If it is true,
choose a promised hull H(b,t) and its support witnesses S(b,t,y). If it is
false, negating SB_R in classical logic gives

    exists x forall u exists y,z
        [R(b,t,x,y) AND E(z,y) AND NOT E(z,u)].

Choose F(b,t), then Y(b,t,u),Z(b,t,u), accordingly. Values of inactive Skolem
functions may be arbitrary. Choose D(x) to be some E-member of x whenever x
has a member, and otherwise any object. If x is nonempty, clause 14 is true
through E(D(x),x); if x is empty it follows from the seed closure of H. All
remaining clauses follow directly. The same D works for every b,t, which
justifies its unary arity. QED.

This branch device spends three short clauses on a counterexample to local
boundedness instead of blindly distributing the quantified antecedent. The
support clause 15 is essential. It has not been weakened to recurrence or to
an output merely appearing somewhere on a finite search trace.

## 5. Lower interpretation: every raw EPSC instance

Let M satisfy FC15. For any fixed equality-free finite formula phi in E,
choose different selector values j_v for all its variable names, after bound
variable renaming. Structural induction builds a class code t such that

    Inc(s,t) iff phi holds with each v interpreted by V(s,j_v),

for every assignment object s. Atomic E uses A; NAND uses N; and an
existential quantifier uses Q with its selector. Clauses 01--02 prove that C
updates the bound coordinate while preserving every other coordinate used
in the matrix. Negation, conjunction, implication, universal quantification,
and genuine falsity have standard finite translations into NAND and exists.
For example NAND(B,NAND(B,B)) is true at every assignment, and its NAND with
itself is false. No equality atoms are needed because the target raw EPSC
language is equality free.

Now take an arbitrary raw EPSC matrix phi(x,y,p_1,...,p_m), with unrestricted
finite parameters and quantifier complexity. Choose selector d for x and q
for y and different other selectors for its parameters and bound names.
Given actual parameter values, finite C updates produce an assignment b with
the prescribed parameter coordinates. The resulting class t satisfies

    R(b,t,x,y) iff phi(x,y,p_1,...,p_m)

for all x,y. The closure lemma therefore gives the actual EPSC instance for
phi. Thus the E-reduct of every FC15 model satisfies full raw equality-free
EPSC, including its support requirement and its seed from all empty objects.

The preceding construction is uniform in finite syntax. Class terms are
built by recursion on phi; selector-distinctness proofs and finite assignment
proofs have recursively generated finite derivations. This is stronger than
checking any fixed list of matrices, although no serialized proof translator
or Lean proof is delivered with this note.

By the existing ordinary ProveIt calibration of full raw EPSC (via the
hereditarily saturated interpretation), ZFC proves

    Con(FC15) -> Con(raw EPSC) -> Con(ZFC).

The use of that calibration must be cited explicitly. It is not a claim that
the arbitrary E-reduct itself is extensional or a model of ZF.

## 6. Upper interpretation: definable classes of a countable ZFC model

Work in ZFC and assume Con(ZFC). Completeness and the countable-model theorem
give a countably infinite set-coded model M of ZFC. The E relation of FC15 is
membership of M. No transitivity, external well-foundedness, or external
omega-standardness of M is assumed.

Choose d to be any object, for example M's empty set. Define V and C inside M
by ordinary pure membership formulas: normalize an assignment code to a
finite partial function graph when it is a valid such graph, and to the empty
graph otherwise. V returns the indicated value if present and a fixed
default otherwise. C replaces the indicated coordinate after normalization.
Use precisely the same normalization in both definitions. These operations
obey clauses 01--02 for every object, including invalid assignment codes.
Internally finite graphs of a nonstandard M cause no difficulty.

In the ambient ZFC metatheory, the family Def(M) of all subsets of M definable
by finite pure-E formulas with finite tuples of M-parameters is countable.
Choose a surjection t -> D_t from the domain of M onto Def(M), with repetitions
allowed. Interpret Inc(s,t) by s in D_t. NAND, membership of the definable V
values, and existential preimages under definable C are again pure-E
definable. Choose N,A,Q to name these classes and W to name the required
existential witnesses. These class-code and witness functions are selected
externally; they need not be E-definable within M.

The term q=N(d,d) denotes an ordinary M-object different from d by the NAND
argument. For every fixed b,t, the relation R(b,t,x,y) is pure-E definable over
M with parameters. To see this, use one ordinary finite E-definition of D_t,
the E-definitions of V/C, and the actual objects b,d,q as parameters. No class
or expanded-language satisfaction predicate is used inside M.

ZF, and hence M, satisfies every pure-E instance of the empty-seeded positive
subset-closure scheme. One may use the already proved EPSC equivalence here;
alternatively the next paragraph gives the direct construction. Thus all
relations R(b,t,-,-) have a hull whenever they are locally subset bounded.
The converse direction of the six-clause lemma supplies G,F,Y,Z,H,D,S.
Therefore M expands to a model of FC15.

For completeness, the standard ZF construction is as follows. Under SB_R,
the fiber F_x={y:R(x,y)} is an actual set: select some b locally bounding
every output by subset, and separate F_x inside Power(b). Its exact extension
is unique, so Replacement supplies fiber images on any set without choosing
a family of arbitrary bounds. Put C_0=F_empty and
C_(n+1)=C_n union union{F_x:x in C_n}; take c=union_{n in omega} C_n. Every
empty object is the unique empty set, so seed closure holds. Replacement,
Union, and the finite-stage recursion give recurrent closure, while induction
shows every hull member belongs to some actual R-fiber, giving support. This
is an instancewise proof for every finite formula and every parameter tuple.

All objects and satisfaction relations just used are sets in the ambient
ZFC proof. The ordinary satisfaction recursion ranges over finite syntax in
that metatheory, not over a presumed standard natural-number part of M.
The enumeration t -> D_t need not be definable in M, and FC15 does not assert
comprehension or a satisfaction predicate for its expanded language. This
avoids the otherwise immediate truth/diagonalization pitfall of unrestricted
one-sorted class coding.

Consequently ZFC proves

    Con(ZFC) -> Con(FC15).

Combined with the lower direction,

    ZFC proves Con(FC15) iff Con(ZFC).

This is an ordinary internalizable model/completeness argument, not a claim
that a machine or proof assistant has checked its arithmetized endpoint.

## 7. Guard fusion and two alternative payloads worth measuring

### 7.0 The ten-function intermediate payload

The functions F and H have the same argument list (b,t), and their constraints
occur under opposite values of exactly the same branch flag G(b,t). Therefore
use the single symbol H for both. Similarly, S and Y have the same argument
list (b,t,z), and their constraints are mutually exclusive under the same
flag; use the single symbol Y for both. The only changed clauses are

    10. G(b,t) OR R(b,t,H(b,t),Y(b,t,u)).
    15. NOT G(b,t) OR NOT E(y,H(b,t)) OR R(b,t,Y(b,t,y),y).

All other displayed clauses are unchanged. The resulting signature consists
of V,C,N,A,Q,W,H,Y,Z,D: ten proper functions, one constant, three predicates.

The proof is exact model conversion. Given an unshared model, define the new
H(b,t) as old H(b,t) when G(b,t), and old F(b,t) otherwise. Define new Y(b,t,z)
as old S(b,t,z) when G(b,t), and old Y(b,t,z) otherwise. Every active literal
has its old value, while inactive constraints are already true through the
guard. Conversely, expand a shared model by putting F=H and S=Y. Thus the
two finite theories are equiconsistent by a ZFC-provable direct construction.

More generally, two same-arity Skolem functions can be identified when every
constraint for one is active only under B(key), every constraint for the other
is active only under NOT B(key), and the key is determined by their common
argument list. This last condition matters: different contexts must not ask
the same tuple of function arguments to take incompatible values. The present
fusions have the literally identical key (b,t), so no such collision occurs.
The claim does not license arbitrary merging of unrelated witness functions.

With the compact equality-as-predicate completion described by the parent
implementation, the unshared 15/35 presentation becomes 32 clauses/91 literals;
the shared one becomes 30 clauses/84 literals. Native equality remains the
meaning of the original 15 rows. These counts include congruence for every
retained proper function and non-equality predicate, not the optional unused
constructor tags in the numerical term representation.

### 7.0a A definable member selector

One can also remove D by the exact term

    D*(x) := W(C(d,q,x),d,A(d,q)).

Indeed, if z in x, put s=C(d,q,x). The assignment laws give
V(C(s,d,z),d)=z and V(C(s,d,z),q)=x, since d != q. The atom and existential
class clauses imply Inc(s,Q(d,A(d,q))). Clause 09 then supplies the witness
W(s,d,A(d,q)), whose atom-class meaning is precisely D*(x) in x.
Thus D* selects a member whenever one exists. Replacing D by this term is
equiconsistent: every model without primitive D can be expanded using D*,
while the nine core rows already prove that this value satisfies the member
selector property needed by the upper construction and seed clause.

This yields the recommended nine-function target after guard fusion, still
15/35 native and 29/82 after the stated equality completion. The expanded
source term grows by eleven term nodes in clause 14. With a fixed five-bit
term opcode this would add sixteen bits to the completed template, but that
pricing misses a threshold: six variable codes, one constant and nine proper
functions fit in sixteen opcodes. A four-bit term format is now available.
The complete template therefore shrinks from 1920 bits for the ten-function
control to 1616 bits (202 bytes) for the nine-function target, including
equality completion. Native term-node count is 182 and complete count 320.
This is a saving in a declared static representation, not a machine-state
bound. The final LaTeX theory section uses this nine-function version.

### 7.1 Remove the branch predicate at the cost of one function

Replace every G(b,t) by Inc(d,B(b,t)), where B is a new binary function.
Since Inc(d,d) and Inc(d,q) have opposite truth values, one of d,q codes each
desired flag value at d. Any FC15 model expands by choosing B accordingly,
and every model of the substituted clauses gives an FC15 model by defining
G through Inc(d,B(b,t)). This is a direct equiconsistency transformation.

The result has 15 clauses, 35 literals, one constant, thirteen proper
functions before guard fusion, eleven after fusion, and the two original
non-equality predicates E/Inc. Its maximum
term depth is still three. It exchanges predicate dispatch for a binary term
constructor and longer literals; only a full compiler comparison decides
which representation is cheaper.

### 7.2 An extensional control with a simpler lower proof

Add a binary function X and two clauses:

    a=b OR E(X(a,b),a) OR E(X(a,b),b),
    a=b OR NOT E(X(a,b),a) OR NOT E(X(a,b),b).

For unequal a,b these require exactly one of the two membership literals;
they are a Skolemization of Extensionality. In this control the E-reduct has
Extensionality and full EPSC, hence is directly a model of ZF without
Foundation or Choice. No raw hereditary interpretation is needed for that
lower step. Standard Foundation and constructibility relative-consistency
interpretations then finish the calibration. The upper model supplies X.

This control has 17 clauses and 41 literals, one constant, thirteen proper
functions before guard fusion and eleven after fusion, and three predicates;
the predicate-eliminated version has fourteen before fusion or twelve after
fusion, and two predicates. The choice between the smaller raw
payload and the simpler calibration proof should be explicit.

### 7.3 A sixteen-clause extensional target without a new function

A later refinement gives a direct extensional calibration with the same nine
functions as the primary raw target. Define the term abbreviations

    Xor(u,v) := N(N(u,N(u,v)),N(v,N(u,v))),
    T_j := Xor(A(j,d),A(j,q)).

Add the single universally quantified clause

    j=d OR j=q OR a=b
        OR Inc(C(C(d,d,a),q,b),Q(j,T_j)).

Call the result FC16*. Over the nine core clauses, the new clause is
deductively equivalent to ordinary Extensionality. Indeed, when j differs
from d and q, the updated assignment C(C(C(d,d,a),q,b),j,z) has values
z,a,b at j,d,q. The exact atom, NAND and existential-class laws therefore
identify the last literal with

    exists z [E(z,a) XOR E(z,b)].

The core supplies a selector j avoiding d,q, so the new clause forces a
distinguishing member for each unequal a,b. Conversely Extensionality
supplies such a member whenever none of the three equality guards is true.
The guards cover all colliding selector assignments. No new Skolem witness
or class operator is assumed: Xor and T_j are literal expanded terms.

Thus the direct lower proof in extensional_control_proof.md applies to FC16*
unchanged, and its upper model is the same extensional countable ZFC model.
ZFC proves Con(FC16*) iff Con(ZFC), without using the raw hereditary
interpretation. This version is a useful main proposal when that shorter
calibration dependency is preferred.

Native metrics are16clauses/39literals/230termnodes/nineproperfunctions;
complete equality metrics are30clauses/86literals/368termnodes. The added
clause has48termnodes and maximum term depth six. The complete four-bit
template is1823bits, padded to228bytes. Native template is1088bits. The
explicit-X seventeen-clause control is retained as a comparison.

The finite Change-row deletion countermodels are scoped to FC15* and the
explicit-X FC17*, not automatically to FC16*. They have extensional
E-reducts, but equivalence between the coded new clause and Extensionality
itself uses the Change laws being deleted. No such extrapolation is made.

## 8. Ground refutation semantics and the machine endpoint

The signature has a constant. Enumerate all ground substitutions into these
fixed clauses, including all colliding substitutions. At stage n form the
finite set of instances over the first n terms and decide its satisfiability
in equality with uninterpreted functions and predicates. The exact finite
decision procedure may enumerate partitions of the observed ground subterms,
require function congruence on all repeated argument tuples, and enumerate
predicate truth values on argument classes. Cyclic term identifications are
allowed. This is the same equality semantics used in the earlier FAK12
reference; syntactic term equality would be incorrect.

If the clause theory has a model, every stage is satisfiable. If every stage
is satisfiable, compactness gives a model of all ground instances, and its
constant-generated substructure satisfies every universal clause. Thus the
ideal search halts exactly when FC15 is inconsistent. The entire argument
formalizes in ZFC and yields a semidecision specification equivalent to the
inconsistency of ZFC. All data emission, total term/partition enumeration,
congruence checking, truth evaluation, and blank initialization must still be
implemented and included before any binary state count can be claimed.

Compared with source34 FAK12's 28 clauses and 62 literals, FC15 uses 15 and
35, reductions of 13 clauses and 27 literals. The final guard-fused target
with derived member term reduces proper functions 15 -> 9 and constants
2 -> 1, while adding one branch predicate. Maximum universal-variable
count drops 5 -> 4. These are exact logical payload metrics. They do not imply
proportional reduction in the code of the term/equality search, and they do
not imply a machine with fewer than 253 working states.

## 9. Primary and project references

* Harvey M. Friedman, Impossible Counting, 2 September 2017, Section 4.1,
  particularly the assignment and class operations; Theorem 4.2.3 for the
  original finite-theory consistency calibration:
  https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/ImpossibleCnt090217-2a5ewhm.pdf
* ProveIt source34, finite_kernel_notes.md, for FAK12's twelve groups and
  exact 28-clause payload:
  https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/34-k12-theory-finite_kernel_notes.md
* ProveIt source26, observational_pairing.md, for the precise raw EPSC
  convention and its full-parameter calibration:
  https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/26-oneparam-research-theory-observational_pairing.md
* ProveIt source26 intake review, for the scope of the inherited raw EPSC
  hereditary-saturation calibration and its unformalized internalization:
  https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-152-source-26.md

Suggested next experiments: compare the 15-clause raw and 17-clause extensional
controls; compare predicate G with class-coded flag B; design a single shared
ground-term walker with genuine congruence; separately measure full payload
printer and blank initialization. A proof-code translation or a formalized
class construction would make the logical calibration independently reusable.
