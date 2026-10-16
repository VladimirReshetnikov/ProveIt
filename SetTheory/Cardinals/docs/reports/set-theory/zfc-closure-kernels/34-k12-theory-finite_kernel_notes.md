# A finite assignment kernel for the consistency-machine programme

Research date: 16 October 2026. This is an ordinary mathematical construction with
an explicit executable clause payload, not a Lean/Coq theorem, a binary compiler,
or a new Turing-machine state record. It develops a finite-theory alternative
already mentioned in ProveIt's source 18, for which that source supplied no fixed
payload. The assignment/class-coding idea is due to Harvey Friedman; the present
artifact fuses projection into the two set-existence interfaces and gives a
self-contained equiconsistent presentation with exact set operations. No historical
priority claim is made for the resulting finite presentation.

## 1. Primary provenance and a transcription issue

Harvey M. Friedman, *Impossible Counting*, 2 September 2017, Section 4.1 gives the
finite theory K1 with assignment evaluation V, single-coordinate change C, a
second membership relation epsilon coding definable classes, Boolean closure,
atomic membership, existential quantification, and projection. Theorem 4.2.3
states ZFC equiconsistency for K1T2, arguing in ACA0. Later Sections 4.2--4.3
convert to one four-place function and seven variables.

Primary URL:
https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/ImpossibleCnt090217-2a5ewhm.pdf

Relevant printed pages: 20--24 (K1 and formula coding), 26--28 (T1, T2 and
consistency), 29--37 (subsequent transformations). The displayed T[3,8] on printed
page 34 has a free z while its prefix lists x,y,w,v,u; it also changes the
preceding matrix's variable roles. This was verified on the rendered primary
page, not inferred only from extracted PDF text. It is a local transcription
issue, not a claim that the paper's global theorem is false. The payload below
does not transcribe that table. Its scopes and Skolem dependencies are given
directly, and its consistency proof uses the following twelve axioms.

Friedman's separate 2020 class-theory paper and the source-17 tagged Capture
repair are not required by this construction.

## 2. The exact twelve axioms

Work in ordinary one-sorted classical first-order logic **with equality**. The
domain is nonempty. There are two binary predicates E and epsilon, two constants
e,I, and five initial function symbols:

| Symbol | Arity | Intended role in an upper model |
|---|---:|---|
| V | 2 | value of a finite partial assignment, default e |
| C | 3 | update an assignment at one selector |
| Pair | 2 | exact unordered pairing |
| Union | 1 | exact union |
| Power | 1 | exact power set |

Let

    rho(b,t,x) = epsilon(C(b,e,x),t),
    sigma(b,t,x,y) = epsilon(C(C(b,e,x),I,y),t),
    succ(x) = Union(Pair(x,Pair(x,x))).

These are abbreviations for terms/formulas, not new primitives. All displayed
free variables in the following axioms are universally closed.

1. **Change.**

       V(C(s,j,z),j)=z
       and [k != j -> V(C(s,j,z),k)=V(s,k)].

2. **NAND classes.**

       forall a b exists t forall s
         [epsilon(s,t) <-> not(epsilon(s,a) and epsilon(s,b))].

3. **Atomic classes.**

       forall j k exists t forall s
         [epsilon(s,t) <-> E(V(s,j),V(s,k))].

4. **Existential classes.**

       forall j a exists t forall s
         [epsilon(s,t) <-> exists z epsilon(C(s,j,z),a)].

5. **Empty object.** `forall x not E(x,e)`.

6. **Extensionality.**

       forall a b [(forall x (E(x,a) <-> E(x,b))) -> a=b].

7. **Exact Pairing.**

       forall a b x [E(x,Pair(a,b)) <-> (x=a or x=b)].

8. **Exact Union.**

       forall a x [E(x,Union(a)) <-> exists z (E(z,a) and E(x,z))].

9. **Exact Power.**

       forall a x [E(x,Power(a)) <-> forall z (E(z,x) -> E(z,a))].

10. **Ordinary Infinity.**

        E(e,I) and forall x [E(x,I) -> E(succ(x),I)].

11. **Direct Separation.**

        forall a b t exists h forall x
          [E(x,h) <-> (E(x,a) and rho(b,t,x))].

12. **Direct partial Collection.**

        forall a b t exists d forall x
          [(E(x,a) and exists y sigma(b,t,x,y))
            -> exists y (E(y,d) and sigma(b,t,x,y))].

Call this finite theory FAK12. Its only class-coding axioms are 1--4. In
particular, there is no class predicate saying that *all arbitrary external
subsets* have codes, no truth predicate for FAK12 itself, and no schema ranging
over the expanded E/epsilon/V/C language. The absence of that expanded-language
comprehension is essential to the upper-model proof.

Axioms 5 and 10 imply e != I. Thus the two distinguished assignment coordinates
used by Collection are different. The use of exact Pair and Union makes the
term succ(x) the ordinary x union {x}; no weak-pair or non-well-founded version
of Infinity is assumed equivalent without proof.

## 3. Formula coding in every model

**Lemma 1 (unbounded supply of selector values).** Empty and exact Pairing imply
that the domain has arbitrarily many distinct selector values; no use of the
Separation or Collection schemas is needed.

Proof. Put s(x)=Pair(x,x). Exact Pairing says E(x,s(x)), so Empty gives s(x)!=e.
If s(x)=s(y), membership of x in their common singleton gives x=y. Therefore
s is injective and e is outside its range. For each external finite n, the
values e,s(e),...,s^n(e) are pairwise distinct: a purported repetition cancels
to e=s^k(e), k>0, which is impossible. Starting with a sufficiently long finite
initial segment and omitting e and I supplies any prescribed finite number of
additional labels. At most two values have been omitted. This is a uniform
finite argument in the ambient ZFC metatheory, not an assumption that the
interpreted set universe already satisfies an unproved schema.

There is also an independent argument from Change and NAND alone. NAND rules
out a one-element domain. A finite n-element domain, n>=2, would let Change
realize all n^n assignments at its n distinct selectors with only n assignment
objects, contradicting n^n>n. The singleton argument is sufficient here.

**Lemma 2 (formula-code existence).** Let M satisfy axioms 1--4. Let phi be any
fixed finite formula in E, without equality, and assign distinct selector values
d_v in M to all its variable symbols, after capture-avoiding alpha conversion
of bound variables if necessary. There is an object t such that, for every
assignment object s,

    epsilon(s,t) iff phi is true when v has value V(s,d_v).

Proof is an induction on the finite syntax tree. For E(v,w), use axiom 3 with
selectors d_v,d_w. Axiom 2 realizes NAND; negation is NAND(A,A), and the usual
Boolean connectives are finite NAND expressions. For exists v psi, use axiom 4
with selector d_v and the already obtained code of psi. Axiom 1 says that
C(s,d_v,z) has precisely the required changed values at every selector used by
the matrix. This proves the existential step for all z in M, not only values
coming from a special sort or fresh names. Lemma 1 supplies as many distinct
selectors as the finite formula needs.

For a formula with equality, replace each equality a=b by

    forall z (E(z,a) <-> E(z,b))

using a fresh bound variable. Extensionality makes this replacement valid.
Thus Lemma 2 applies to every ordinary set-theoretic formula after this
effective equality erasure. Formula coding here is a metatheorem; it does not
assert an internal satisfaction predicate for the expanded theory.

## 4. Lower direction: recover the full set-theoretic schemas

Let M model FAK12. For an arbitrary set-theoretic formula phi(x,p_1,...,p_k),
give x selector e and the parameters mutually distinct selectors different from
e. Use Lemma 2 to obtain its code t. Starting with any assignment, use finitely
many C updates to construct b with V(b,d_i)=p_i. Consequently rho(b,t,x) agrees
with phi(x,p_1,...,p_k) for every x in M. Axiom 11 therefore gives the full
Separation instance, with every parameter and every finite quantifier pattern.

For arbitrary phi(x,y,p_1,...,p_k), use selectors e and I for x,y, and distinct
remaining selectors for the parameters and renamed bound variables. Since
e!=I, Change gives

    sigma(b,t,x,y) iff phi(x,y,p_1,...,p_k).

Axiom 12 gives partial Collection. On a set a where every x has an output, this
is the usual Collection statement. Full Separation then cuts out the exact
image of a functional relation, giving Replacement. Empty, Extensionality,
Pairing, Union, Power and ordinary Infinity are already axioms. The E-reduct
is therefore a model of ZF without Foundation or Choice. We do **not** call it
a model of ZF with Foundation at this step.

The standard relative-consistency reductions through well-founded sets and
the constructible universe then give Con(ZFC). These reductions are available
within ZFC; the upstream jeff87654/busy-beaver ZF development gives derivation
level versions in stdzf_r3/regcon and stdzf_r3/zfc. No additional large-cardinal
or soundness hypothesis is introduced.

## 5. Upper direction: definable classes of a countable model

Argue inside ZFC, assuming Con(ZFC). By completeness and downward
Lowenheim--Skolem, choose a countably infinite set-sized model M of ZFC. It need
not be transitive or omega-standard. Interpret e as its empty set, I as its
omega, and Pair, Union, Power as the ordinary operations of M.

Define V and C *inside M by ordinary set formulas*. A valid assignment code is
an M-finite partial function graph. V(s,j) is its value at j when defined, and
e otherwise. Invalid assignment codes are treated as the empty graph. C(s,j,z)
is a code for that normalized graph, with any old pair at j removed and the
pair (j,z) inserted. Thus Change holds for every s,j,z,k, including invalid
codes. M-finiteness suffices; external standardness of its finite graphs is
not needed.

In the ambient ZFC metatheory, let Def(M) be the family of subsets of the domain
definable over the E-reduct of M by finite E-formulas with finite tuples of
parameters. This is a countable family: both M and the ambient finite-formula
syntax are countable. Choose a surjection d |-> D_d from M onto Def(M), with
repetitions allowed, and define epsilon(s,d) iff s belongs to D_d.

NAND preserves E-definability. The class

    {s : E(V(s,j),V(s,k))}

is E-definable with parameters j,k, because V is E-definable in M. Likewise,
if D_a is E-definable, then

    {s : exists z [C(s,j,z) belongs to D_a]}

is E-definable with finitely many parameters. Thus axioms 2--4 hold by the
surjectivity of the class-code map.

For fixed b,t, the predicates rho(b,t,x) and sigma(b,t,x,y) are also E-definable
with parameters in M: take a formula defining D_t and substitute the
E-definable C operations. M's ordinary Separation and Collection prove exactly
axioms 11 and 12. There is no invocation of Separation or Collection for an
arbitrary external class: each particular code t has an ordinary finite
E-definition. There is likewise no assertion that the enumeration d |-> D_d
is definable *inside M*, or that d is M's own formula code.

All constructions just described concern sets and ordinary satisfaction in the
ambient ZFC universe, so they formalize there. The resulting expansion is a
model of FAK12.

**Theorem.** ZFC proves

    Con(FAK12) <-> Con(ZFC).

Proof. Completeness turns Con(FAK12) into a model, Section 4 gives a model of
ZF minus Foundation/Choice, and the usual relative-consistency bridges yield
Con(ZFC). Section 5 proves the reverse implication. This is the requested
level of internal consistency comparison. A primitive-recursive translation of
serialized proofs would be a further stronger artifact; it is not required by
the stated user target and is not asserted to have been produced here.

## 6. Exact universal clause payload

`finite_assignment_kernel.py` emits a Skolemization of the twelve axioms as 28
universally closed clauses. It uses genuine equality and 15 proper function
symbols, whose arities are 2 unary, 8 binary, 4 ternary and 1 quaternary, besides
the two constants and two binary predicates. The clauses have at most five
universally quantified variables each, 62 literal occurrences, 244 term-node
occurrences, and maximum term depth 3. These are syntax measurements with the
declared representation; they are **not Turing-machine states**.

The additional functions are NAND/atomic/existential class-code constructors,
an existential-class witness, an extensionality counterexample witness, union
and power counterexample witnesses, a separation-set constructor, a collection
bound constructor, and a collection witness. The exact collection witness is

    CollectWitness(a,b,t,x),

not a function of an additional antecedent witness y. Its two emitted clauses
are, writing f for this term and B=Collect(a,b,t),

    not E(x,a) or not sigma(b,t,x,y) or E(f,B),
    not E(x,a) or not sigma(b,t,x,y) or sigma(b,t,x,f).

They assert one suitable chosen output for each x whenever any output exists;
choice of f may depend on a,b,t,x and needs no dependence on the displayed
antecedent witness. For fixed a,b,t,x, the miniscoping step is

    [(exists y eta(y)) -> exists z good(z)]
       iff exists z forall y [eta(y) -> good(z)].

If eta has a witness, choose a good output; if it has none, choose any object
from the nonempty domain. The extra condition E(x,a) can be included in eta.
This proves the displayed equivalence and the omitted y-dependence. It is
standard Skolemization over a nonempty domain.
The corresponding higher-level quantifier proof is explicit, rather than
hidden in an implementation that silently drops dependencies.

Extensionality is encoded by a witness d(a,b). If a!=b, exactly one of
E(d(a,b),a), E(d(a,b),b) must hold. The pair of clauses has been checked against
the complete eight-case Boolean table. Other biconditionals are expanded by
the listed positive and negative clauses. All variables are inferred from
actual terms before universal closure, so there are no free schematic names.

Every model of the universal clauses reduces to a model of FAK12. Conversely,
inside ZFC a countable FAK12 model has choices of all Skolem witnesses and hence
an expansion to the clause theory. Therefore its arithmetized consistency is
equivalent to Con(FAK12), provably in ZFC. The payload does not claim Friedman's
more compressed one-function/seven-variable signature: it is a concrete,
independently specified input before that additional compiler work.

## 7. A complete finite-ground feasibility search

The clause set supports a search with no run-time quantifier calculus and no
run-time set-theoretic schema generator. Enumerate ground terms over the fixed
signature; constants e,I ensure a nonempty term universe. At stage n instantiate
each clause with all tuples of terms in the first n-term prefix, allowing
different variables to receive the same term. Test satisfiability of that
finite set of ground clauses in equality with uninterpreted functions and the
two predicates. Halt at the first unsatisfiable stage.

Here is an elementary exact finite test, implemented as a deliberately small
Python reference. Collect all ground subterms S, and enumerate all partitions
of S. Reject partitions violating function congruence: if f(t_1,...,t_k) and
f(u_1,...,u_k) both occur and every t_i,u_i share a block, their resulting terms
must share a block. Then enumerate truth values for each predicate applied to
the observed argument-block tuples. Equality literals use block identity;
predicate values must agree on equal argument tuples. Accept feasibility if
some such choice satisfies every clause.

**Finite-test correctness.** A model induces precisely such a partition and
truth assignment. Conversely, form a finite domain of the partition blocks.
An observed function application specifies its value on the tuple of argument
blocks; congruence makes this well-defined. Give every unobserved tuple any
fixed block as default value. Extend predicate values arbitrarily on unused
tuples. Induction on ground terms proves that every observed term has its
declared block as value, so the resulting finite structure satisfies the
ground clauses. Cyclic identifications such as Pair(e,e)=e are allowed in this
test unless the actual ground axioms forbid them; an occurs check would be
incorrect for equality with uninterpreted functions.

**Exhaustive-search correctness.** If the universal theory has a model, every
stage is feasible. Conversely, if every stage is feasible, all finite sets of
ground instances are satisfiable. By first-order compactness, all ground
instances have a common model. Restrict that model to the substructure generated
by the constants. Every element of this substructure is the value of a ground
term, so every universal clause holds there. Thus the universal theory has a
model. Each stage test is finite and terminating, and the enumeration covers
all ground substitutions. Combining this proof with first-order completeness
and the consistency calibration proves, in ZFC, that the ideal algorithm halts
exactly when ZFC is inconsistent.

This common-domain grounding includes all colliding substitutions. The
retired finite-sort semantics cannot validate it by assigning different
variable labels different domains. Equality is also treated semantically by
congruence, not reduced to syntactic term identity.

## 8. Executed scope, remaining cost, and comparison

The generator and audit ran successfully. Their eight tiny controls cover the
empty theory, an empty clause, equality reflexivity, distinct constants,
function congruence, predicate congruence, permissible cyclic term equality,
and incompatibility of e=I with the actual Empty/Infinity rows. The full
extensionality-witness truth table passed. These are diagnostics of concrete
risks, not a proof of the Python interpreter or a consistency test for FAK12.
No whole-kernel consistency search was run.

The useful new artifact is the fixed, fully scoped 28-clause input with a direct
ZFC-level calibration argument. Projection has moved into the set-existence
interfaces, eliminating one separate class axiom; Collection acquires a
four-argument Skolem witness. That tradeoff may increase a particular machine's
state count. It must be measured with the full data printer, term enumerator,
partition enumerator, congruence checks, predicate assignments, truth evaluator,
and blank-tape initializer. No numerical state saving is inferred from the
twelve-axiom count or from the omission of a run-time formula schema.

Recommended next implementation experiment: compile this fixed clause input
using one shared term walker and compare total initialized binary tables with
the complete EPSC2/tableau and protected-rule controls. An alternative is to
extend the payload extractor to a corrected, explicit four-place-function
coding; that conversion needs its own collision/constant-domain audit.

## Sources and exact repository context

* Friedman (2017), primary PDF above, especially K[1,1]--K[1,5] and Theorem 4.2.3.
* ProveIt `intake-149-source-18.md` and the batch-149 host note: finite universal
  alternatives already proposed, fixed payload absent. This artifact advances
  that input, not the already known abstract possibility of finite theories.
* ProveIt `raw_psc.md`: equality-free PSC, EPSC2 and protected rules already
  established as ordinary proposals; they are distinct from FAK12.
* https://github.com/jeff87654/busy-beaver/tree/main/ZF/stdzf_r3/regcon/
* https://github.com/jeff87654/busy-beaver/tree/main/ZF/stdzf_r3/zfc/

No remote files were modified.
