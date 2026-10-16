# A bounded-parameter subworld kernel

Research notes, 16 October 2026. These are ordinary mathematical arguments,
not a checked Lean/Coq development or a newly compiled Turing machine.

## Result and scope

There is a concrete alternative to the PSC/CP/GIC theory stencils currently
studied in ProveIt. Work in classical first-order logic **with actual logical
equality**, one binary relation `E`, and one distinguished constant `W`.
Two schemes with at most three free matrix variables suffice. An inhabited
variant of separation eliminates a separate nonemptiness sentence. No
Extensionality is needed for the finite-parameter reduction, or for the
bisimulation interpretation below.

The resulting raw, equality-bearing theory interprets Friedman's extensional
`K(W)`. Conversely, it is a subtheory of `K(W)` after elementary logical
rewriting. Consequently its consistency is equivalent to that of ZFC in ZFC.
The new argument is explicit about the source equality, weak products,
constant, parameter restrictions, and absence of a machine-state result.

The formulas are genuinely schemes: the number and names of BOUND variables
in the matrix remain unrestricted. Three free slots do not mean
three-variable logic and do not produce a finite axiomatization.

## 1. Exact joined template

Write `x in y` for `E(x,y)`. Choose distinct variable names `a,b,z,x,y`.
The matrix `phi(a,b,z)` is an arbitrary formula in the language `{E,=}`:
it has no literal occurrence of the constant `W`, and all its free variables
are among `a,b,z`. Its bound variables are unrestricted. In particular,
`x,y` do not occur free in `phi`; bound occurrences of these names are harmless.

Put

    Exact_phi(x,y,z) :=
      (z in y -> (z in x AND phi(a,b,z)))
      AND (z in x -> (phi(a,b,z) -> z in y)).

This is just `z in y <-> (z in x AND phi)`, with the reverse direction
curried before expanding conjunction into implication and falsity.

Define

    Splus_phi := EXISTS y [y in W AND
                  (x in W -> FORALL z Exact_phi(x,y,z))],

    R2_phi := a in W -> (b in W ->
               (phi(a,b,z) -> EXISTS z [z in W AND phi(a,b,z)])).

The free `z` in the antecedent of `R2_phi` is rebound ONLY in its consequent.
The same matrix is therefore copied literally: no free substitution of a
fresh witness variable is hidden in the displayed template.

The raw theory `S2plus` consists of the universal closures, excluding the
constant `W`, of

    A_phi := Splus_phi AND R2_phi.

The open joined formula has free variables among `a,b,x,z`, so one possible
closure is `FORALL a FORALL b FORALL x FORALL z A_phi`.

For an extensional control, add to the same joined formula

    EXT(a,b) := (FORALL z [z in a <-> z in b]) -> a=b.

Variable names must be distinct where needed for capture avoidance. Their
VALUES are completely unrestricted and may coincide. In particular, the
proofs repeatedly use tuples with repeated coordinates. A finite-sort engine
that cannot instantiate variables at already present values does not prove
the required theorem.

## 2. Inhabitation is absorbed by moving one guard

For each fixed matrix, the usual restricted separation clause is

    SS_phi := x in W -> EXISTS y [y in W AND
                                  FORALL z Exact_phi(x,y,z)].

In nonempty classical first-order logic,

    Splus_phi <-> ((EXISTS u u in W) AND SS_phi).

The forward direction projects the existential witness, and under `x in W`
it projects the separation assertion. Conversely, if `x in W`, use `SS_phi`;
if not, any witness to `W` being inhabited serves. The output variable `y`
is not free in the guard. This is a classical case split, with no Choice.

Thus no separate nonemptiness axiom is required by `S2plus`. The ordinary
guarded `SS2+RED2` without either nonemptiness or this change is too weak:
a one-element universe with empty membership and `W` its sole object models
both guarded schemes. Full `RED` includes its zero-parameter case; applying
that case to `z=z` proves nonemptiness. The inhabited separation stencil
packages that consequence without printing another existential sentence.

## 3. The finite-parameter reduction, without Extensionality

Let `S` denote full subworld separation and reducibility, in classical logic
with equality:

    SS: x in W -> EXISTS y in W FORALL z
          [z in y <-> (z in x AND psi(z;parameters,W))],

    RED_n: p1,...,pn in W ->
          ((EXISTS t theta(p1,...,pn,t)) ->
           EXISTS t in W theta(p1,...,pn,t)),

where the `SS` output is fresh, and `theta` does not mention `W` and has no
other free variables. There is an instance for every finite `n`, including
zero. **Theorem:** `S2plus` and `S` prove the same sentences of `{E,=,W}`.

### Step A: exact pairs inside W

Nonemptiness is already available. If `a,b in W`, the formula
`a in t AND b in t` has a witness `t=W`. Its matrix does not mention `W`.
`RED2` supplies a container `t in W`. Apply `SS2` inside this container with
the matrix `z=a OR z=b`. The resulting object belongs to `W` and has exactly
the literal members `a,b`. This works when `a=b` as well.

Repeating the construction gives within `W` representatives of
`{a}`, `{a,b}`, and `{{a},{a,b}}`. Distinct coextensional representatives
are permitted: no uniqueness of set objects is used.

### Step B: exact Kuratowski codes have unique endpoints

Define `PairExact(t,a,b)` by `FORALL z(z in t <-> (z=a OR z=b))`, and define

    OP(t,a,b) := EXISTS u,v
       [PairExact(u,a,a) AND PairExact(v,a,b) AND PairExact(t,u,v)].

This formula is `W`-free. In pure equality logic,

    OP(t,a,b) AND OP(t,a',b') -> (a=a' AND b=b').

Here is a proof that does not appeal to Extensionality. For any code `t` of
`(a,b)`, the intersection of the extensions of its members is exactly `{a}`:

    FORALL q(q in t -> z in q) <-> z=a.

The extension union is exactly `{a,b}`:

    EXISTS q(q in t AND z in q) <-> (z=a OR z=b).

The first equivalence gives `a=a'`. The second then gives `b=b'`, splitting
into `b=a` and `b!=a` if necessary. These are statements about literal
elements of one object, not an identification of coextensional objects.

Iterated ordered pairs give `W`-free tuple formulas `Tuple_n(t;p1,...,pn)`
with uniquely determined coordinates for each fixed `t`. Whenever all
coordinates belong to `W`, a suitable tuple code belongs to `W` as well.
For `n=1`, the code can simply be the coordinate. Coding and all its
uniqueness proofs are obtained by a finite induction on `n`.

### Step C: all reducibility arities

`RED2` gives `RED1` by using an unused second parameter from nonempty `W`;
the same padding gives `RED0` for formulas with no parameters.

Fix `p1,...,pn in W`, an associated tuple `t in W`, and a witness to
`theta(p1,...,pn,v)`. Apply `RED1` at `t` to

    EXISTS q1,...,qn
       [Tuple_n(t;q1,...,qn) AND theta(q1,...,qn,v)].

This is `W`-free, with only `t,v` free. The reflected output belongs to `W`.
Tuple endpoint uniqueness identifies its recovered coordinates with the
original `p1,...,pn`. This proves `RED_n` for every `n`.

### Step D: upward transfer of universal assertions

Full `RED` has the following useful consequence. For every `W`-free formula
`eta(p1,...,pn)`,

    [FORALL p1,...,pn in W eta] -> FORALL p1,...,pn eta.

If the conclusion failed, successively apply `RED0,RED1,...` to the
existential counterexample, moving one counterexample coordinate at a time
into `W` while retaining all previously moved coordinates. The result
contradicts the antecedent. This proof does not use relativized truth,
Extensionality, global Pairing, or global Separation.

Apply this to the `W`-free statement that an exact pair of `a,b` exists.
Step A proves its premise, so **global exact Pairing** follows.

### Step E: all separation parameters, including W

Given any full `SS` matrix, use global Pairing to code ALL its parameters
into a single tuple `t`. Include the source object `x` if it occurs in the
matrix, and include the actual object `W` if the constant occurs. Replace
these parameters by bound decoding variables. The resulting formula

    chi(z,t) := EXISTS q1,...,qn
                 [Tuple_n(t;q1,...,qn) AND psi_replaced(z;q1,...,qn)]

has only `z,t` free and no literal `W`. At the chosen code `t`, endpoint
uniqueness proves `chi(z,t) <-> psi(z;original parameters,W)` for every `z`.
Use `SS2` with `chi` and recover the requested full separation instance.
The tuple `t` may lie outside `W`: the separation parameter slots are
unguarded. No attempt to place the object `W` itself inside `W` is needed.

This completes the difficult inclusion. The converse follows because full
`RED0` gives nonemptiness, full `SS` gives restricted `SS2`, and Section 2
gives `Splus`. No step of this theorem uses Extensionality.

The construction is uniform on finite syntax. With standard arithmetizations,
the proof translations can be generated by primitive-recursive recursions
on formulas, tuple lengths, and derivations, with PA proving their correctness
by induction. This supports the PA-level consistency equivalence between
these two presentations. No serialized proof translator is supplied here.

## 4. A repaired raw-to-extensional interpretation

This section establishes the calibration for the equality-bearing raw theory;
it is not a deletion of the logical equality engine. It also avoids a gap in
Friedman's preliminary well-founded-comparison sketch, discussed below.

### 4.1 Resources derived in raw S

**Global Separation.** For a `W`-free separation matrix, full `SS` gives the
exact separation assertion absolutely whenever the source and parameters are
in `W`. Upward transfer from Step D makes it global. To allow a literal `W`
in the matrix, replace it by an ordinary universally quantified parameter
first, then instantiate that parameter at `W`.

**Transitivity of W.** For `x in W`, use `SS` to obtain `x' in W` whose
members are exactly the members of `x` that belong to `W`. If `x,x'` had a
different member, `RED2` at `x,x'` would give such a distinguishing member in
`W`, where they agree. Thus their incoming extensions coincide. Every member
of `x` therefore belongs to `W`. No equality of `x,x'` is inferred.

**Rooted transitive covers.** For `a in W`, the raw object `W` is a transitive
set containing `a`. The assertion `EXISTS u(Transitive(u) AND a in u)` is
`W`-free. Upward transfer proves it for every raw `a`.

**Weak Cartesian products.** A weak product of `x,y` is an object `P` such
that every `(a,b) in x times y` has at least one `OP` representative in `P`,
and every member of `P` is such a representative. It need not contain all
possible representatives. If `x,y in W`, transitivity gives their elements
in `W`; Step A supplies their ordered-pair codes in `W`. Global Separation
cuts the relevant codes out of `W`, giving the required `P`. The weak-product
existence assertion is `W`-free, so upward transfer makes it global.

**Representing definable relations.** Given a weak product `P` of `x,y`, any
definable relation `Q(a,b)` on `x times y` has a set code: separate from `P`
those `q` satisfying `EXISTS a in x EXISTS b in y(OP(q,a,b) AND Q(a,b))`.
Endpoint uniqueness ensures exactly the intended relation. This uses no
Choice and no set containing all pair representations.

These resources suffice below. In particular, no Power Set, Replacement,
Foundation, global choice of representatives, or universe-sized relation is
assumed by the interpretation.

### 4.2 Bisimulation on arbitrary transitive covers

For a relation-code object `R`, write `R[a,b]` for
`EXISTS q in R OP(q,a,b)`. A code is a bisimulation between transitive
objects `U,V` if every coded pair has endpoints in `U,V`, and each coded
pair `(a,b)` satisfies the forth/back conditions

    FORALL u in a EXISTS v in b R[u,v],
    FORALL v in b EXISTS u in a R[u,v].

Define `B(a,b)` to mean that some such `U,V,R` satisfy `a in U`, `b in V`,
and `R[a,b]`. This is one fixed first-order formula using only `E` and actual
equality. Crucially, its definition does not mention `W`.

`B` is an equivalence relation on ALL raw objects:

* A diagonal relation inside a weak product of a transitive cover with itself
  proves reflexivity.
* A reversed relation inside the reversed weak product proves symmetry.
* Given witnesses for `B(a,b)` and `B(b,c)`, separate their relational
  composition inside a weak product of the first and last covers. Whenever
  a middle object belongs to both middle covers, all its members do too, by
  transitivity. Forth and back therefore pass through the composition.

All these relation codes are produced by the definable-relation construction.
No uniform choice among witnesses is required.

The equivalence has the exact coinductive characterization

    B(a,b) <->
      [(FORALL u in a EXISTS v in b B(u,v)) AND
       (FORALL v in b EXISTS u in a B(u,v))].

The forward implication uses the same witnessing bisimulation for each
matched pair of children. For the converse, choose transitive covers `U,V`
of `a,b` and a weak product. Separate the relation

    B(s,t) OR (s=a AND t=b)

on `U times V`. Pairs in the first part satisfy forth/back by the already
proved forward implication; the root pair satisfies them by the displayed
hypothesis. The separated relation is therefore a witness for `B(a,b)`.
This is why no well-founded recursion, or collection of a family of
bisimulation witnesses, is needed.

### 4.3 Quotient membership and extensionality

Put

    E*(a,b) := EXISTS c in b B(a,c).

`B`-equivalent objects are interchangeable in either argument of `E*`.
This follows from transitivity of `B` and its forth/back characterization.
Moreover,

    B(a,b) <-> FORALL z(E*(z,a) <-> E*(z,b)).

For the reverse implication, each `u in a` satisfies `E*(u,a)` by reflexivity,
so the assumed equal profiles provide a `B`-equivalent member of `b`, and
vice versa. The characterization then yields `B(a,b)`.

Interpret target equality by `B`, target membership by `E*`, and the target
constant by the same raw object `W`. Equivalently, in a set-coded model,
take the quotient of its domain by `B`. The target Extensionality axiom is
now proved. Induction on formulas gives invariance of every translated
formula under replacement of any parameter by a `B`-equivalent one.

### 4.4 Transfer of the two full schemes

**SS.** Suppose `E*(x,W)`, and choose `x' in W` with `B(x,x')`. Apply raw
`SS` at `x'` to the translated target matrix, obtaining `y in W` with
exactly the members of `x'` satisfying that matrix. Then `E*(y,W)`.
Membership in `y` modulo `B` gives exactly the translated subset of `x`,
by matrix invariance and the congruence of `E*`.

**RED.** Suppose target parameters satisfy `E*(pi,W)`. Choose raw
representatives `pi' in W` with `B(pi,pi')`. If a translated target matrix
has a witness, invariance gives a witness at these representatives.
Because a target `RED` matrix has no `W`, and both `B` and `E*` are defined
without `W`, its translation is a legitimate raw `RED` matrix. Apply raw
`RED`, obtain a witness in raw `W`, and use reflexivity/invariance to return
to the target parameters. This proves target `RED`.

Therefore raw `S`, and hence `S2plus`, interprets extensional `K(W)`.
This is a full ordinary mathematical interpretation in the equality-bearing
source language. It remains to serialize and check these arguments if a
formal artifact is desired.

## 5. Direct derivation of ZF without Foundation or Choice

Friedman's extensional `K(W)` has `EXT`, full `SS`, and full `RED`. Its
calibration can be verified directly here, without relying on the
preliminary predication paper's well-founded-comparison argument. Global
Separation, Pairing, transitivity of `W`, and upward transfer were proved
above and remain available after adding Extensionality.

**Subset closure inside W.** Suppose `x in W` and `a subseteq x`. Apply
`SS` at `x` to the predicate `z in a`. The output `a' in W` has exactly
the members of `a`. Extensionality now implies the literal equality `a=a'`,
so `a in W`.

**Union.** If `x in W`, transitivity of `W` implies that every member of
every member of `x` is in `W`. Global Separation on `W` therefore yields
an exact union of `x`. Upward transfer of this `W`-free existence assertion
gives Union for all raw objects.

**Power Set.** If `x in W`, subset closure shows that every actual subset
of `x` belongs to `W`. Global Separation on `W` yields an exact Power Set
of `x`. Upward transfer gives the axiom globally. This is exactly where
Extensionality is needed for an outright derivation: raw coextensional
representatives cannot be silently identified.

**Infinity.** Nonempty `W` and `SS` with a false predicate yield an empty
object `e in W`. Global Pairing and Union give a successor `s=x union {x}`
for every `x`. For `x in W`, `RED1` at `x` supplies such a successor in
`W`. Consequently the actual object `W` contains an empty object and is
closed under successors, so it witnesses the axiom of Infinity. This does
not assert `W in W`.

**Functional Replacement.** Fix a `W`-free formula `rho(x,y;parameters)`.
Assume first that the domain `A` and all parameters are in `W`, and that
`rho` is functional on `A`. For any `x in A`, transitivity gives `x in W`.
If an output exists, `RED` reflects an output into `W`; functionality
implies that every output equals that reflected output, hence belongs to
`W`. Global Separation on `W` gives the exact image. Apply upward transfer
to the `W`-free implication "functionality on A implies an exact image
exists," universally closing `A` and the parameters. This proves the full
Replacement scheme, including its partial-function version. No Collection
or choice of local witnesses has been assumed.

Empty Set, Extensionality, full Separation, Pairing, Union, Power Set,
Infinity, and functional Replacement are therefore derivable. The reduct
to `{E,=}` is a model of `ZF` without Foundation or Choice. Combined with
Section 4, this gives an explicit interpretation of that theory in the raw
equality-bearing kernel.

## 6. ZFC calibration and effective finite reflection

For precision the comparison theory is the equality-bearing version
K^=(W): full SS and RED plus incoming extensionality implying actual
equality. It is not a literal transcription of Friedman's equality-free
extensionality convention. Section 5 calibrates this version directly.

For the upper direction, given any finite list Delta(W) of its axioms,
construct a ZFC derivation of EXISTS w AND Delta(w). Take the finite list
of RED matrices and their existential closures, and close it under
subformulas. Finite Levy reflection supplies a limit rank V_alpha,
alpha>omega, reflecting this list. Interpret W by V_alpha. RED follows
from witness closure and absoluteness. SS follows from Separation and
rank closure under subsets, even for matrices mentioning W and parameters
outside V_alpha. Extensionality and inhabitation hold.

Uniformity is supplied by the effective proof-schema construction, not by
a global truth predicate. For each existential subformula, define the
least rank of a witness if one exists (zero otherwise). Replacement bounds
these ranks for tuples from a given V_beta. Iterate a common increasing
rank bound for the finitely many formulas through omega, and take the
supremum. Witness closure follows, and syntactic induction gives
absoluteness. Each step uses fixed logical/set-theoretic proof templates
with computably generated Separation and Replacement instances. Recursion
on finite formula trees and list length gives a primitive recursive proof
generator for the finite-fragment existence sentence; the same inductions
verify its syntactic correctness in ZFC. This ordinary proof construction
has not been serialized as a formal artifact.

A K^=(W) refutation uses finite Delta(W). Deduction and fresh-constant
generalization turn it into a refutation of EXISTS w AND Delta(w).
Combine with the generated ZFC proof to obtain a ZFC refutation. Since
K^=(W) proves every S2plus axiom, this also translates an S2plus refutation.

For the lower direction, a set-coded model of S2plus gives the bisimulation
quotient model of K^=(W), hence a model of ZF without Foundation or Choice.
The usual definable well-founded part and constructible inner-model
interpretations give a model of ZFC; external well-foundedness of the
original coded membership relation is not assumed. These standard
interpretations and the effective arguments above are formalizable in ZFC.
Consequently ZFC proves Con(S2plus) iff Con(ZFC).

There is no claim of one rank satisfying all ZFC, of a transitive set model
of ZFC, or of an inaccessible cardinal. Nor do we assume that an arbitrary
coded model has a uniform internal reflection theorem for all formula
codes. Effective finite-fragment proof generation is the justification for
the uniform consistency implication. The PA proof-translation route in
Section 3 concerns the two schema presentations; no machine-specific PA
endpoint for the entire calibration is asserted here.

Primary reference for these standard bridges and finite reflection:
Stefan Geschke, Models of Set Theory, Sections 3--5,
https://www.math.uni-hamburg.de/home/geschke/teaching/ModelsSetTheory.pdf .

## 7. Exact syntax measurements and their limits

`kernel_counts.py` expands

    NOT A := A -> Bottom
    EXISTS x A := NOT FORALL x NOT A
    A AND B := NOT(A -> NOT B)
    A IFF B := (A -> B) AND (B -> A).

An atomic `Member` or `Equal` is one formula node; each `Imp`, `All`,
`Bottom`, and opaque matrix hole is one node. Postfix-token counts add two
term-label tokens per atom and one binder-label token per `All`. Repeated
subtrees are counted repeatedly: these are tree sizes, not shared DAG sizes.

| Open template | Formula nodes | Matrix holes | Postfix tokens |
|---|---:|---:|---:|
| Inhabited separation `Splus` | 33 | 2 | 47 |
| Curried `RED2` | 18 | 2 | 25 |
| Joined raw kernel | 56 | 4 | 77 |
| Joined kernel with `EXT` | 75 | 4 | 107 |
| Raw kernel plus original two vacuity rows | 74 | 4 | 105 |
| Extensional control plus those vacuity rows | 93 | 4 | 135 |
| Original 254-lineage `C/G/V` bundle | 101 | 3 | 145 |

The original comparison is a hand-normalized transcription of the exact
`C/G/V` formulas in the upstream design/`Codes254.v`; it abstracts the
relative falsity alias to `Bottom` ONLY to compare syntax. It omits the
original arithmetic gate and the rest of the logical engine. The new
kernel similarly omits all implementation overhead. The raw interpretation
still uses actual logical equality, so all necessary equality machinery
must remain in any direct adaptation of the old backend.

In particular, this is NOT a claim of a 105-state or 135-state machine,
or of any reduction below 254/253. A constant, extra matrix occurrence,
changed atom/quantifier frequencies, a matrix generator, proof enumeration,
and binary compilation can outweigh the source-size saving.

## 8. Compiler obligations that cannot be omitted

1. **W is one shared constant.** Turning it into a free variable while
   retaining unrestricted theorem generalization is unsound. A constant
   constructor, a correctly reserved parameter discipline, or the separate
   finite-conjunction constant-elimination theorem is necessary.
2. **All finite subsets must share W.** Existentially closing each axiom
   separately is not a substitute. A constant-free implementation can instead
   enumerate existential closures of cumulative finite conjunctions; the
   full finite-proof transport has to be supplied.
3. **The matrix restriction is real.** Every emitted matrix must have no
   literal W and no other free variable besides its three slots. A grammar
   can enforce this; a syntax checker can test it; a total normalization
   can establish it. None is free. Bound-variable names and nesting remain
   unbounded.
4. **Keep complete logical instantiation.** Repeated coordinates and
   instantiation at already existing variables are essential. Boolean or
   finite-sort validity of retained quantifier rows does not suffice.
5. **The target must be an actual contradiction.** The primitive Bottom
   convention in these notes is intentional. Importing `F=Rel(0,0)` needs
   a separate falsity/irreflexivity normalization proof, including binders
   that capture variable 0.
6. **Count the whole blank-tape machine.** Data printers, initialization,
   decoder, complete proof checker, interpreter, and binary alphabet
   conversion all contribute to the final state total.

## 9. Primary sources and the preliminary-sketch gap

* Harvey M. Friedman, *Axiomatization of set theory by extensionality,
  separation, and reducibility: seminar notes*, 5 October 1997:
  https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/TalkAxiomSetThy-ts05xn.pdf
* Harvey M. Friedman, *From Russell's paradox to higher set theory*,
  10 October 1997, especially the K(W) statement on pp. 9-10:
  https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/FromRusselltoSetThy-1rnmfbg.pdf
* Harvey M. Friedman, *The interpretation of set theory in mathematical
  predication theory*, preliminary report, 25 October 1997:
  https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/IntSetMPT97-2hjdxqo.pdf
* Published machine formulas and logical interfaces:
  https://github.com/jeff87654/busy-beaver/tree/main/ZF/m254
  and the pinned comparison source
  https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/Codes254.v

The preliminary predication paper defines its relation `E(b,c)` using
well-founded transitive sets containing `b,c`, then claims reflexivity for
all raw objects. An object with self-membership cannot lie in a well-founded
transitive set, so that global assertion needs additional domain work or a
different definition. Lemma 13's converse has the same domain issue. The
argument of Section 4 supplies a different, unrestricted set-coded
bisimulation definition and an explicit greatest-relation construction
inside a weak product. It does not cite the defective reflexivity step.

Novelty is not asserted against the entire interpretability literature.
The contribution for this project is an explicit small-stencil candidate,
a noncircular finite-parameter proof, an inhabited separation transformation,
and a complete ordinary mathematical repair of the raw equality-bearing
calibration. A compiled state result remains to be obtained.

## 10. Finite supporting checks

`check_pair_endpoints.py` independently enumerates every binary membership
structure on one through four objects, with no set axioms. All 66,066
structures pass endpoint uniqueness. The structures include duplicate
incoming profiles and self-membership; 41,463 exact ordered-pair witness
triples are checked. Up to four different code objects can represent the
same endpoints in these examples. This confirms that the regression does
not accidentally assume unique set representatives. The finite check is
not a replacement for Step B's general proof.
