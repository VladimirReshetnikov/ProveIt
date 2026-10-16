# Proposed equality-free CP/GIC bisimulation interpretation

Research audit, 16 October 2026. This note gives a mathematical proof route
from **full equality-free CP + GIC** to the usual first-order set theory
with Foundation and Choice omitted. Irreflexivity may be added to the
source theory, but none of the set-theoretic constructions below uses it.
The route is proposed for independent checking. Only the explicitly named
Lean components are currently formal results. It is not a consistency
calibration of the current experimental compiler or its 252-state output.

The reference construction is Mira-Cult's actual-equality source theory in
the attributed pinned snapshot, particularly
`lib/jeff-busy-beaver-zfc254/ZF/m254/coq/settheory/S_raw.v`, `S_quot.v` and
`S_ax.v`. Those files use equality axioms. Replacing their equality atoms
by predecessor profiles without changing the proofs is unsound. The repairs
below concern those equality-dependent uses; the attribution does not imply
that the equality-free adaptation is an upstream result.

No intended meaning of the source theory is required. The purpose is a
small consistency-equivalent input for a completely accounted compiler.

## Source theory and two distinct equivalence relations

Work in classical equality-free first-order membership logic with a
nonempty domain. All displayed matrices may have arbitrary finite tuples
of parameters; all auxiliary binders are fresh, and parameters are
universally closed. Abbreviate `Sub(x,b) := ∀z(z∈x → z∈b)` and let
`Trans(V)` mean `∀x∈V Sub(x,V)`.

CP is

\[
 \forall a\exists V\,[a\in V\land\operatorname{Trans}(V)\land
   \forall x\in V\exists W\in V\forall z
                        (\operatorname{Sub}(z,x)\to z\in W)].
\]

For every equality-free matrix `θ(x,y;p̄)`, GIC is

\[
 \forall A\exists B\,[
   \forall x\in A(\exists y\,\theta(x,y)\to
                         \exists y\in B\,\theta(x,y))
   \land\forall y\in B\exists x\,\theta(x,y)].
\]

The supporting input in the final clause is unrestricted. The matrices
below include a domain guard when support must certify an input's
membership in that domain. There is no axiom saying all semantic
relations satisfy GIC.

Raw coextensionality is

\[
 D(x,y):=\forall z(z\in x\leftrightarrow z\in y).
\]

Pure logic proves that `D` is an equivalence relation. It respects
membership in the **second** argument. It need not respect membership in
the first argument. In particular, `D(x,y)` and `x∈V` do not imply `y∈V`.
The later bisimulation equivalence `E` is a different, generally coarser
relation. Interpreted membership will use `E`, not raw membership or `D`.

## Profile pairs and ordered-pair codes

Put

\[
 \begin{aligned}
 J(x,s)&:=\exists z\in s\,D(x,z),\\
 \operatorname{SingD}(s,a)&:=\forall z(J(z,s)\leftrightarrow D(z,a)),\\
 \operatorname{PairD}(p,a,b)&:=\forall z(J(z,p)\leftrightarrow
                                  (D(z,a)\lor D(z,b))),\\
 K(a,b,c)&:=\exists s,p\,[\operatorname{SingD}(s,a)\land
                  \operatorname{PairD}(p,a,b)\land
                  \operatorname{PairD}(c,s,p)].
 \end{aligned}
\]

These are exactly the predicates `ClassMember`, `Singleton`, `Pair` and
`OrderedPair` in `Lean/BusyBeaver/ZFC/ProfilePairs.lean`.
`orderedPair_injective` proves, without profile congruence or existence
assumptions, that `K(a,b,c)` and `K(a',b',c)` imply `D(a,a') ∧ D(b,b')`.
`orderedPair_endpoint_congr` proves endpoint invariance under `D`.
Changing the code within `D` also preserves `K`, because `J` is invariant
in its second argument. The latter observation follows from the checked
`classMember_right_congr` and `pair_object_congr` lemmas.

Existence follows from the following GIC proof, checked semantically in
`ProfileCollection.lean` under its explicitly named relation instances.
GIC with a false matrix yields an empty object `e`. CP at `e` provides
`e,W∈V`, where `W` contains every subset of `e`. In particular `e∈W`,
so `¬D(e,W)`. Apply GIC over `V` to

\[
 (D(t,e)\land D(y,a))\lor(D(t,W)\land D(y,b)).
\]

Coverage at `e` gives a member of the output in the profile of `a`;
coverage at `W` gives one in the profile of `b`. Their input profiles are
distinct, so the branches cannot interfere. Support puts every output
member in one of those two profiles. Transitivity of `D` proves PairD.
The case `a=b` gives SingD, and three such constructions give `K`.
Neither this argument nor endpoint uniqueness uses IR.

## Approximate collection tools

For a raw relation code set define

\[
 \operatorname{App}(R,a,b):=\exists c\in R\,K(a,b,c).
\]

It is invariant under `D` in either endpoint and under `D` on `R`.
Replacing an individual code by a `D` copy also preserves the represented
edge. Thus literal raw singleton, union and separation are unnecessary for
collecting edge sets.

An **approximate union** of `A` is an object `U` satisfying

\[
 J(z,U)\leftrightarrow\exists x\in A\,J(z,x).
\]

Take a CP transitive container `V` of `A`. Every `z∈x∈A` belongs to `V`.
Apply GIC over `V` to
`θ(z,v) := (∃x∈A z∈x) ∧ D(z,v)`. Coverage retains every original member
profile; support excludes other profiles. This proves the displayed
equivalence. In particular, an approximate union of a family of relation
code sets represents precisely the union of their edges.

PairD followed by approximate union similarly joins two edge sets. A
SingD object at a code `k` represents exactly the edge profiles represented
by `k`. This permits adjoining a root edge to a union of bisimulations.

For a `D`-invariant predicate `P(c)` on code objects, a bounded filter can
be formed up to `D`. Apply GIC over a bound `B` to
`θ(d,c) := d∈B ∧ D(d,c) ∧ P(c)`. Every output satisfies `P`; every `d∈B`
satisfying `P` has a `D` copy in the output. This replaces the imported
literal raw Separation of code sets.

The necessary bound is larger than the imported actual-equality bound.
If `R`'s codes belong to a transitive `V`, every endpoint decoded from a
code of `R` is a subset of `V`. Indeed some actual representative of its
profile lies on a finite membership chain from that code inside `V`.
The endpoint itself need not belong to `V`.

For endpoints `a,b⊆V`, take a fresh CP container of `V` and successive
power bounds `B0,B1,B2` for `V,B0,B1`. Every member of an inner singleton
or pair code is `D`-related to `a` or `b`, hence is a subset of `V` and
belongs to `B0`. Every actual inner code, including a `D` copy of it, is
therefore a subset of `B0` and belongs to `B1`. Every outer code is a
subset of `B1` and belongs to `B2`. Thus `B2` contains **all** the required
ordered-pair codes. This handles endpoint copies outside `V`.

To bound two relation code sets together, form PairD at `R1,R2` and put
it in a CP container `V`. There are actual representatives `R1',R2'∈V`
with `D(Ri,Ri')`. Hence every actual member code of either original `Ri`
belongs to `V`, which is the premise needed above. Membership of `Ri`
itself in `V` is unnecessary.

## Bisimulation equivalence

Define `Bisim(R)` to assert that every edge `App(R,p,q)` satisfies

\[
 \begin{aligned}
 &\forall a\in p\,\exists b\in q\,\operatorname{App}(R,a,b),\\
 &\forall b\in q\,\exists a\in p\,\operatorname{App}(R,a,b).
 \end{aligned}
\]

Put

\[
 E(x,y):=\exists R(\operatorname{Bisim}(R)\land\operatorname{App}(R,x,y)),
 \qquad
 M(x,y):=\exists u\in y\,E(x,u).
\]

These are fixed equality-free formulas. The corresponding semantic
`App`, `Bisim` and `Eqv` definitions are in `ProfileCollection.lean`.

For reflexivity at `x`, choose a CP transitive container `V` containing
`x` and apply GIC over `V` to
`θ(t,c) := t∈V ∧ K(t,t,c)`. Every member code of the resulting `R` is a
diagonal code at some `t∈V`; coverage supplies an edge `(t,t)` at every
such `t`. Endpoint uniqueness implies that any edge `(p,q)` has both
endpoints `D`-related to that `t`. They therefore have identical raw
members. Each such member lies in `V` and has its diagonal edge in `R`,
which proves both bisimulation clauses. Endpoint invariance also proves
`D(x,y) → E(x,y)` using this same diagonal construction.

For symmetry, apply GIC over `R` to

\[
 d\in R\land\exists p,q\,[K(p,q,d)\land K(q,p,c)].
\]

Coverage supplies every reverse edge. Support and endpoint uniqueness
show that every new edge is the reverse of an old edge up to `D` on its
endpoints. Those endpoints have identical raw members to the old ones,
so the old back clause becomes the new forth clause, and conversely.

For composition, use the common container and all-code bound above.
Filter codes up to `D` by

\[
 \exists s,t,u\,[\operatorname{App}(R1,s,t)\land
       \operatorname{App}(R2,t,u)\land K(s,u,c)].
\]

All desired codes lie in the bound. The filtered relation contains every
composite edge; every edge it contains has endpoints `D`-related to those
of a composable pair. Successive applications of the two forth clauses,
and of the two back clauses, prove Bisim. Consequently `E` is transitive.
This construction uses only finitely many fixed GIC patterns. The diagonal
and reversal arguments are checked under explicit semantic collection
instances in `bisim_refl_of_collection`, `reverse_of_collection` and
`eqv_symm_of_instances`; composition remains a mathematical obligation.

Equivalence of `E` and the root forth/back clauses imply that `M` respects
`E` in both arguments. For quotient extensionality, suppose `x,y` have the
same `M` members. Every raw child `a∈x` has a matching child `b∈y` with
`E(a,b)`, and conversely. Apply GIC over `x` to collect a bisimulation
matching each child to some child of `y`; apply it over `y` for the
reverse matches. Support ensures that every collected relation is a
bisimulation, even if its supporting input was outside the collection
domain. Approximately union the two families and adjoin a code of
`(x,y)`. Existing edges retain their witnesses; the new root edge has the
two collected matching families as its witnesses. Endpoint uniqueness
handles `D` copies of that edge. This proves `E(x,y)`.

Thus equality interpreted by `E` and membership interpreted by `M`
satisfy equality congruence and Extensionality. Formula induction gives
invariance of every translated formula under changing assignments by `E`.
No congruence property of arbitrary **raw** formulas under `D` is used.

## Interpreted set-existence axioms

All quantifiers of the interpretation range over the whole nonempty raw
domain; equality atoms become `E` and membership atoms become `M`.

**Empty Set and Pairing.** A raw empty object has no `M` members. A PairD
object at `a,b` has precisely the `E` classes of `a,b` as `M` members,
because `D` implies `E` and `E` is transitive.

**Union.** An approximate union `U` of raw `A` has
`M(z,U) ↔ ∃x(M(x,A) ∧ M(z,x))`. The forward implication uses its raw
supporting child and member. For the reverse implication, replace the
interpreted child by a raw member of `A` using congruence of `M`, then
use approximate-union coverage and `D→E`.

**Separation.** For an `E`-invariant predicate `P(u)` obtained by formula
translation, apply GIC over `A` to
`θ(u,v) := u∈A ∧ D(u,v) ∧ P(u)`. Support and coverage give

\[
 M(z,B)\leftrightarrow M(z,A)\land P(z).
\]

Every raw member of `B` is `D`-related to a raw member of `A`; it need
not literally belong to `A`. This is the exact interpreted Separation
statement, with arbitrary translated matrices and parameters.

**Power Set.** Write
`SubD(r,A) := ∀z∈r J(z,A)`. Choose a CP transitive container `V` of `A`.
For `u∈A`, every `D` copy of `u` is a subset of `V`. In a fresh CP
container of `V`, a power bound `B` for `V` therefore contains all those
copies. Every `SubD(r,A)` object is a subset of `B`; a power bound `Q`
for `B` contains every such `r`. Filter `Q` up to `D` by `SubD(r,A)`,
giving `P`.

Every interpreted member of `P` is an `M` subset of `A`. Conversely, for
an arbitrary interpreted subset `X` of `A`, the preceding Separation
construction with predicate `M(u,X)` produces `r` with `SubD(r,A)` and
the same `M` members as `X`. Quotient extensionality gives `E(X,r)`.
Coverage of the bounded filter supplies a `D` copy of `r` in `P`, hence
`M(X,P)`. This proves the full interpreted Power Set axiom without a
literal raw trace `r⊆A`.

**Replacement.** For a translated relation `φ*(u,v)`, use GIC over `A`
with `θ(u,v) := u∈A ∧ φ*(u,v)`. Assume it is functional modulo `E` on
the interpreted source. Support gives only intended output classes.
For an intended output at an interpreted input, choose its raw input
representative in `A`, transport the formula by invariance, and apply
coverage. Functionality modulo `E` identifies the chosen output with
the intended output. Thus the resulting object's `M` members form the
exact interpreted image. The same argument gives partial functional
images; no literal single-valuedness is assumed.

**Infinity.** CP at any root `x` gives an interpreted container of `x`
closed under interpreted singletons. If `M(u,V)`, choose `u'∈V` with
`E(u,u')` and a SingD object `s` at `u'`. Every raw member of `s` is a
subset of `u'`, hence belongs to a CP power bound `W1∈V` for `u'`.
Then `s⊆W1`, so a second power bound `W2∈V` contains `s`; transitivity
puts `s∈V`. Its interpreted members are exactly the `E` class of `u`.

This proves the singleton-closed `INF_lib` formulation used in the
imported `S_ax.v`. The existing ordinary set-theoretic argument
`Std_setinf.inf_or_to_zf` turns this into standard Infinity in the
presence of the other interpreted ZF axioms. That bridge is an explicit
remaining Lean obligation; merely writing an inductive-set conclusion
without this step would omit work.

## Scope and remaining verification

The proposed interpretation uses fixed finite equality-free formulas
`D,J,K,App,Bisim,E,M`. It commutes with propositional connectives and
quantifiers, replacing only the atoms. Every axiom proof above uses a
finite list of fixed GIC patterns, with additional patterns containing
the translated source matrix for Separation and Replacement. Fresh
renaming makes the construction a candidate computable proof
translation. No serialized translation or correctness theorem for that
translation is supplied by this note.

The established Lean results are profile-pair endpoint uniqueness and
congruence, empty/pair/code existence under the named GIC hypotheses,
diagonal bisimulation reflexivity and reversal symmetry. `ProfileSyntax.lean`
also checks actual first-order profile/pair predicates and the GIC wrapper.
The adapters for all required matrix families, composition, quotient Extensionality, the
remaining interpreted axiom proofs, the Infinity bridge and proof
translation must be checked separately. The usual further interpretations handling
Foundation and Choice are also not formalized here. IR is not preserved
automatically by bisimulation: a raw cycle can become a self-member in
the quotient. This causes no contradiction with the stated target,
which omits Foundation and IR.

In the reverse consistency direction, standard ZFC proves the full CP
and GIC schemas and IR. An effective forward interpretation, the
Foundation/Choice bridge and a verified emitted proof calculus would
complete a calibration argument. Until those are actually connected,
the recorded 252-state result is a literal compiler experiment with an
uncalibrated theory. No smaller machine with the required ZFC endpoint
has been proved.
