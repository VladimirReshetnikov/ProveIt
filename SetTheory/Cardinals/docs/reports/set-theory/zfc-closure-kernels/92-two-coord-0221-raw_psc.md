# Raw PSC: hereditary-saturation interpretation and formalization

Research audit, 16 October 2026. The candidate here has classical logical
equality and all subset-only positive seeded closure instances from
`subset_only.md`, but omits Extensionality. Either the point or subset seed
works in the arguments below; only seed reflexivity is used. No proposed
theory needs an intended set-theoretic meaning for this project. The tests
are consistency strength and the cost of a complete compiled search.

The initial audit below established useful consequences and proposed an
interpretation. Subsequently, batch 144 source 08 supplied an independently
reviewed mathematical calibration of **equality-free PSC alone**, with no
Extensionality, profile congruence or irreflexivity. This also calibrates the
equality-bearing raw variant by the stated consistency sandwich. The new
Lean results check part of that interpretation under explicit semantic
resources; they do not yet certify its full first-order theory translation.

## Reconciliation after source 08, 16 October 2026

The [source 08 intake](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-08.md)
records the accepted ordinary mathematical argument and its provenance.
An equality-free bootstrap uses full incoming-and-outgoing profile equivalence
for twin singletons and the decoder. Incoming-profile saturation then gives
the hereditary domain `H` below. The key simplification is a **purity cut**:
given a raw transitive cover `V` of `a`, separate
`U={u∈V:H(u)}`. Heredity makes `U` transitive. If `a` is saturated and
all its members satisfy `H`, this one `U` witnesses `H(a)`. It replaces the
least-transitive-cover and coextensional-Replacement construction in the
earlier proposal retained below.

For each translated matrix, guard its input and output by `H`, apply raw
PSC, and saturate the resulting hull under incoming-profile equality.
Matrix invariance preserves initial closure, recurrent closure and global
support. The purity cut makes that saturated hull an `H` object. Thus the
report interprets Extensionality plus subset-seeded PSC in equality-free
raw PSC, and composes this with the extensional calibration and ordinary
Foundation/Choice consistency bridges. This is an ordinary mathematical
ZFC-provable consistency argument, not a serialized proof-code artifact or
the experimental machine's calibration.

[PSCSaturation.lean](../../Lean/BusyBeaver/ZFC/PSCSaturation.lean) now checks
incoming-profile invariance, heredity and nonemptiness, the purity-cut lemma,
exact saturation from one constant-image closure instance, restricted
membership congruence/Extensionality/subset absoluteness, and guarded-hull
transfer including support. Its resources name the required cover, cut,
saturation and guarded relation instances. Deriving those resources from
the actual equality-free Form-indexed schema, translating arbitrary formulas
and connecting the whole interpretation to the ZFC proof predicate remain
formalization work. The report's reference checker and 269-state compiler
control are separate artifacts; neither implements a calibrated sub-254
machine for this new theory.

## The forward bootstrap does not need Extensionality

The exact constant-fiber argument, empty sets, exact singletons, Power Set,
the gated singleton decoder, transitive covers, full Separation, Union and
two-cycle Pairing use no Extensionality. The Russell-root argument also
gives ordinary partial functional Replacement without Extensionality.

Infinity needs no Extensionality either. A successor of `x` has precisely
the members `z∈x ∨ z=x`. Although there may be multiple successor objects,
they have the same literal members. Therefore every successor is a subset
of any one chosen successor, which supplies the local subset bound. The
successor closure instance at an empty `e`, followed by adjoining `e`,
produces an inductive set. This weakening is checked in `Bootstrap.lean`:
`successor_subset_bounded`, `inductive_of_successor_instance` and
`infinity_of_instance` have no Extensionality hypothesis. The optional
`successor_unique` lemma retains that hypothesis and is not used by them.

These consequences alone do not settle consistency strength. In particular,
ordinary functional Replacement becomes substantially less useful when
set representations are not unique.

## Exact images of locally subset-bounded fibers

A stronger consequence is available. For every formula `ρ(x,y;p̄)` and set
`A`, raw PSC proves

\[
 [\forall x\in A\,\exists b\,\forall y
       (\rho(x,y;\bar p)\to y\subseteq b)]
 \quad\longrightarrow\quad
 \exists B\,\forall y\,[y\in B\leftrightarrow
                    \exists x\in A\,\rho(x,y;\bar p)].
\]

To prove this, use Separation to form `r={t∈A:t∉t}`; Russell's argument gives
`r∉A`. Let `U=⋃A`, and apply PSC at `r` to

\[
 R(x,y)\equiv(x=r\land y\in A)\lor(x\in A\land\rho(x,y;\bar p)).
\]

Its root fiber is subset-bounded by `U`. At an input in `A`, the root
branch is false, and the assumed local bound applies. Elsewhere its fiber
is empty. The positive hull contains `A` and every desired output.
Separation in that hull gives the displayed exact image. No bounds are
chosen simultaneously, and no functionality assumption is needed.

Consequently the same exact image exists whenever every nonempty fiber of
`ρ` is unique up to **coextensionality**

\[
 D(y,z)\equiv\forall t\,(t\in y\leftrightarrow t\in z).
\]

Any one output bounds the other outputs by subset inclusion. This is
stronger than the actual-equality functional Replacement currently stated
in `Bootstrap.lean`; the stronger consequence in this section is an
ordinary mathematical argument, not an additional checked Lean theorem.

It also yields exact images for the relation
`ρ(x,y) ≡ ∀z(z∈y ↔ φ(x,z))`, since any two such outputs are coextensional.
There need not be an output at every input. This is a concrete interface
for an extensional interpretation, rather than an assumption that an
arbitrary bisimulation-functional relation is literally single-valued.

## Power-bounding transitive containers

Raw PSC proves the container principle

\[
 \forall a\exists V\,[a\in V\land
   \forall x\in V\,(x\subseteq V\land
     \exists p\in V\,\forall z(z\subseteq x\to z\in p))].
\]

Let `PowerExact(x,p)` mean `∀z(z∈p ↔ z⊆x)` and use the single closure
relation

\[
 R(x,y)\equiv\operatorname{Switch}(x,y)\lor\operatorname{PowerExact}(x,y).
\]

Each Switch fiber has its earlier local subset bound. Every exact power
object at `x` has the same members as any one chosen exact power object,
so that object bounds all power outputs by subset inclusion. Pairing and
Union combine these two local bounds. Thus `R` is locally subset-bounded.

Its positive hull at `a` is Switch-closed, hence transitive. An exact power
object `p` at the initial input `a` enters the hull. Since `a⊆a`, we have
`a∈p`, and transitivity gives `a∈V`. Every `x∈V` likewise outputs an exact
power object into `V`. Neither a separate subset-output arm nor a self
output arm is necessary. This is also a mathematical consequence pending
a dedicated Lean adapter.

## The initial interpretation gap

The following records the earlier gap and research leads. Source 08 now
supplies a different mathematical solution through the purity cut above;
the full first-order Lean interpretation remains unfinished.

Coextensionality does not automatically respect membership in its first
argument: `D(x,y)` alone need not give `x∈z ↔ y∈z`. A bisimulation quotient
also changes uniqueness from actual equality to quotient equality.
Ordinary functional Replacement therefore cannot simply be transported to
that quotient. The exact-image principle above is stronger, but its
adequacy for the desired interpretation must still be proved.

[Al-Johar's 2020 preprint](https://arxiv.org/html/2010.01938v1), Sections 2–3,
studies replacement by all exact extensions and coextensional-functional
replacement, and sketches an interpretation and removal of Regularity.
The formulas there match the stronger interface derived above. That
preprint is a research lead; its complete interpretation has not been
independently reproduced or formalized here.

[Hinnion's extensional quotient paper](https://randall-holmes.github.io/Bibliography/Hinnion%20%281981%29%20Extensional%20Quotients%20of%20Structures.pdf),
especially Chapters 3, 4 and 6, supplies primary-source machinery for
contractions and preservation, including the role of transitive
containment. It does not by itself identify raw PSC with its hypotheses.

An optional irreflexivity sentence remains an independent addition to
raw PSC. It may be useful to calibrate an off-diagonal theoremhood target;
it is neither Foundation nor an automatic property of a bisimulation
quotient. No claim here removes a fixed control sentence from the final
calibrated machine theory or establishes a new state bound.

## Earlier proposed direct interpretation using saturated sets

The following is a new proof plan for independent checking, rather than a
verified invocation of Scott's theorem. It avoids the abstraction-choice
operator assumed by Hinnion's `ZFX` interpretation in Chapter 6, pages
200–202. That operator and Replacement for its extended language have not
been derived from PSC.

Put `S(x) := ∀u v(D(u,v) → (u∈x ↔ v∈x))`, and define

\[
 H(x):=S(x)\land\exists T\,[x\subseteq T\land
                   \operatorname{Trans}(T)\land\forall z\in T\,S(z)].
\]

Both predicates are invariant under `D`. The class `H` is hereditary: if
`H(x)` and `y∈x`, the same transitive witness for `x` witnesses `H(y)`.
Every empty object belongs to `H`.

The key proposed closure lemma is: **if `S(B)` and every member of `B`
belongs to `H`, then `H(B)`.** Define a least transitive cover by

\[
 y\in\operatorname{TC}(x)\quad\leftrightarrow\quad
  \forall T\,[(\operatorname{Trans}(T)\land x\subseteq T)\to y\in T].
\]

An earlier transitive cover bounds this predicate, so full Separation
gives an exact extension. It is transitive, covers `x` by subset, and is
contained in every transitive cover of `x`. All its possible extensions
are coextensional. Coextensional-functional Replacement therefore collects
all these extensions for `x∈B`. Let `U` be their union. Each such `x` is a
subset of `U`, and `U` is transitive. If `H(x)`, leastness puts every member
of every `TC(x)` copy in an `S`-only transitive cover. Thus every member of
`U` satisfies `S`. The set `T=B∪U` is transitive, covers `B` and has only
`S` members, proving the lemma without choosing a family of covers.

Interpret equality by `D`, preserve raw membership, and restrict
quantifiers to `H`. Membership is congruent under `D` on this domain,
because every target is `S`. Formula induction gives invariance of every
translated formula. The proposed axiom derivations are:

- Extensionality: all raw members of `H` objects belong to `H`, so agreement
  on members in the interpreted domain is their full raw profile.
- Pairing: saturate a raw pair under `D`. Union: take raw Union. Each result
  is `S` with only `H` members, so the closure lemma applies.
- Power Set: separate `{y:y⊆a ∧ H(y)}` from a raw power object. For `H(y)`,
  inclusion restricted to `H` is ordinary raw inclusion. This predicate is
  `D`-invariant and has only `H` outputs.
- Separation: a translated predicate is invariant under `D`, so Separation
  in an `S` source again gives an `S` object with only `H` members.
- Replacement: collect all `H` outputs of the translated matrix on the
  source. Interpreted uniqueness is precisely `D`-functionality. The image
  is `S` by formula invariance and has only `H` members.

For Infinity use the definable relation

\[
 R(x,y):=H(x)\land
       \forall z\,[z\in y\leftrightarrow(z\in x\lor D(z,x))].
\]

At an `H` input, a successor exists by adjoining the set of all `D` copies
of that input. Its members are all `H`, and it is `S`, so the closure lemma
puts it in `H`. Every fiber of `R` is empty or coextensional, hence locally
subset-bounded. Apply PSC at an empty `e`, obtaining `C`. Its support
clause implies every member of `C` is `H`, even when its supporting input
was not active in the closure clause. Saturate `C∪{e}` under `D` to get
`I`. Then `I` is `S` with only `H` members, hence `H(I)`. Closure at members
of `C`, and initially at `e`, makes `I` successor-closed: `D`-related inputs
have identical displayed successor profiles. This gives interpreted
ordinary Infinity.

Every auxiliary predicate here is a fixed first-order formula. Matrix
translation replaces equality by `D`, relativizes quantifiers to `H`,
renames fresh variables and inserts the matrix into finitely many fixed
PSC/Separation patterns. This identifies a computable syntactic shape.
The complete proof patterns and their implementation were the missing
interfaces of this initial proposal. Source 08 supplies the revised
mathematical proof through the purity cut; the corresponding full Lean
syntax and proof-transport result remains to be checked. The separate
equality-free CP/GIC experiment is analyzed in
`equality_free_bisimulation.md`; it cannot use this PSC exact-image lemma
without another proof.

## Batch 150: two slots and native rules

The reviewed source 21 in the closure-kernel host now gives an ordinary
ZFC-level consistency calibration for **EPSC2**, restricting free matrix
variables to x,y,p,q while allowing arbitrary internal quantifiers. The proof
obtains covers, Union and binary bounds with this budget, then hereditary
Pairing before encoding parameter tuples. Only hereditary interpretations
are packed; incoming-profile equivalence need not preserve arbitrary raw
predicates. Restoring a seed uses the second slot, and the support filter
then uses the hull and packed tuple. This is a useful concrete interface
reduction, not a finite first-order axiom set or a smaller measured machine.
One-slot and parameter-free versions remain open.

Source 22 proves an alternative presentation theorem: EPSC is equivalent to
its global boundedness-to-hull rule, even with purely logical premises. The
proof guards the matrix by its **open** boundedness statement and completes
the premise before applying the rule. Universally closing that guard first
fails in the delivered three-object counterexample. A unary protected-witness
rule uses `forall b beta` as the matrix and recovers the basic rule through
an unused witness slot. Its complete numeric de Bruijn reference has two
76-line positive closure certificates, but no compiled binary table.

These results complement the prior raw PSC and hereditary-saturation
resources; neither is currently a Lean theorem for the full new theory.
The complete proofs, attribution, diagnostic counterexamples and replay
limits are recorded in
[the batch 150 reconciliation](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch-150-bounded-parameters-native-closure-and-quantified-nand)
and `intake-150-source-21.md` / `intake-150-source-22.md` beside it.

## Batch 151: outgoing equality and exact hulls

[Sources 24 and 25](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch-151-outgoing-equality-finite-carriers-and-exact-fixed-point-hulls)
add two reusable ordinary proofs. Exact full-profile singletons make
`forall z, (x in z -> y in z)` equivalent to full observational equality.
The singleton construction comes first, so this does not assume raw
incoming-profile congruence or Extensionality. Reserving variable zero at an
empty object then permits a membership-only translation of equality and
Bottom, provided every other binder and substitution respects that convention.
The raw observational quotient remains distinct from the hereditary incoming
quotient used for extensional set theory.

EFPC asks for a represented fixed point of the empty-seeded image operator.
Its equivalence with full EPSC uses raw Separation to represent an intersection
of prefixed subobjects and a second image cut. A three-object counterexample
shows that replacing one universally closed EPSC instance in isolation fails.
The delivered constructive Lean theorem assumes those two explicit resources;
global leastness requires an additional intersection resource. Connecting them
to `RawPSCModel.separation_of_model` needs actual fresh formula builders and
an EPSC/PSC adapter. The exact-hull control costs 271 states versus its 270-state
EPSC comparison; the new normal form supplies no measured saving.


## Batch 152 theory continuations

The closure-kernels host's sources 26, 29, 30, 33 and 34 (arrival `da6dabcd89`,
placement `b123527ff4`) add ordinary theory results that bear on this route.
Source 26 proves EPSC1 plus fixed adjunction deductively equivalent to full
EPSC, and exact represented hulls at positive parameter arity. EPSC1 alone
remains open. Source 29 uses ground epsilon terms to name parameters in its
term model; this does not prove ordinary parameter-free EPSC sufficient.
Source 30's regular-ordinal model refutes deleting output support, even with
the listed container axioms; it is not a countermodel to supported PSC.

Source 33's inhabited subworld schema SR₂⁺ uses a shared world constant and
native equality. Its arbitrary-transitive-cover bisimulation argument avoids
assuming all raw objects are well founded. Source 34's finite assignment/class
FAK12 uses an expanded language and an external definable-class enumeration.
Neither is a finite membership-language axiomatization of ZFC. The full
dossiers are in `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`.
These are ordinary calibrations, separate from current actual CP/GIC quotient
ZF0, its one-way enumerator consistency implication and the remaining effective
Foundation/Choice reductions. Their literal proof compilers and full internal
machine endpoint remain open.

## Batch153: the one-parameter Pairing obstruction

Source36 in the closure-kernels host gives a three-component class
interpretation of Extensionality, IR and full EPSC1, with full Separation,
Union, Power Set, Infinity, parameter-free Replacement and the explicitly
stated local graph Choice axiom, but without cross-component Pairing.
The old hereditary-saturation domain is the whole interpretation and its
profile quotient is actual equality, so that particular interpretation
still lacks Pairing. A specified EPSC2 instance and a one-parameter
Replacement instance also fail. This is an ordinary relative deductive
separation under Con(ZFC), not a consistency-strength separation or a Lean
theorem. The EPSC1 consistency question remains open to other interpretations;
source26's EPSC1 plus adjunction/observational Pairing comparison is unchanged.
Full proof, finite truncations that explicitly fail EPSC1, and review are in
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-153-source-36.md`.
# Batch155 finite and unary refinements

Sources42/44 in `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`
package full equality-free EPSC into finite assignment/class kernels with nine
proper functions, retaining native or explicit equality for the auxiliary
language. Their ordinary consistency arguments and ideal ground-search proofs
are not yet Lean interpretations or small binary implementations. Source46
proves raw deductive EPSC1+exact BinaryUnion ↔ EPSC1+profile adjunction ↔ full
EPSC by one-parameter singletons, raw Union and observational tuple coding.
Its fixed-dimensional support obstruction leaves invariant interpretations and
the consistency strength of bare EPSC1 open. These refine the earlier theory
interfaces without completing the full formal interpretation discussed above.
