# Actual source tagged Collection: proposed next checkpoint

27 October 2026. Read-only mathematical/interface and cache plan. No new Lean
source, object, overlay or compiler run was produced for this proposal.
The suggested next pair is `ValidatorSeedTaggedCollection222.lean` and
`ValidatorSeedTaggedCollection222Checks.lean`, with precisely these imports:

```lean
import ZFCinPA.ValidatorSeedGuardedComprehension222
import ZFCinPA.SetCongruence
```

The concrete theory is the accepted `ValidatorFullSeedTheory222.seedTheory`:
set-language equality, raw membership irreflexivity, and the recognized full
seed schema. This proposal neither replaces it by raw CP/GIC nor supplies an
axiom-image oracle. Guarded was independently accepted while this audit was
being prepared; the inventory selects ROOT's accepted provider directly.

## 1. Exact semantic contract and source target

The reference is `KLowerTag.tag_collection`, not an unspecified Collection
principle. `ProfileCollection.ImageCollection mem R a b` is exactly

```text
(∀ y, mem y b → ∃ x, R x y) ∧
(∀ x, mem x a → (∃ y, R x y) → ∃ y, mem y b ∧ R x y).
```

The first clause is global-image support. Its input need not belong to a.
Adding that bound would strengthen the target and would not follow from the
reference proof. In `KLowerTag.tag_collection`, both variables range over
the tagged domain and the source formula has output in slot 0, input in
slot 1. The source-code version should preserve exactly these conventions.

Write `D(t,x)` for the literal source atom `t ∈ x`. For every internally
typed binary matrix `θ : Bootstrapping.Semiformula V ℒₛₑₜ 2` and arbitrary
internal terms `a,t : Bootstrapping.Term V ℒₛₑₜ`, define `collectionBody θ a t`
with one bound slot C to express

```text
D(t,C) ∧
  (∀ y, D(t,y) → y∈C → ∃ x, D(t,x) ∧ θ(y,x)) ∧
  (∀ x, D(t,x) → x∈a →
    (∃ y, D(t,y) ∧ θ(y,x)) →
    ∃ y, D(t,y) ∧ y∈C ∧ θ(y,x)).
```

The main proposed endpoint is

```lean
theorem tagged_collection
    (θ : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (a t : Bootstrapping.Term V ℒₛₑₜ) :
  seedTheory.internalize V ⊢
    emptyAt t 🡒 memTerm t a 🡒 ∃⁰ collectionBody θ a t
```

Its context is `{V : Type*} [ORingStructure V]
[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`. No truth assumption about the source formulas is supplied
at the Lean level. Empty(t) and D(t,a) are antecedents inside the actual
source derivation. Neither is a Boolean test on term codes. The endpoint
does not take a≠t, bounded free variables, an externally chosen source model,
a standard-length matrix, or a CProv premise.

Also expose `taggedCollectionProof : Source V ⊢! ...` and the exact
`Proof seedTheory (taggedCollectionProof θ a t).val (...).val` certificate.
Choosing a proof from the established internal proof-existence statement
does not make the chosen proof-code map a total Σ1 function. No such graph
is proposed without a separate definability proof.

The formula θ is an arbitrary raw source matrix, not silently identified
with a tagged or quotient interpretation. This generality will allow the
later actual represented interpretation to instantiate θ. It does not by
itself formalize that interpretation or its proof transport.

## 2. Finite source proof from full seed

The proof is the literal construction in `KLowerTag.tag_collection`, with
every use of equality performed by a source proof rather than Lean equality
of source term codes.

1. Use public `raw_augmented` with matrix `t∈z` to obtain
   E={a}∪{z∈a | D(t,z)}. Empty(t) and D(t,a), together with the actual
   irreflexivity axiom, prove a≠t, E≠t, t∉E, and that every tagged member
   of a belongs to E. These are all source implications.
2. Use public `raw_pair_of_empty t E t` to obtain r={E,t}. Since E≠t,
   r≠t and r cannot be a singleton. Empty t cannot be a singleton either.
   The singleton conclusions retain both equality directions; no source
   equality symmetry step may be replaced by a metatheory rewrite.
3. Define the typed binary seed matrix, with output v first and input u
   second,

   ```text
   K(v,u) =
     (u=r ∧ v=E) ∨
     (u=t ∧ v=t) ∨
     ∃ x, (D(t,x) ∧ Singleton(u,x) ∧ D(t,v) ∧ θ(v,x)).
   ```

   Apply the actual `openSeedProof K` at input r. Retain the entire
   support/closure/request pair, not merely its image projection. The
   public `seedPairAt` and `full_member_closure` definitions provide the
   existing literal closure interface. Request/support specializations can
   be derived locally from that exact pair and `openSeedProof`; private
   lemmas of earlier files are not proposed imports.
4. The root request uses K(E,r). Any returned K(z,r) must have z=E:
   its empty branch contradicts r≠t and its singleton branch contradicts
   r not singleton. Therefore E∈C.
5. Full member-closure at E, with the actual source proof t⊆E and K(t,t),
   gives t∈C. An output of K(z,t) is t: the root branch contradicts r≠t
   and the singleton branch contradicts Empty(t). Thus C is tagged.
6. For tagged y∈C, full support provides K(y,u) for some u. The root
   output y=E contradicts t∉E; the empty output y=t contradicts t∉t.
   The remaining branch supplies tagged x and θ(y,x). It makes no
   assertion x∈a, exactly as required by global-image support.
7. For tagged x∈a and a tagged y with θ(y,x), use the public singleton
   theorem to obtain sx={x}. Since x∈E, sx⊆E. Full member-closure at E
   with input sx and K(y,sx) yields z∈C and K(z,sx). The root and empty
   branches contradict the singleton exclusions. The third branch has
   Singleton(sx,x'), D(t,z), and θ(z,x'). Singleton uniqueness gives
   x'=x as a source equality. Apply the genuine arbitrary-matrix equality
   replacement below to derive θ(z,x).
8. Combine support and coverage, introduce all target quantifiers, and
   eliminate the chosen sx, r, E and C with the exact shifted contexts.
   The conclusion retains all ambient free parameters of θ,a,t.

This construction uses the seed and raw-pair/raw-augmentation endpoints
available through Guarded. It need not invoke guarded separation inside
the Collection proof itself. Both are complementary source resources for
the later tagged interpretation. No raw Collection axiom is assumed.

## 3. The substantive arbitrary-matrix transport is already available

`ZFCinPA.SetCongruence.setReplace` states, for every Δ1 set theory T
containing equality and every internally coded unary φ,

```lean
T.internalize V ⊢ eqAtom x' x 🡒 φ.subst ![x'] 🡒 φ.subst ![x].
```

Its formula code may be nonstandard. `replace_aux` proves it by actual
Σ1 structural induction on the internal formula code. The binder cases
shift φ and its free parameters, then use the actual internal quantifier
rules. It is not a standard-Nat-only substitution lemma.

The proposed local wrapper is

```lean
theorem matrix_second_transport (θ : Semiformula V ℒₛₑₜ 2)
    (y x' x : Term V ℒₛₑₜ) :
  Source V ⊢ eqTerm x' x 🡒
    θ.subst ![y,x'] 🡒 θ.subst ![y,x]
```

Instantiate `setReplace seedTheory` at
`φ := θ.subst ![y.bShift, Semiterm.bvar 0]`, then use the checked
`substs_substs` law. The required `𝗘𝗤 ℒₛₑₜ ⪯ seedTheory` follows from
literal subset inclusion into the first union component, using
`Axiomatized.le_of_subset`. `seedTheory_delta1` is already present.
No congruence premise about θ is added.

SetCongruence's fixed atomic seed laws use outer completeness/D1 for
fixed equality sentences. Its arbitrary internal matrix result then uses
the represented structural induction just described. Reusing that checked
theorem does not infer arbitrary-code proof existence from external
standard-Nat semantic completeness. No placeholder-template completeness
theorem is needed by the new leaf, despite its transitive import presence.

## 4. Literal binders, code constructors and checks

Use the existing `Semiformula`, `SemitermVec`, `subst`, `bShift`, `shift`
and `free` APIs. Do not create a new formula grammar. Under the existential
x in K, the bound slots are x=0, v=1, u=2. Thus the arbitrary θ occurrence
is exactly `θ.subst ![#1,#0]`. The ambient r,E,t terms receive the exact
three bound-variable lifts at that occurrence. Their free labels, and
every free label of θ, remain parameters.

In `collectionBody`:

| Occurrence | Bound slots | θ substitution |
|---|---|---|
| Global-image existential | x=0,y=1,C=2 | `![#1,#0]` |
| Coverage premise existential | y=0,x=1,C=2 | `![#0,#1]` |
| Coverage conclusion existential | y=0,x=1,C=2 | `![#0,#1]` |

Source opening must shift θ,a,t and all retained assumptions together.
An occurrence of free label 0 in θ is not an eigenvariable and must survive
that shift. The semantic `collSh` in KLowerTag sends marker/output/input
to 5/1/0 and later parameters to n+6; it explains the same slot pattern,
but no unproved equivalence of the semantic Form syntax and the current
internal Semiformula syntax is used as a proof rule.

Propose total raw constructors and fixed Σ1 graphs for:

* `collectionMatrixCode k E t r`, the exact K code;
* `collectionBodyCode k a t`, the one-slot conclusion body;
* `collectionConclusionCode k a t`, the full implication/existential.

Give exact typed-value identities for each. The total raw constructors
are defined on all raw codes; well-typed identities and proof endpoints
retain actual `IsSemiformula`/`IsSemiterm` evidence through typed arguments.
Auxiliary fixed singleton/atom graph helpers may remain private. The
entire chosen proof-code function is deliberately not assigned a Σ1
graph. Its actual `Proof` certificate is required.

Focused Checks should cover:

* the exact output/input order of arbitrary binary θ in K and both
  conclusion clauses;
* actual typed free label 0, a high free label, and a nested quantified θ;
* shift and free identities with θ,a,t and retained contexts all varied;
* arbitrary source terms with no assumption that their codes differ;
* the literal Empty(t) and D(t,a) antecedents, without externally assuming
  either holds;
* global-image support with an unrestricted tagged input; coverage alone
  uses x∈a;
* the actual proof-code certificate, raw graph instances and typed-value
  equalities, with axiom reports for transport and final endpoints.

No scope is assigned to a source theory recognizer for Collection, a
bounded proof search, or a translated arbitrary-proof endpoint in this
pair. If the binder/resource development needs another owned module, its
exact split should be reported before expanding imports or compiling it.

## 5. Position in the actual QHyp and marker routes

`KLowerEqv.tag_gic` applies `tag_collection` to the swapped matrix and
gets `ModelsGIC (tmem mem t)`. This is tagged, equality-free Collection;
it is not raw GIC for the original membership relation.

With additional exact pairs and transitive containers, the profile
development uses Collection instances to establish coded bisimilarity
reflexivity, symmetry, transitivity and extensionality. The eventual
`KQHyp.QHyp` interface also requires interpreted union, interpreted power
and singleton-closed containers. `Member` and `Eqv` there are the profile
definitions. Neither is raw membership/source equality, and neither is
identified with C222 `Eind` by this proposal.

`KLowerQHyp.tag_qhyp` and `zf_consistent_of_formSeed` describe the actual
semantic quotient/WF route. They are reference contracts, not an internal
proof transport available for arbitrary nonstandard source codes. The
present pair supplies one substantive source-schema family needed by
that route. Actual interpreted schema constructors, parameter closure,
remaining container/power resources, and represented quotient/WF axiom
images remain open. No raw `nativeTheory` CP/GIC shortcut is justified.

The new marker-counter proposal retains P(j), the domain d(j)=(&j∈#0),
and side context C(j), with `shift P(j)=P(j+1)` rather than a shift-fixed
marker. Collection's arbitrary t and arbitrary free parameters fit that
future family: after a checked interpretation constructor has supplied θ,
the source proof can be instantiated at t=&j. Its Empty(&j) antecedent
will correspond to the residual negative empty guard in a source sequent.
The required family substitution laws, bounded proof-induction motive,
actual image sequent and side-set elimination are still to be proved.
This plan does not instantiate `InternalInterpretation.Good` with &j.

After the actual ZF source-refutation route is established, Choice is a
separate existing bridge: `LSchema.provable_falsum_ZF_of_ZFC` is the
all-internal constructible reduction from a ZFC refutation to a ZF
refutation. It is not a theorem that the raw seed relation satisfies
Choice. Its reuse does not remove the tagged/quotient source obligations.
The present packet proves no ZF/ZFC calibration or HA equation theorem.

## 6. Exact authenticated cache and provenance boundary

The read-only auditor is
`validator-seed-tagged-collection-cache-audit.py`; its complete result is
`validator-seed-tagged-collection-cache-plan.json`, SHA256
`94c923959cc8870c08f452e26d330c68b8bea7f43961595498e5eb355cdde911`.
It authenticates **207 current custom modules / 136 Foundation modules /
615 artifact records / 45 external boundaries**, with 252 first primary
providers and all 660 first artifact providers. There are 2,431 distinct
reauthenticated paths. Every selected current source/header is checked,
including the actual Aesop meta import. Dependency order and exact
explicit package boundaries are retained. No prerequisite refresh is
needed, and no source in the selected closure is newly written here.

The selected Guarded provider is the accepted independent ROOT directory
`/tmp/validator-seed-guarded-comprehension222-root-mrsef1jx/lib`.
Its source SHA is
`af5b5e45b080dcbb186606f87542c02499944d9bdcb4f263a0959390272b0c54`,
object SHA
`29125a668191816879c77201103d63cb95b7daf2562a48d450f17e57092c81d7`.
ROOT packet `ef51f6203ee7c0376888a1682bc48d7a7c398d7f028531075111d4be8051d424`
and 15-file manifest
`4c4abe69d3c3614ed285addc3502ded78203bf060a3202ea8d12f6ca177bdd2b`
are rehashed, alongside the author packet and all 71 historical files.
This plan was not frozen provisionally and therefore needs no provider
replacement supplement for Guarded.

The four extra cached clients are TypedTemplateProofCompiler,
SetPlaceholders, SetPlaceholderQuotient and SetCongruence. Their selected
historical source/object records are identical to those reauthenticated
in the accepted fixed-consistency73 and consistency-semantics closures.
The latter independent provider supplies these four first objects. The
original verification-record hashes and absent server/private/IR companion
qualifications remain recorded. The source/object pair for SetCongruence
is `a72c669ecd09b1fdb3dfb7aafbb9fd137fd7f6eda96f76f021f5de8e5bf4eaaf` /
`cc6dd0d95f48fc7d2892593fd2a24722464b9af885b818a8ce08dbe2a64cd754`.
No claim is made that these four sources, or the Foundation closure, were
freshly compiled in this audit.

Two metadata-only audit failures are preserved: v1 treated a ROOT
repository-relative manifest path as bundle-relative; v2 encountered the
older peer manifest's object-with-files format after resolving the path
convention. The final auditor accepts exactly those recorded formats.
Neither failure involved Lean execution, source typing, a changed theorem
or a cache mutation. The final run succeeded without changing any parent
evidence. Its driver, both failed versions/logs, final log, this plan and
the resulting inventory are pinned in a separate manifest.

Only after review would the proposed pair be authored and freshly compiled
into two absent regular private outputs with pinned Lean4.32,
`-M6000 -j1 -DElab.async=false`, one worker and a 512MiB reserve. Every
attempt and final source/Checks/driver would be retained and read before
execution. No shared source, object, vendor dependency, display artifact
or Git state is changed by this proposal.
