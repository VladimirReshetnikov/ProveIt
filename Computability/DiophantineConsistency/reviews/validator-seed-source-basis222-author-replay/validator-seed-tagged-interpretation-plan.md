# From the concrete C222 seed theory toward internal ZFC interpretation

27 October 2026. Read-only source/API and cache plan by circuit_reduction.
No new Lean source, compiler invocation, overlay, or dependency refresh is part
of this audit. The accepted full-seed packet is unchanged.

## 1. Recommendation and exact remaining endpoint

The next coherent pair is `ZFCinPA.ValidatorSeedSourceBasis222` and its Checks:
an explicit represented proof constructor for **every internally typed open
full-seed body**, followed by genuine source-theory proofs of an empty object,
singletons, and a nonempty tagged domain. This discharges a real uniform
schema-instance obligation and the nonempty-domain prerequisite. It does not
pretend to discharge tagged Collection or the whole interpretation.

The eventual missing arithmetic theorem is, for every model `V` of IΣ2,

```lean
Provable (𝗭𝗙 : SetTheory) (^⊥ : V) → Provable seedTheory (^⊥ : V)
```

where `seedTheory` is the exact accepted equality + irreflexivity + full-seed
schema, with its actual Delta1 recognizer. Then the already proved
`LSchema.provable_falsum_ZF_of_ZFC` and
`ValidatorFullSeedTheory222.seedTheory_refutation_witness` compose to an
actual C222 History value2 witness from an internal ZFC refutation.
Neither that missing arrow nor its hypotheses are silently supplied here.

There are two independent structural obstacles after the proposed basis:

1. The seed route gives a **tagged QHyp quotient interface**, not the raw
   CP/GIC theory used by `NativeSchema`.
2. The tagged domain uses a chosen empty marker. The existing all-internal
   interpretation theorem requires shift-fixed meanings and therefore cannot
   directly accept that free marker.

## 2. Exact accepted source boundary

`ValidatorFullSeedTheory222` has the literal definitions

```lean
seedSchema := Set.range (fun K => (fullSeedBodyMeta K).univCl)
seedRecognizerBodyVal k := fullSeedBodyVal (Bootstrapping.neg ℒₛₑₜ k)
seedTheory := ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ seedSchema
```

The range is unchanged by negative reparameterization. Its actual internal
recognizer accepts a closed body together with an internally typed matrix,
not just quotations of standard matrices. The accepted AxOK theorem handles
all recognized instances and all internal closure lengths under IΣ2.

However, source-theory *provability of an arbitrary open instance* is a
separate direction. `recognizerBody_quote_bound` is a standard-Nat quotation
bound used to identify the schema set; it cannot itself justify the desired
all-internal open-instance constructor. The needed internal bound can be
proved directly from the same literal negative identity occurrence.

Accepted provider:
`/tmp/validator-full-seed-theory222-peer-tnk8lknu/lib`.
Root accepted commit `3b9331242e`.

- Main source: `481f8f44a4d01cda7f41d92463336aabae66573e3764f056785667192bb33acd`.
- Checks source: `048cc4850a073f18c3eb29bc704b61b755db8c45eb91d922ae2743593be9ad6c`.
- Main object: `c0279d1a80ba6b1a7bafa5f75c0cf9e1a66126f0a5f26eb4b2bd76bb06995fb0`.
- Peer packet: `4c0307c365be10c8680d27ed33b60caff41914bc390014a25955ea9fd5152a56`.
- Root acceptance: [receipt](../reviews/validator-full-seed-theory222-root.md),
  SHA `3c35efbc6b7754b66b3fb2c29e48972102c686eab8a833ffd0d1bd40f889dcf0`.
- Root authentication manifest: `f69e4d966c48e84358f26497283e80d363ace30d4876fde1b96d04693ba6e1c9`.

## 3. Proposed first pair: uniform open instances and actual source basis

Only two imports are proposed:

```lean
import ZFCinPA.ValidatorFullSeedTheory222
import ZFCinPA.ModelCodedOpenSchemaAxioms
```

Proposed owned paths are
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedSourceBasis222.lean`
and `ValidatorSeedSourceBasis222Checks.lean` in the same directory.

The latter transitively imports the existing generic closing/specialization
machinery and ZFDelta1. Its ZF wrappers are not used as seed axiom images.
No NativeTheory, NativeSchema, R2, semantic KLower theorem, or LSchema proof
is imported into this first leaf.

### A. Uniform literal constructor

Work under `[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`. The source proof constructor
needs no C222 image theorem or supplied source proof. Proposed names and
contracts, with `L := ℒₛₑₜ`:

```lean
seedInstanceCode k := seedRecognizerBodyVal (neg L k)
closedSeedCode k := closeFormulaCode L (seedInstanceCode k)
openSeedProofCode k := openAxiomProofCode L (seedInstanceCode k)

seedInstanceCode_eq (hk : IsSemiformula L 2 k) :
  seedInstanceCode k = fullSeedBodyVal k
closedSeed_recognized (K : Semiformula V L 2) : SeedR (closedSeedCode K.val)
closedSeed_mem (K : Semiformula V L 2) :
  closedSeedCode K.val ∈ seedTheory.Δ₁Class
openSeed_isProof (K : Semiformula V L 2) :
  Proof seedTheory (openSeedProofCode K.val) (fullSeedBody K).val
openSeedProof (K : Semiformula V L 2) :
  seedTheory.internalize V ⊢! fullSeedBody K
```

The definitions deliberately use the accepted negative parameterization.
On arbitrary raw invalid input no double-negation identity is asserted.
The graph of `seedInstanceCode` is the composition of actual `negGraph` and
`recognizerBodyGraph`; the open-proof graph then composes the existing total
`openAxiomProofCodeDef`. Thus no new proof-search or proof chooser is needed.

The proof is concrete:

1. Prove `subst L (^#0 ∷ ^#1 ∷ 0) k = k` for every internally typed two-slot
   matrix, using the actual `subst_eq_self` and the two vector lookups.
2. Follow the eleven literal constructor inequalities from that negative
   identity copy to obtain `neg L k ≤ fullSeedBodyVal k`. Apply this to the
   internal negative parameter and use typed `neg_neg`. This extends the
   needed bound internally without assuming code monotonicity of negation.
3. Apply `ModelCodedClosedSchemaAxioms.closeFormulaCode_schemaRecognizer`
   to parameter `∼K` and `seedRecognizerBodyVal`. The existing
   `bindFreeAt_closing` supplies a shift-fixed closed core and its actual
   internal binder count; reopening recovers the full original matrix.
4. Unfold the accepted recognizer and union membership, then use
   `ModelCodedOpenSchemaAxioms.openAxiomProofCode_isProof`.
5. Obtain the typed proof with `typedProofOfCode`; its `.val` is exactly the
   explicit code above. All internal free labels and nested binders survive.

### B. Actual source proofs of empty, singleton, and tagged nonempty

Define exact ordinary source formulas (and typed substitution instances):

```text
Empty(t)       := ∀z, z∈t → ⊥
Singleton(c,t) := ∀z, z∈c ↔ z=t
Tag(t,x)       := t∈x
```

Required endpoints are actual typed source proofs, not semantic hypotheses:

```text
seedTheory.internalize V ⊢! ∃t, Empty(t)
seedTheory.internalize V ⊢! ∃c, Singleton(c,t)   [every internal term t]
seedTheory.internalize V ⊢! ∃x, Tag(t,x)        [every internal term t]
seedTheory.internalize V ⊢! ∀t, ∃x, Tag(t,x)
seedTheory.internalize V ⊢! ∃t, (Empty(t) ∧ ∃x, Tag(t,x))
```

Their finite derivations use only actual equality/logical rules and A:

- Instantiate the matrix by falsity. Its full closure clause says every
  member of the resulting container has a false matrix witness, giving
  `Empty`. The root request is vacuous, but the existential container is an
  actual proved seed instance; this does not assume an empty domain.
- For an arbitrary internal term `t`, use the matrix `K(y,x) := y=t`, with
  `t` lifted across both matrix slots. The support part gives every member
  equal to `t`; the root request at `y=t` produces a member equal to `t`.
  Actual source equality gives both directions of `Singleton(c,t)`.
- Instantiate singleton membership at `t` and generalize with the actual
  eigenvariable shift to obtain the universal tagged-nonempty sentence.
- Combine the genuine empty and tagged-nonempty witnesses.

The source equality symbol is the equality of seedTheory. Its later C222
image is the accepted `Eind` interpretation. It is not identified here with
primitive numeric `weq` or with the later profile-bisimulation `Eqv`.

Checks should cover the raw composed graph, typed double negation, truth and
falsity matrices, arbitrary internal free indices, nested/sparse free labels,
the exact open proof code, singleton at free0 and a general internal term,
and the literal closed tagged-nonempty endpoint. No model premise, finite
length bound, standardness premise, or assumed source-axiom image is allowed.

## 4. What the retained KLower route really requires

The semantic source route is explicit:

- `KLowerSeed.formSeed_of_fullSeed`: converts the named standard-formula
  FullSeed interface into the standard de Bruijn FormSeed interface.
- `KLowerRaw`: exact empty/singleton/pair/transitive/power constructions;
  augmented comprehension `{a} ∪ {z∈a | θ(z)}` and guarded tagged
  comprehension `{B,t} ∪ {z∈B | θ(z)}`, with `B≠t` and `Empty(t)`.
- `KLowerTag`: genuine tagged separation, pairs, union, transitive
  containers, and Collection for **all formula matrices and parameters**.
  The Collection matrix explicitly handles root and marker cases and uses
  a tagged singleton witness; it retains the full seed closure + request.
- `KLowerEqv`: builds the profile bisimulation equivalence on the tagged
  domain and proves interpreted `Member` congruence.
- `KLowerQHyp.tag_qhyp`: supplies exactly the QHyp fields.
- `KQ1ZF.zf_consistent`: quotient extensionality, Separation, Replacement,
  interpreted power and singleton-closed containers give Infinity; quotient
  Collection gives WF closure; the WF part satisfies ZF with Foundation.

**Critical limitation:** `KQHyp.lean` explicitly notes that the tagged domain
lacks the literal power containers of a CP/GIC model. Its `power` and
`singleton` fields use interpreted `Member` and `Eqv`. Consequently
`NativeSchema.provable_falsum_native_of_ZF`, whose target is raw CP/GIC
`nativeTheory`, cannot be inserted into the seed route without a separate
proof of those stronger raw hypotheses. No such proof was found or assumed.
The reusable semantic route is KQ1/QHyp, not a relabeling of NativeTheory.

These KLower/KQ1 results quantify over ordinary Lean Form and ordinary
structures. They guide finite proof templates and exact formula definitions;
they are not themselves all-internal transformations of nonstandard source
proof or schema codes. Fixed template completeness may produce a fixed
ordinary proof which a checked compiler then instantiates at every internal
matrix; completeness of the entire standard seed theory alone does not do so.

## 5. Marker parameter diagnosis and viable later work

`InternalInterpretation.Good P` requires `dom P` to be a one-slot formula
fixed by free-variable shift, and each two-slot atom meaning shift-fixed.
The actual free-marker domain

```text
d₀ := (&0 ∈ #0)
shift d₀ = (&1 ∈ #0) ≠ d₀
```

violates that exact contract. The inequality is a direct constructor/index
distinction, not a semantic counterexample to the seed theory. The analogous
`InternalRelativization.relativize_shift/free` requires the same fixedness.
`NativeWFClosedParameters.good_parameter` proves only syntax for a different
closed untagged WF/quotient parameter; it supplies neither tagged nonempty
nor the required tagged axiom images.

The following existing tools were checked before proposing new transport:

- `OpenSetTemplateCompiler.compileOpenTemplate` and
  `OpenTemplateClosure.closeTemplate` preserve arbitrary internal predicate
  free parameters. Their proof input and shift buffer are externally finite.
  They are suitable for the fixed tagged-comprehension/Collection templates,
  including arbitrary internal matrix parameters, not for an arbitrary
  internally coded source derivation.
- `ModelCodedFreeRenaming` has internal chosen/level/offset maps and exact
  shift/free/substitution laws. `ModelCodedProofRenaming.derivable_rename`
  performs all-internal proof renaming under explicit axiom-renaming closure.
  Its exported named generalization is currently specialized to ZF/ZFC.
  This is useful hygiene machinery, but not a tagged interpretation theorem.
- `ModelCodedBindOne` binds one arbitrary internal free label at the actual
  internal depth; `ModelCodedBindOneSwap` proves the two-slot interchange.
- Foundation `DirectTranslation` also uses closed semisentence meanings and
  ordinary proof inputs. It does not remove this marker obstruction.
- `ModelCodedPredicateParameters` replaces finitely many arithmetic constants
  by internal arithmetic numerals in fixed templates. The raw set marker is
  a set-language variable, not such a numeral; this is not a constant-extension
  conservativity theorem for the tagged set interpretation.

There is therefore no inspected ready-made represented parameter/constant
extension that closes the gap. A later marker-safe interpreter must explicitly
reserve the marker while shifting source free variables, and must either
generalize/discharge it under proved `Empty` or compile a conservative named
constant extension. It must track the guard and domain side formulas under
ALL, EXS, SHIFT, CUT, and arbitrary internal closure lengths. The final
refutation theorem must quantify over arbitrary internal source proofs.

A viable later statement is a **guarded** internal proof transport, after
defining the actual marker-reserving formula map: from a source derivation,
derive a seedTheory sequent containing `¬Empty(marker)`, the translated source
sequent, and domain side formulas for its source parameters. Its induction
motive must vary the marker environment/buffer, not assume a fixed free marker
commutes with shift. Proved nonempty and empty-marker existence must discharge
these side formulas at falsum. That theorem is not yet defined or authorized
by this plan; no existing Good hypothesis is weakened.

Suggested order after the first basis pair: parameter-preserving raw augmented
and tagged comprehension templates; guarded tagged Collection for every
internal matrix; represented QHyp axiom images; reviewed marker-safe proof
transport and closure; exact quotient/WF schema interpretation. A represented
parameterized interpreter can be developed in parallel only after its precise
reserve/guard interface is separately reviewed. No raw GIC/CP premise replaces
any step.

## 6. Choice and exact reusable internal contracts

`LSchema.provable_falsum_ZF_of_ZFC` already has the required all-internal
contract (under IΣ1):

```lean
(h : Bootstrapping.Provable 𝗭𝗙𝗖 (^⊥ : V)) →
Bootstrapping.Provable 𝗭𝗙 (^⊥ : V)
```

Its `hSchema` discharges every internal Separation/Replacement instance in
the constructible interpretation. The module also proves the actual IΣ1/PA
consistency equivalence. No new standard-Nat Choice semantic lemma is needed.
This theorem remains separate from the unfinished seed interpretation.

`InternalInterpretation.provable_falsum_of_interp` is reusable exactly when
all its hypotheses fit: Good P; every set-language term is a free variable;
every internal source axiom has an actual target derivation with domain side
formulas; and actual target proof of `∃x,dom P`. It is not an image oracle.

Pins (complete selected records are in the JSON):

- LSchema source `c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2`,
  accepted root73 object `78878fd2bf4bfb550e60a1a04a70faac9ba20da035137f071fc52b13959f14c0`.
- InternalInterpretation source `60bdb604d5aa34402a3a050a397a4b46b7e2892ae1a14875a806caa9dfac3720`,
  authenticated historical object `9552dfb313ed4cd0de34406310853af9f088b79b906e3533a344a033cff27646`.
- NativeSchema source `a707e5ca406d9c45c1ce436bdfaf39c36c3511bec4317dac0bc380b4656c108d`,
  root73 object `6f78827443d1bbd974b1ef4100c28f919cce42c4add04e456bbb73b7295cc170`;
  retained as a contrast/possible template guide, not a valid seed substitution.

## 7. Authenticated cache boundary and audit scope

The recommended two-import closure has **200 current-source cached modules,
136 Foundation modules, 608 recorded object artifacts, and 45 external
boundaries**. Relative to the accepted FullSeedTheory input inventory it adds
the accepted FullSeedTheory object and eight already-authenticated custom
modules: ModelCodedBindFree, SeparationDelta1, ReplacementDelta1, ZFDelta1,
ModelCodedSchemaAxioms, ModelCodedClosedSchemaAxioms, ModelCodedSpecialization,
and ModelCodedOpenSchemaAxioms. No new Foundation module or compiler run is
needed for this planned pair. Historical source/object and absent-companion
qualifications remain explicit.

The later finite-template import candidate is 208/136/616/45; the later
InternalInterpretation + ProofRenaming candidate is 209/136/617/45. These
are feasibility inventories, not authorizations or proofs of the later work.
The LSchema/NativeSchema records are pinned as reviewed tail contracts; this
audit does not freshly replay their entire closure.

The final JSON contains dependency order, every current source and selected
object hash, explicit external paths, parent acceptance records, and source
anchors. The planning driver only parses headers and rehashes data. Initial
inventory and driver v1 are retained separately; adding the decisive KQHyp
source anchors did not change any import/provider selection. No compiler
failure or source change occurred during this read-only audit.

Full reads include the new accepted seed theorem, KLower Seed/Raw/Rel/Tag/
Eqv/QHyp, KQHyp and KQ1ZF, LSchema, generic closed/open schema constructors,
OpenSetTemplateCompiler and OpenTemplateClosure. InternalInterpretation,
renaming/parameter infrastructure, NativeInterp and KQ1Model/Collect were
reviewed at the exact definition/theorem sections relevant to these contracts;
no claim of a new full review of every existing dependency is made.

No ZFC→seed, ZFC→C222, PA current-equation, or final HA equivalence theorem
is claimed by this plan. All existing equation and proof artifacts are intact.

Frozen final inventory: [validator-seed-tagged-interpretation-plan.json](validator-seed-tagged-interpretation-plan.json),
SHA `f139d86765d1827c6dfb938065ae4e705e96387840dc5fabae7221d065326f46`,
952 distinct path/hash observations. The complete metadata driver is
`/tmp/seed-tagged-route-plan.py`; both that driver and its preceding v1 were
fully read before their respective read-only executions.
