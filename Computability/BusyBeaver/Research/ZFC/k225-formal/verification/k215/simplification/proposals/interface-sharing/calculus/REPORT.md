# One quotient-model proof core instead of generated forks

## New recommendation at the pinned current sources

Pin: `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

Promote the existing `KQHyp.QHyp`-parametric quotient development to the common
implementation, and supply the older `ModelsCPGIC` interface through one checked
adapter. Stop generating a second copy of quotient proofs for the K calculus.
This is distinct from phase12's ZFModels/WFModelCore import split, the shared
implication proof, and the previously proposed direct full-seed construction.

Six current KQ1 files explicitly declare themselves generated forks:
KQ1Model, KQ1Separation, KQ1Basic, KQ1Power, KQ1Replacement and KQ1Collect. Their
current total is805 lines /34,291 bytes. This is GROSS duplicated-development
inventory, NOT805 removable lines or net savings. Some lines are interface
adaptations rather than duplicates. The exact54-line /2,201-byte block from
memberForm through equalityFree_translate in KQ1Model and QuotientModel is
byte-identical. A portable owned reader verifies both claims without running
the received generator.

## The existing weaker interface is already sufficient

QHyp has exactly nine fields: formula-indexed GIC, Eqv reflexivity, symmetry,
transitivity, extensionality, raw profile pairs, interpreted union, interpreted
power and singleton-closed containers. Existing KQ1 proofs derive quotient
Separation, Replacement, Collection and the semantic ZF-model construction from
that interface. We do not propose weakening or replacing any field.

The stronger CP/GIC model provides all nine fields via existing theorems:

- gic: h.2;
- refl/symm: ProfileModel.eqv_refl_of_model / eqv_symm_of_model;
- trans/ext: CompositionModel.eqv_trans_of_model / eqv_extensionality_of_model;
- pairs: ProfileModel.pairs_of_model;
- union: QuotientBasic.interpreted_union;
- power: QuotientPower.interpreted_power;
- singleton: QuotientBasic.interpreted_singleton_closed.

`proposed/CPGICQHyp.lean` is a concrete25-line staging adapter using those exact
providers. `proposed/QuotientCompatibilityAudit.lean` gives four explicit rfl
compatibility targets and a consumer of KQ1ZF.zf_consistent. Both files are
UNCOMPILED proposals. Their Print Assumptions commands are future checks, not
reported outputs. No axioms, admissions, external execution or new assumptions
are introduced in their source.

## Quotient compatibility, not a hidden transport obligation

The original and forked modelSetoid definitions both have literally `Eqv mem`
as their relation. Their other components prove equivalence laws and are Prop
fields. Their Domain is Quotient of that setoid; mk uses Quotient.mk; and their
quotientMember is Quotient.liftOn₂ of the identical predicate `Member mem`.
Only the proofs establishing well-definedness differ.

Consequently, after unfolding these transparent definitions, Lean kernel proof
irrelevance should identify the proof fields and proof arguments. The expected
compatibility is DEFINITONAL equality, not a nontrivial quotient equivalence:

    old.modelSetoid mem w h = shared.modelSetoid mem w (ofCPGIC mem w h)
    old.Domain mem w h = shared.Domain mem w (ofCPGIC mem w h)
    old.mk mem w h x = shared.mk mem w (ofCPGIC mem w h) x
    old.quotientMember mem w h = shared.quotientMember mem w (ofCPGIC mem w h)

The audit file requires rfl for each. This reasoning is strong source-level
evidence, NOT a substitute for compiling those targets. If one fails, inspect
which definition differs; do not silently insert casts or claim old theorem
types survived. No quotient representative choice is needed for these four
compatibility equalities. Existing collection proofs still choose lifted
valuations where they already did; no claim removes Classical.choice or Quot
from the final assumptions.

## Critical import-cycle issue and correct migration order

The staging adapter imports the old QuotientBasic and QuotientPower. That is
acyclic NOW, while both implementations remain. It is NOT the final adapter:
rewriting those modules as facades that call this same adapter would create a
cycle. Resolve it before replacing any facade.

1. Extract the54-line shared formula translation/RelSat block to a neutral
   QuotientSyntax module. Preserve old names with aliases/wrappers. Its existing
   lemmas depend on raw membership/bisimulation formula semantics, not an
   instantiated quotient or a CP/GIC model.
2. Extract the raw resource providers to CPGICQuotientResources. The needed
   original statements are interpreted_union, interpreted_power and
   interpreted_singleton_closed. Retain their existing proof bodies. Power
   additionally needs trace_instance and the formula-only separation_instance
   support. That support uses translate/RelSat but NOT the actual quotient or
   its Separation theorem, so route it through QuotientSyntax. Do not import
   QuotientSeparation wholesale, which would reintroduce the cycle.
3. Point ofCPGIC to those raw providers. Its dependencies are then QHyp,
   ProfileModel/CompositionModel, neutral syntax and raw resource proofs only.
4. Keep the existing KQ1 implementation as the first shared core, avoiding an
   unnecessary namespace renaming. Replace the old CP/GIC quotient proof
   bodies with thin wrappers instantiating this core with ofCPGIC. Verify the
   rfl clients and original theorem statements before relying on aliases.
5. Update the producer/template maintenance policy so it no longer regenerates
   the removed proof forks. Inspect and change the producer as text, rather
   than execute received scripts. Do not delete historical evidence.

Resulting direction:

    profile semantics -> QuotientSyntax + raw CP/GIC resources -> ofCPGIC
    QHyp -> KQ1 shared quotient core -> KQ1ZF
    old Quotient* facades -> shared core instantiated with ofCPGIC

The K lower endpoint retains its current direct QHyp provider tag_qhyp. It must
NOT be forced through ModelsCPGIC: the tagged domain intentionally lacks the
older literal-power-container premise. The upper/legacy CP/GIC lane alone uses
the adapter. Both lanes retain their original assumptions and conclusions.

## Small concrete client patch and an honest negative result

KLowerQHyp imports QuotientModel only for memberForm and sat_memberForm. Those
are in the exactly identical block in KQ1Model. `minimal_import.patch` replaces
the import and those two qualified names, with no other proof edit. This is a
low-risk preliminary use-site cleanup, still requiring Lean compilation.

The owned import-graph audit finds NO dependency reduction from this micro-patch
alone: another path still reaches the old quotient implementation. In its
explicit KEndpoint215-root scope the fetched-project closure is167 before and
after, with zero added/removed modules. That scope is not phase12's broader
179-module audited endpoint/client closure. Do not claim the micro-patch lowers
the179 figure or removes805 lines. The substantial benefit requires the shared
implementation and compatibility facades above.

## Rocq comparison and scope

The inspected Rocq Complete222 route already abstracts the interpreted proof
predicate Q and reuses the standard K0 lower chain, rather than literally
mirroring these Lean-generated KQ1 files. It would be misleading to claim the
same805-line deletion in Rocq. Preserve that language's existing theorem
interfaces and use explicit small adapters where its generic construction is
instantiated. The reusable principle is one semantic construction with checked
hypothesis adapters, NOT making either kernel trust the other's result.

This round supplies a concrete new simplification primarily in the Lean
logical-model implementation. The companion current-source/runtime review can
identify Rocq-specific reductions. It neither rebrands the old direct-seed
proposal as new nor recommends porting a new model development unnecessarily.

## Evidence and remaining validation

Bundled inputs are exact current sources, independently bound by the review
worker to the accepted phase12 source set. AUDIT.json gives individual hashes.
Run `python audit_forks.py` and `python audit_imports.py`; both are new owned
standard-library scripts, reject optimized Python, and execute no received
source or build scripts. The first checks source identities/structure; the
second checks the supplied import graph. Neither performs Lean elaboration.

No Lean/Rocq executable is available on current PATH; no formal compilation,
net line-count saving, fresh endpoint axiom report or build-speed improvement
is claimed. Before deployment: compile the staged adapter and rfl clients,
perform the cycle-free extraction, compile compatibility wrappers against all
old signatures, and rebuild the unchanged endpoint plus compatibility clients
with the same named axiom reports. The machine and its source are untouched.

### Do not transfer Lean conversion claims to Rocq

The four proposed rfl compatibility checks rely specifically on Lean's kernel
proof irrelevance for proof fields and arguments. They are NOT a claim about
Rocq conversion. A Rocq interface-first refactor should preserve and reuse the
same carrier, relation and setoid instance explicitly wherever possible. If an
existing client changes quotient/setoid representations, supply its appropriate
explicit morphism/transport theorem under existing assumptions. Do not add a
proof-irrelevance axiom to imitate the Lean alias argument. No Rocq duplication
count or concrete Rocq quotient-equivalence proof was established in this audit.
