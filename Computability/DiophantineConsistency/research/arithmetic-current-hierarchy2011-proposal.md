# Exact hierarchy of the maintained arithmetic endpoint

29 October 2026. Read-only dependency/build proposal; implementation and
compiler launch await independent verification of this plan. The prior
HalfRatio task was stopped before its unexecuted planner ran. No overlapping
Lean files, old proofs or compiler caches are changed here.

The new ArithmeticCurrentHierarchy2011 and Checks will import only
FoundationHACurrentNoZero2011 and FoundationZFCConsistencyNat. The three
public statements concern the exact constants already used by the closed
HACurrentEquation2011.isigma1_proves_current_iff_consistency:

```
Hierarchy 𝚷 1 FoundationHACurrentNoZero2011.classicalSentence
Hierarchy 𝚷 1 FoundationZFCConsistencyNat.sourceSentence
Hierarchy 𝚷 2
  (FoundationHACurrentNoZero2011.classicalSentence 🡘
   FoundationZFCConsistencyNat.sourceSentence)
```

Optionally expose the exact `𝚷-[2].Sentence` wrapper and its `val =` the
same biconditional by reflexivity. There is no renamed theory, equation,
Gödel checker, normal-form replacement or extra mathematical premise.
The first proof closes an arbitrary negative equality under its actual
fourteen universal binders, using a short structural allClosure helper and
Hierarchy.all/nrel. Its huge coefficient terms stay opaque. The second
uses the existing `Theory.consistent : 𝚷₁.Sentence` and `pi_prop` certificate.
For the biconditional, Hierarchy.accum promotes each Π1 proof to both Π2
and Σ2. Hierarchy.iff_iff then certifies the unchanged syntax. No semantic
completeness, model hypothesis, arithmetic induction or new axiom is needed.
Expected new source size is about 45 lines plus 25 focused Checks.

This establishes only the syntactic complexity input for a future
conservation theorem. It does not formalize PRA or Parsons' theorem and
does not itself construct a PRA derivation. The existing closed IΣ1/HA
endpoint binds the maintained 14-variable Carrier65 sentence. The small 13
and other metric equations still need their own exact internal transfers.

## Current-source dependency boundary

The complete current source-header DAG of these two imports contains 430
custom modules including 139 Foundation modules and 57 external boundaries.
The accepted historical ConsistencyNormalization inventory has 455 modules.
Exactly 338 reachable modules have unchanged source, headers and all current
transitive dependencies. Fourteen reachable sources changed, and the split
PAHF.PACore module is new; including their dependent clients gives 92 required
fresh non-Foundation prerequisites. All 139 Foundation sources remain reusable.
The exact list and order are recorded in the accompanying cache inventory.

The 37 successful records of the recent HACurrent endpoint reconstruction
have no overlap with those 92 prerequisites. That reconstruction explicitly
used unaudited historical transitive objects and is not selected as evidence
for their current-source validity. Its records are pinned only to document
this exclusion. Mere presence of an object is never treated as authentication.

The safe proposed build is to reuse only the 338 authenticated unchanged
modules, exclude every affected old object, refresh the 92 listed sources
in topological order, then build the two new leaves. PAHF.PACore has 8,600
lines, so this dependency refresh is materially larger than the new proof.
No old source is edited and no Foundation, package or broad umbrella is
rebuilt. A smaller provider set could be selected only after an explicit
source/dependency authentication and revised independent plan review.
A Foundation-only generic helper would leave this exact named-constant
client's dependency refresh unchanged; it is not substituted for the target.

The planner rehashes the historical author/peer manifests, all current
sources, selected cached objects and each first artifact provider, and
preserves original object provenance. Changed historical source hashes are
recorded as excluded evidence rather than falsely required to match current
bytes. External package interiors retain their existing explicit boundary.
It creates no overlay and invokes no Lean or Lake compiler.

After independent approval, every refreshed source and complete new pair
must be read, all inputs snapshotted before compilation, and all attempts
preserved. Use pinned Lean 4.32 -M6000 -j1 -DElab.async=false, one thread,
fresh regular outputs and 512MiB reserve. No shared object or Git mutation.

The first inventory was revalidated at HEAD fa059b73ac170ec64631aee36a788a596c262471
with 40 affected modules. The first audit passed; its proposal had only prose
formatting errors in an identifier and command flags. The second audit passed
all selected pins but rejected a concurrent HEAD change. The third audit
correctly rejected the old 40-module count after the upstream
ModelCodedBinderAbsorption change introduced another 52 affected descendants.
All prior inputs, diagnostics and the original successful inventory are retained
under plan-history. No compiler or overlay was created in any attempt.

The final inventory records its start and finish commits and rehashes every
selected source/provider byte. Unrelated commits may proceed. It selects 755
cached custom artifacts plus 57 boundary primaries and 171 companions (983
existing first providers). The 92 refreshes and two target outputs are additional
fresh private artifacts. The upstream BinderAbsorption commit reports only
four local builds using cached transitive dependencies; that is not substituted
for the current-source descendant refresh.
