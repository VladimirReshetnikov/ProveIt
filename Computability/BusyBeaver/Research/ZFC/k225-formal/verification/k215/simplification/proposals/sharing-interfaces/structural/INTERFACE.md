# One semantic proof, multiple certificate front ends

## Recommendation

Preserve the public all-register source-equivalence theorem and the runtime
proofs. Put the halting induction in one representation-independent semantic
bisimulation module per language, and make each certificate checker prove that
semantic predicate. Lean already has the essential interface in RMBisim.
Port that boundary to Rocq instead of copying a soundness induction each time
certificate storage or pointer equality changes.

The inspected Rocq Bisim230.v and NormalizedBisim.v contain respectively50 and53
lines of checker-specific simulation proof. Their central32-line sim/nsim proof
is BYTE-IDENTICAL after renaming just three identifiers. `audit_refactor.py`
checks this exact claim, with source hashes in AUDIT.json. These figures are
identified duplicated blocks, not a predicted net line saving: adapters and a
shared interface also need source lines and compilation.

## Minimal semantic interface

Use the existing Lean definitions, not a new register-machine semantics:

    BranchGood t1 t2 S A B :=
      exists l1 P1 l2 P2,
        seg t1 fuel A = Some(l1,P1) /\
        seg t2 fuel B = Some(l2,P2) /\
        (forall i, count l1 i = count l2 i) /\ S P1 P2.

    EntryGood t1 t2 S P1 P2 :=
      both sites halt
      OR both sites test the same register r, with BranchGood for
         their consumed-path nonzero successors and zero successors.

    Bisim t1 t2 S :=
      BranchGood t1 t2 S [] [] /\
      (forall P1 P2, S P1 P2 -> EntryGood t1 t2 S P1 P2).

The one generic theorem is:

    bisim_halts_iff : Bisim (ptree p1) (ptree p2) S ->
      forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).

Prove it with existing seg_run, seg_hn and test-step lemmas. The decrement test
consumes one actual step before recursive segment reasoning, even when the
segment contains no increments. This is the strict-progress fact needed for
induction on a finite halting witness. Symmetry swaps both segment witnesses
and the relation, so there is no reverse certificate or second induction.
Rocq can retain its pointwise R1/R2 equality formulation without introducing
functional extensionality. No bound or invariant on initial registers is added.

## Checker adapters and exact theorem boundaries

For any storage object D, expose only:

    lookup : D -> nat -> option Entry
    allEntries : (Entry -> bool) -> D -> bool
    lookup_all : lookup D j = Some e -> allEntries f D = true -> f e = true.

The literal checker adapter proves `literal_check_bisim`. Its relation is
successful lookup pairs, and literal endpoint equality supplies related sites.
The normalized checker proves `normalized_check_bisim` using the lifted relation

    Sbar P Q := exists A B,
      lookup-pair-relation A B /\ ipeq P A /\ ipeq Q B.

Required small lemmas:

1. `tsite_ipeq`: equivalent zero-padded paths have equal site lookup results,
   INCLUDING the consumed leaf path. This follows from existing walk_ipeq and
   prefix/consume equality, not from a false statement that inc_path preserves
   arbitrary ipeq directly. The actual increment/break operates on consumed Q.
2. `branch_ok_good`: count equality plus checked endpoint equivalence gives
   BranchGood with Sbar.
3. `entry_ok_good`: lookup_all provides the entry test; tsite_ipeq transports
   it to any Sbar representative and keeps the same branch successors.
4. `normalized_check_bisim`: combine the initial branch and all entry facts.

All lookup/decoder details belong ONLY in these finite front ends. The decoder
parameter must remain the actual decode215/fuel512 where required, not silently
revert to the legacy128 fuel. False or failed lookups must reject checks.

A balanced list/tree adapter, a new pointer codec or a changed batch layout then
proves lookup_all and its decoding facts, rather than re-proving halting.
Existing Lean RMBisim.WithDecoder.check_bisim/check_halts_iff already exemplify
this split. Audit the maintained RMNormalizedBisim adapter against that boundary
before changing it; do not assume its current implementation is the old packet.

## Cut validity is not semantic soundness

The Lean lookupC_all proof already works for ARBITRARY cut values. A successful
lookup follows one finite tree branch to a leaf, and allC checks every leaf.
Neither cut=size(left), balanced shape, flatten equivalence nor numeric index
surjectivity is required. Leaf lookup even ignores its residual index.

Therefore a self-contained checker can prove soundness directly from lookup_all.
Wrong cuts either cause a failed lookup, route to another entry whose branch
conditions still must pass, or expose a genuinely equivalent graph. None
invalidates soundness when initial and every reached branch are fully checked.

Cut validity IS still required if a theorem claims that tree lookup equals an
external list's nth_error, or if other clients interpret indices independently
of the checked table. Keep those obligations as optional representation/data
compatibility audits, not axioms or hidden assumptions of halting soundness.

`proposed/CheckedIndex.v` gives a standalone uncompiled Rocq prototype of the
exact structural lookup_all proof. Its wrong-cut example routes index0 to22
rather than flatten-list11, while all entries still satisfy the checked
predicate. This is an index-law counterexample, not a compiled source-machine
certificate. The retained semantic checks, not this example alone, justify
soundness. Actual balanced Rocq dependency removal must be checked against its
current source before claiming that production imports were removed.

## Concrete low-risk source patch

The graph bridge currently imports the entire NormalizedBisim checker merely
for ibeq/ibeq_ok/halts_ipeq. `proposed/PathEq.v` extracts the41-line existing path
utility block verbatim; `proposed/SourceGraphBridge.v` and the accompanying patch
change only that import and name qualification. The owned audit verifies the
utility text unchanged and the bridge edits reversible exactly. This decouples
graph adequacy from an unrelated certificate simulation/mirroring module.
It is source-checked, NOT newly compiler-checked. Integrating it requires module
mapping updates and rebuilding the original public clients and their assumptions.

## Dependency shape and trust

    RM / RMEquiv -> SegmentFacts + PathEq -> SemanticBisim
                                         -> checker adapters -> Source215
    PathEq + SegmentFacts -> SourceGraphBridge -> optional macro analysis

A subsequent cleanup can move segment facts out of historical Bisim230 so that
new adapters do not import the old checker implementation just to access lemmas.
Keep compatibility facades during migration so endpoint names do not change.

Rocq and Lean still each kernel-check their own theorem and concrete certificate.
Sharing an untrusted data generator or language-neutral table is useful, but
neither proof assistant trusts a Python result, a hash, the other assistant's
receipt or native execution. Use kernel-backed existing computation, print the
same final assumptions and run the established endpoint audits. No new axiom,
admit, theorem weakening or performance claim is proposed.

## Current-source confirmation and concrete next patch

The refreshed maintained Lean RMNormalizedBisim.lean already implements exactly
this saturation adapter: Rel at line75, branchOk_good at92, entryOk_good at114,
check_bisim at135 and check_halts_iff at157. It reuses RMBisim.Bisim.halts_iff and
lookupC_all without cut-validity hypotheses. Do not present this Lean component
as missing or as a new proposal. Lean is the reference architecture to reuse.

The inspected current Rocq proposal `NormalizedBalanced.v` does something
strictly heavier: ncheckTree_halts_iff requires `validb T = true`, converts via
ncheckTree_flatten, then invokes ncheck_one_sided_iff on flatten T. Its concrete
Source215NormalizedBalanced.v endpoint explicitly passes
`normalized_tree215_valid` before `normalized_balanced215_forward`.

After the semantic adapter above, replace that dependency chain with:

    ncheckTree_bisim : ncheckTree (ptree p1) (ptree p2) T = true ->
      Bisim (ptree p1) (ptree p2) (normalizedTreeRel T).
    ncheckTree_halts_iff_direct :
      ncheckTree (ptree p1) (ptree p2) T = true ->
      forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).

Then the source endpoint supplies only normalized_balanced215_forward. The
old theorem with its extra validity argument may remain as a compatibility
facade calling the direct theorem. Preserve the current concrete certificate
and branch checks. This is NOT achieved merely by deleting the validity
hypothesis from the old flatten proof: the direct semantic adapter is necessary.

`proposed/BalancedLookupSound.v` supplies the small structural lemma against the
actual Rocq API, whose leaf lookup checks residual index=0 (unlike Lean's leaf
lookup). That distinction does not affect lookup_allTree. It needs no valid,
validb, csize, flatten or lookup_flatten. The entire file is proposed uncompiled
proof text; no fresh assumptions output is claimed.

The old flattened-index lemmas and generated validity computation can leave
the source endpoint's proof dependency cone once the generic core and adapter
are integrated. They can remain optional tests of list-index compatibility.
This removes an unnecessary proof obligation, not any source-machine semantics
or trustworthy checking. No measured speed or net line reduction is asserted.

Copies of the specifically inspected sources are in inputs/, so the owned
`python audit_refactor.py` uses only paths relative to this packet and can run
without the original workspace. It executes no received source/build scripts.
The current maintained Rocq Source215 facade may still use the older offset
lane after merges; installing the normalized facade remains a separate audited
integration step, not something this proposal claims already happened.

## Further Lean shortening without another semantic theorem

There is also a small implementable Lean follow-on beyond its already-shared
semantic core. Parameterize the finite front end by an endpoint comparator:

    endpointEq : List Bool -> List Bool -> Bool
    endpointEq_sound : endpointEq P Q = true -> ipeq P Q.

Use the same saturated lookup relation for BOTH literal and normalized checking.
Instantiate endpointEq with RMBisim.lbeq (lbeq_ok then reflexivity gives ipeq),
or with RMNormalizedBisim.ibeq (ibeq_ok). Both instantiate the same branchOk,
entryOk, branchOk_good, entryOk_good and check_bisim definitions/proofs.
Their actual Boolean computations and successful certificates need not change.
The plain checker's semantic witness becomes slightly more general, but the
public all-register halting theorem remains identical.

This removes duplicated finite-checker adapter proofs, not another semantic
induction. The inspected literal entryOk_good is19 lines and normalized version
20 lines, with the same case split. The normalized branch proof differs mainly
in recording ipeq witnesses instead of substituting endpoint equality. Since
RMBisim already imports RMEquiv, this abstraction need not introduce a new
semantic dependency or a module cycle; place tsite_ipeq in the shared base.
Do not delete legacy public Rel/check_bisim declarations blindly: preserve old
facades if downstream clients use their exact relation rather than only the
halts theorem. This second-stage cleanup requires compiler-checked adapters
and existing-client rebuilds before asserting compatibility or net code savings.
