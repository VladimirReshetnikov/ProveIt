# Next control lead: exact dispatch-to-framed-port composition

**Future uncompiled source-only lead.** This is separate from phase23 acceptance.
No canonical source, producer, certificate or machine is edited. No Lean, supplied
program, producer or checker was run. No state, runtime or net maintenance saving
is claimed.

The smallest useful missing lemma is `dispatch_to_framed_port` in the accompanying
33-line owned sketch. It identifies the current decoder's exact symbolic port
with the framed caller's complete-word physical port. This is an actual dispatch
prefix proof, not transition-table extensionality and not a residual run merely
renamed as a full edge contract. Its syntax and simplifier steps remain untested.

## Exact sources already available

| Obligation | Actual source theorem or definition |
|---|---|
| Uniform dispatch prefix on the full source word | Current `KDecoderPrefix215.leaf_prefix`; arbitrary `n` and `vs`, with no validity premise |
| Prefix's exact physical tape | Current `KDecoderPrefix215.conc_leafPort` |
| Actual role path and final primitive row | Current `DecoderPaths.RoutedEntry`, returned by `leaf_prefix` |
| Checked caller port matches that route | Packet `KFrameContracts.portState_of_path` and `KFrameCallers.caller_bindings` |
| Positive residual from the complete port | Packet `KFrameCallers.all_caller_standard hc n hv` |
| Compose a possibly zero-step prefix with positive residual | Current `KZip.Reach.trans_reach1` |
| Final symbolic target's exact tape and gap | Current `KSim.conc_target` |
| Domain of source framing and break carry | Packet `Shape.sourceGuard`, `KPathFrame.stripPath_append` |

The sketch takes `LeafAt t215 word e` and the caller's exact
`portState roles 0 word.dropLast = some q`. Unpacking the returned RoutedEntry
and applying `portState_of_path` identifies its state with `q` along the entire
word's role path. The equality `word = pre ++ [bit]` then identifies both physical
ports, retaining the final primitive bit, the leading marker, every preceding
source bit, and exactly `n + (64 - word.length)` blanks. Only Reach is required
for the prefix; all_caller_standard supplies positive progress after composition.

This adapter needs current KDecoderPrefix215 plus the packet's FrameContracts,
not FrameCallers or any old site batches. The current prefix closure contains
23 project modules and no KSites215 batches, source-forward batches, boot chunks
or KSource215Data. FrameContracts would still need its pinned template/engine
closure adopted and checked; it is not currently a canonical import. The new
lemma belongs at that actual producer seam, not in a facade that reexports the
old full certificate stack.

## Small next producer after this lemma

For a caller `c` in the existing caller list, let `m := metaAt c.templateIndex`.
The exact remaining dispatch contract is:

```lean
c.word.length ≤ 48 ∧
  ∀ n vs, Valid none vs →
    Reach1 tm215 (conc n vs (KSim.start c.word))
      (conc n vs (KSim.tgtConf (sourceResult m c.word) false (.plain .none)))
```

Instantiate the source walk from `(caller_bindings hc).1`, obtain LeafAt via the
current `walk_root`/`twalk_leafAt` correspondence, and simplify
`consume c.word c.word.length = c.word`. Supply `(caller_bindings hc).2` to the
new prefix adapter. Compose with `(all_caller_standard hc n hv).2` using
`Reach.trans_reach1`. The length bound is `(caller_ok hc).2.1`.

For continue, `sourceResult` is `continuePath` and overflow is false by definition.
For break, extract `sourceGuard` from `shape_of_index (index_valid hc)` and
`c.word = c.prefix ++ m.suffix` from `caller_ok hc`. The guard gives both
`m.argument ≤ m.suffix.count false` and
`false ∈ stripPath false m.argument m.suffix`. Apply
`stripPath_append false c.prefix m.suffix m.argument` to put that false bit in the
full stripped word. Thus `KSim.allOnes (stripPath false m.argument c.word) = false`.
This overflow proof is essential: the residual's no-overflow output gap otherwise
does not match KSim.tgtConf. Rewrite `conc_target`, growth of plain-none and
boxList to finish. Case splitting m.isBreak then gives exactly the two control
branches of the proposed EdgeContract, with no totality or extra machine premise.

This is a precise instantiation plan, not a completed full caller EdgeContract.
Current KSim has no RunContract, EdgeContract or SemanticCovered declaration.
The archived semantic consumer provides those interfaces and a mixed-sites fold;
it must be narrowly rebased against current KSim before the pilot's explicit
`C` can become exactly `KSim.EdgeContract tm215`. Current `runTo_sound` remains
an alternative literal producer only when the old runTo Boolean premise is
available; semantic reachability does not establish old fixed-4000-fuel acceptance.

## Keep table transfer and fallback separate

Current `KFastSites215.fast_eq : fastOf tt215 = tm215` is only all-state transition
function equality. `allSites_of_fast` transports the current literal checkEdge
predicate; neither theorem proves dispatch-to-port reachability or primitive
semantics. They cannot discharge the producer above.

The complete actual maintained `generate_sites215_lean.py` was read as inert
source. It emits each allSites(checkEdge tm215) block through
`allSites_of_fast (by decide +kernel)`, joins the same 105 subtrees, and uses
covered_of_allSites. It emits no EdgeContract or primitive-port lemma. A future
mixed fallback producer should retain those subtree boundaries and define
`literalGateFor M Q e := if isControl e && !literalControl Q e then true else
KSim.checkEdge M Q e`. Its block proof may rewrite with
`← KFastSites215.fast_eq` and then use `decide +kernel` on the new gate. The old
allSites_of_fast is specific to checkEdge and is not itself a gate adapter.
The producer is not among phase23's mandatory current-input pins; any future
adaptation must freeze its bytes explicitly rather than inheriting acceptance.

The published three-module classifier remains uncompiled: ordered caller-row
equality, walk-to-full-consumed-word classification, and the complete fallback
gate must all be checked. Retain failed decoder branches, both decrement guards,
increments, the two exact literal control exceptions, halt and all source-outcome
bindings. `literalGate_of_old_sites` is a useful initial compatibility check but
keeps old certificates and cannot establish a reduction. No producer or fallback
batch is changed in this lead.
