# Independent review of the checked left-frame prototype

Reviewed against ProveIt commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. This is a source review and independent finite-data audit, not a second execution of the proof assistants. Compiler results and axiom reports are supplied separately by the implementation workstream.

## Result

No logical defect was found in the statements or guards of the four new Lean modules listed below. The implemented statements have the right scope to become reusable control-edge contracts. They do not yet replace the maintained endpoint's Boolean coverage premise.

| File | SHA-256 of reviewed source |
|---|---|
| `KLeftFrame.lean` | `e32b6d4805453a542691d2b47cfe54d8b52f54bf39f98cf80aa7779a883a5d6c` |
| `KLeftFrame215.lean` | `4f721af887542f4deaedbdaa26443b665908a2dbabe91e987955e6d3558b3a76` |
| `KControlFrame.lean` | `3e95cc2baf162386a73690f19c70006603741cdb0a24aab3cf28bc8e51525133` |
| `KFramedControl215.lean` | `93e0abd472dbd7326445a9e399c018748e9b9f53a0707cc1cf58b79e5f316a81` |

## Guard and tape model

`sstep_natural` proves the full option-valued equality under `safeLeft`, including failure. The necessary excluded case is exactly an active empty left list. That branch supplies an implicit blank; after appending a nonempty frame the same branch instead reads the frame. The explicit `unsafe_frame_counterexample` uses a transitionless table, so this failure cannot be repaired by assumptions about the particular machine.

The guard is checked before every symbolic step. A local run may finish at `(2, true, [], R)` without testing the guard at that final configuration. This is intentional: Home then consumes the caller prefix. The run proof needs only reflexive reachability; Home supplies strict progress. There is no need to trust an accumulated local `moved` flag.

Framing is on the raw segment list, before any left normalization or trimming. This matters because exterior blanks become interior cells after a frame is appended. For example, a left list containing one zero and an empty left list can denote the same infinite blank exterior before framing, but appending a marker puts that marker at different distances. The prototype normalizes only the resulting right list when comparing template outputs, which is sound under the maintained `flatT_norm` theorem.

`home_prefix` permits every prefix accepted by `KHome.scanBound`; it does not require a prefix to end in one. Its marker and far-left blank assumptions are explicit in the configuration. The finite assignment census includes 721 prefixes ending in zero, so adding an unnecessary end-bit restriction would lose many intended instances.

## Source actions and exact endpoints

`KControlFrame.stripChecked` rejects underflow and `incChecked` rejects carry escaping the suffix. The append lemmas establish equations with the maintained `stripRev` and `incRev`, and the final theorem mentions the maintained `RegisterPath.execute`. The new definitions therefore certify the existing source semantics rather than silently replacing them with a more convenient arithmetic convention.

`KFramedControl215.aligned` checks the exact local start, equality of normalized right outputs, the exact source action result, output length, and a nonempty suffix. Its `aligned_contract` combines the runtime and source-action sides. The tape contract retains the marker, entire register box, and the gap adjustment. The only arithmetic precondition used to rearrange natural subtraction is the checked result-length bound. All registers are unchanged in this control-only contract.

The 35 finite runtime checks use the actual maintained `tm215` and ordinary `decide`. The 35 descriptor checks bind those templates to precise suffixes and source actions. These are stronger claims than merely replaying a separate Python interpreter. The independent Python audit complements them by identifying the same rows, actions, and 1,422 source uses in the pinned repository data.

One documentation refinement is advisable: “routed state” in the header of `KFramedControl215` currently means the numerical runtime start state in the descriptor. The module itself does not establish `DecoderCertificate.RoutedEntry` for the 1,422 callers. Use “entry state” there, or clarify that actual decoder routing is a later coverage-binding obligation.

## Endpoint integration remains a separate proof

The current `KSim.Covered` premise is a Boolean equation for the original bounded checker. A semantic `Reach1` theorem does not imply that old Boolean checker succeeds: the checker may have a different fuel bound or a deliberately incomplete normalization procedure. Consequently, the prototype must be consumed by a semantic coverage interface, or by a new checker branch with its own soundness theorem. It cannot simply be substituted into the old `Covered` theorem.

The least disruptive route is the already proposed `EdgeSpec`/`SemanticCovered` consumer: retain the existing checker's soundness theorem for unchanged edges; use the framed contracts for the 1,422 control uses; then prove coverage of every actual source leaf and branch. Use the maintained prefix/decoder theorem to reach the correct primitive port, bind the state, source action, and suffix decomposition, instantiate the frame contract, rebase the gap parameter, and compose executions. A state number alone is not a proof of the caller's decoder role.

The independent audit finds 6,176 original guarded outcomes. Replacing 1,422 control replays by 35 reusable local bodies leaves a projected 4,789 expensive bodies: 1,900 increment cases, 2,850 decrement cases, three exceptional controls, one halt, and 35 templates. All 6,176 source-outcome bindings still require coverage. The 22.46% reduction is a count of distinct expensive certificates, not a demonstrated 22.46% decrease in source size, kernel time, or endpoint closure size.

## Reproducibility and provenance

`audit_left_frames.py` independently parses the current source DAG, decoder roles, formal table, native table, and earlier template-discovery JSON. It checks all 4,751 source leaves, all 430 transition actions, all 444 saved symbolic steps, all 1,422 frame assignments, and the exact three exceptional controls. It also checks equality with the 430 effective transitions of the current Rocq `Table230.v`/`TM230.v` pair. It imports no repository Python and makes no proof-kernel claim.

The earlier round13 discovery and uncompiled contract proposal are prior work. The reusable mathematical idea and the template census should be credited to that packet. The new contribution is completing and checking the generic theorem, checking the real literal templates, and binding those templates to the maintained source actions and exact whole-tape endpoints.

The four new files depend on six copied maintained Lean files, all byte-identical to the pinned repository. `provenance_review.json` records their upstream paths, hashes, byte counts, and relevant notices. Preserve the repository's inherited-source license scope; its MIT No Attribution license does not retroactively assign a license to all inherited proof developments.

## Baseline measurement

An independent import-graph walk from the maintained endpoint confirms 174 local modules, 1,752,650 bytes, and 37,648 lines, with only `Init` outside the selected source roots. The result agrees with the maintained build driver's inventory. Historical phase15 receipts describe a different 176-module source snapshot. The present closure removes `Code254Models`, `KCodeDom`, `KIndisc222`, and `KSeedModel222`, and adds `KSeedDirect222` and `KSeedInterface222`; 91 common module hashes also differ. These differences are not explained by line endings. Keep the current source measurement and historical successful rebuild receipt separate.
