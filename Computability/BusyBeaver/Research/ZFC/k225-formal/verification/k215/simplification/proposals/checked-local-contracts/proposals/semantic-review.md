# Review of framed residual contracts

Repository baseline: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Main conclusion

The guarded left-frame proposal is mathematically sound with its explicit guard,
whole-configuration endpoints, and separate terminal Home theorem.  It is a useful
next increment because production `KSim.Covered` still requires literal Boolean
`checkEdge` success, whereas the already checked decoder-prefix and residual
proposals expose semantic contracts.  A semantic endpoint adapter must accompany
the factoring; reachability alone does not prove that a fuel-4000 executor accepts.

The expected 6,176 -> 4,789 expensive execution obligations is a candidate finite
obligation count, not a reduction in the number of source leaves, an endpoint
proof size measurement, or a measured wall-clock speedup.  There are still 4,751
leaves and 6,176 branch outcomes.  The 1,422 shared control occurrences need exact
source-action, routing, frame, and gap bindings.

## Checked reasoning about the proposed boundary

1. Let `addLeft F (q,onl,l,r)=(q,onl,l++F,r)`.  The syntactic one-step equality
   commutes with this extension for every successful `sstep` except the case
   `onl=true,l=[]`.  In that case, the original interpreter reorients using an
   implicit blank; the extended interpreter instead reads the first frame cell.
   Consequently a guard must be checked before every replay step.  It need not
   hold at the final state, since no local step is then taken.

2. The symbolic `run` segments may have length zero, and symbolic reorientation
   may take zero physical steps.  The local framed replay should promise `Reach`,
   not infer `Reach1` merely from its positive symbolic step count.

3. All selected local bodies end at `(2,true,[],R')`.  Appending
   `F=P.reverse.map Seg.bit ++ [Seg.bit true]` gives the full preserved prefix and
   its marker.  `KHome.scanBound_sound` and `KHome.home_word` finish the return
   with `Reach1`.  Thus the existing positive final boundary supplies the
   progress needed by reverse halting transport.  Decoder `Reach`, local `Reach`,
   and Home `Reach1` compose to a positive source-step simulation.

4. The Home contract assumes the standard blank exterior beyond the marker.
   It does not quantify over an arbitrary nonblank far-left tape.  Arbitrary
   source prefix `P` is allowed only when the existing `scanBound` check accepts.
   For literal bit prefixes this excludes eight consecutive zeros.  There is no
   requirement that the final bit of `P` be one; prefixes ending in zero are valid.

5. `KDecoderPrefix215.leafPort` retains the complete consumed source prefix.
   If the full word is `P ++ S`, its left side is
   `reverse(init S) ++ reverse P ++ [true]`.  A local suffix contract may frame
   `reverse P ++ [true]`, but must never replace the entire leaf port with a short
   suffix or identify ports merely because their physical states coincide.
   `RoutedEntry` and its exact consumed word determine the port.

6. `normL` trims trailing blank segments, which is sound only at the outer blank
   boundary.  Before adding a nonblank frame it is not congruent: `[]` and
   `[Seg.bit false]` have equal `normL`, but appending `[Seg.bit true]` produces
   different tapes `[true]` and `[false,true]`.  Therefore use exact local
   configuration equality, or full `norm` on the right endpoint.  Do not lift an
   unframed `sMatches` equality through `addLeft`.

7. Source path arithmetic must also preserve `P`.  For `continue k`, stripping
   must consume its k matching bits entirely within `S`.  For `break k`, the
   corresponding stripping and subsequent increment must both remain inside
   `S`; a carry into `P` violates the contract.  `PathFrame.lean` supplies partial
   local checkers whose successful finite result entails this universal theorem.
   This avoids relying on matching a few concrete prefixes.

8. The templates use gap `n'+16`.  The production leaf has gap
   `n+(64-|word|)`, where `|word|<=48`.  Instantiate
   `n'=n+(48-|word|)`; then `n'+16=n+(64-|word|)`.
   After a control operation preserving the prefix, the gap grows by
   `|S|-|E|`.  Prove the equality in naturals with its length premises;
   unrestricted subtraction cancellation is not valid.

9. The native table's state labels are not the maintained Lean labels.  The
   recorded translation is `301->102`, `302->120`, and halt `254->230`.
   Native state 302 occurs in the selected local traces.  The formal template
   data, not an unchanged native trace, must be checked against `tm215`.

## Current production seams

- `KRuntimeCore.lean`: `sstep` is the original symbolic stepper;
  `sstep_sound` justifies each local step against every valid register file.
- `KRuntimeCore.lean`: `normL` at line 491 and `sMatches` at line 496 explain
  why only complete configurations can use the existing trimmed-left match.
- `KHome.lean`: `home_word` line 42, `scanBound` line 72,
  `scanBound_sound` line 83, `home_sound` line 211.
- `KDecoderPrefix215.lean`: `leafPort` line 13, `entry_run` line 109,
  `entry_uniform` line 152, `leaf_prefix` line 171, `walk_prefix` line 185.
- `KSim.lean`: `Covered` line 182 still packages Boolean `checkEdge` success;
  `sim_step` line 218, `sim_stop` line 295, `sim_halt` line 303, and
  `halts_iff` line 316 consume that package.
- `SiteCoverage.lean`: its Boolean checker rejects `.none` branches and its
  totality theorem is essential.  A new semantic coverage checker must retain
  that totality and the exact consumed-path relation, including implicit zero
  padding.  The state `step p c=none` alone is not a source halt: it can also mean
  decoder exhaustion.  Preserve `sim_stop` or its equivalent completeness proof.

## Endpoint migration recommendation

Use the existing semantic-coverage proposal as the API migration basis:
`RunToSpec` is universal positive reachability, `HaltPortSpec` reaches the
designated halt port, `EdgeSpec` retains bounds and the two decrement branches,
and `SemanticCovered` retains exact walk results and all source paths.  The old
Boolean checker is one supplier via `edgeSpec_of_checkEdge`; the new framed
control contracts are another.  Preserve the old public wrappers.  Keep explicit
terminal-row evidence until converting a halt port into actual halting.

This extraction has a local source cost (the archived semantic-coverage packet
reports KSim 356 -> 485 lines).  Its benefit is enabling the factoring, not that
the API extraction by itself shortens source.  After integrating all occurrence
bindings, rebuild the exact literal-machine endpoint and compare the complete
selected dependency closure, producer source, and kernel timing with baseline.

An even narrower endpoint-only seam is provided by `KEndpointPort.patch`:
`blank_halts_iff_c222_of_port` accepts a checked port theorem
`KZip.Halts M T <-> KCode222.C222 Code254.F`, and the new
`blank_halts_iff_zfc_refutation_of_port` composes it with the unchanged
calibration.  The original Boolean endpoint is a wrapper that supplies
`(KSim.halts_iff ...).symm.trans hsrc`.  A semantic residual theorem can supply
the same port directly.  This preserves the old endpoint declarations while
removing certificate-producer choice from endpoint composition.  The patch
applies cleanly to the pinned repository, but has not been compiled against its
full endpoint closure.  KEndpoint grows from 81 to 102 physical lines; this API
seam is enabling work, not a claimed source-length saving by itself.

## Provenance and scope

The 35-template strategy, 1,422 occurrence assignments, three literal fallback
controls, and 4,789 candidate count are already proposed in the repository's
`round13-left-frame` packet.  They must be credited as existing work.  New work in
this delivery is any successfully compiled universal frame/action lemma and
closed template checks recorded by the current build, not rediscovery of those
counts.  A checked primitive/contract library is still distinct from an adopted,
freshly rebuilt 215-state Con(ZFC) endpoint.
