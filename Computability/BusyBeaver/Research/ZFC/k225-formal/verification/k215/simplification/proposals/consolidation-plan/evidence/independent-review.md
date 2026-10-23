# Independent review of the Native Replacement and termination prototypes

Reviewed against ProveIt commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
This is a separate mathematical and source-integration review. No source was
modified and no additional compilation was performed for this review.

## Conclusion

No mathematical defect was found in the supplied Native Replacement proof or
the termination transport adapter. The Native Replacement refactor uses the
existing first-order collection interface without strengthening `QHyp`, and the
termination adapter explicitly discharges the source-deadlock issue. The
retained legacy APIs are supported by unchanged proof bodies and the completed
`build02` audit. The measured saving is a reduction in the selected endpoint's
source closure, not a reduction in total maintained source.

## Native Replacement: mathematical checks

1. **The domain guard is essential and correctly placed.**
   `ProfileCollection.lean:22-27` defines support as
   `mem y b -> exists x, r x y`, without requiring that this witness belong to
   the collection input domain. Consequently collection of the unguarded
   relation would not directly yield an exact image. In
   `KQ1ReplacementNative.lean:16-24`, the relation is explicitly
   `fun x y => mem x a and r x y`; the support witness therefore supplies
   `x in a`. For the reverse inclusion, coverage gives an output `z` in the
   collected set for the input `x`, and functionality identifies `z` with the
   requested output `y`. The proof needs only uniqueness on `a`, and assumes
   neither totality of `r` nor a choice function. Its use of equality transport
   has the correct orientation.

2. **The syntactic instance really is a `Form`.**
   `guardForm` and `sat_guardForm` at lines 27-40 insert the domain parameter
   using the environment `[x,y,a,parameters...]`. The original formula expects
   `[output,input,parameters...]`. The renaming `0 -> 1`, `1 -> 0`,
   `k+2 -> k+3` therefore supplies `[y,x,parameters...]`; the conjunct
   `fMem 0 2` states `x in a`. The existing `Sat_rename_relOf` theorem handles
   binding, so this is not an unchecked variable substitution.

3. **There is no semantic comprehension strengthening.**
   `replacement_of_collection` at lines 43-57 is conditional on collection
   for syntactically represented matrices. It applies that hypothesis to the
   single explicit `guardForm phi`, with environment `scons a env`.
   The generic semantic lemma `exact_image` is harmlessly conditional on its
   stated guarded instance. The final theorem at lines 60-68 obtains the
   syntactic collection interface from the unchanged
   `KQ1Collect.quotient_collection` (`KQ1Collect.lean:39`), which in turn uses
   the existing equality-free translation (`translated_instance`, line 30).
   The proof does not assume collection for arbitrary semantic relations.

4. **The existing quotient/choice footprint remains accurately described.**
   The completed native audit reports no axioms for `exact_image`, and
   `[propext]` for `sat_guardForm` and `replacement_of_collection`. The
   quotient theorem and generic endpoint retain
   `[propext, Classical.choice, Quot.sound]`, matching the existing quotient
   development. Thus this removes one route through the raw quotient
   Replacement proof; it does not remove quotient construction or classical
   choice from the complete endpoint.

## Split, API compatibility, and dependency measurements

Direct source comparison independently confirmed that:

- The body from `def Agree` through `ordinary_infinity_of_container` in the
  original `InductiveAttempts.lean` is unchanged in `InductiveAttemptsCore`.
- The three legacy CP/GIC specializations beginning with `quotientFiniteBase`
  are unchanged in the compatibility facade, in their original namespace.
- `KQ1ZF.lean` changes only two imports and the two references selecting the
  Replacement theorem. Its other declarations and `QHyp` are unchanged.
- The old `KQ1Replacement.lean` and `QuotientReplacement.lean` remain available.

`AuditLegacyReplacement` checks all nine old Replacement declarations and the
legacy infinity declarations. The proof equalities established by `rfl` in
that audit confirm that the native and old theorems inhabit the same proposition
type. Because Lean has proof irrelevance, these equalities should not be
described as equality of their internal proof constructions.

The `build02/receipt.json` reports PASS for 107 project modules and two audit
modules with Lean 4.32.0. Every recorded current source, source snapshot, and
log SHA-256 was independently recomputed and matched the receipt. Its legacy
audit contains the final infinity axiom reports. This build covers generic
`KEndpoint` and legacy compatibility; it does not compile the concrete K215
source/boot/site certificate closure.

Independently traversing imports from `KEndpoint215` with and without the
overlay reproduces every record in `closure-census.json`:

| Static selected-source closure | Baseline | Native overlay | Difference |
| --- | ---: | ---: | ---: |
| Modules | 174 | 173 | -1 |
| Bytes | 1,752,650 | 1,744,292 | -8,358 |
| Physical lines | 37,648 | 37,483 | -165 |

The removed closure members are `InductiveAttempts`, `KQ1Replacement`, and
`QuotientReplacement`; the added members are `InductiveAttemptsCore` and
`KQ1ReplacementNative`. This is a valid dependency cut, not a claim that the
legacy source can be deleted. Across the changed production-source set,
preserving the compatibility facade increases maintained source from 20,744
to 24,646 bytes and from 413 to 497 physical lines: **+3,902 bytes and +84
lines**. Audit modules and scripts are excluded from both figures.

## Termination transport and source deadlock

The generic theorem works for deterministic partial transition functions.
Its strengthened induction over all reachable suffixes of a terminating run
is sound: determinism aligns the first successors, and a `none` state has no
outgoing transition. Positive forward simulation therefore reflects
termination without a reverse simulation. Preservation additionally uses the
explicit finite drain from a source terminal. The strict `Reach1` condition
is used in the reflection argument and must remain.

The source adapter retains literal source halting. In the repository,
`RegisterPath.step` (`RegisterPath.lean:96`) can return `none` when decoding
fails, whereas `AtHalt` (line 108) requires a decoded `.halt`. The adapter's
`complete : step p c = none -> AtHalt p c`
(`TerminationTransportK.lean:54`) is consequently indispensable, and is used
both when translating source termination and when invoking the terminal
drain. The actual KSim patch supplies it via the existing
`sim_stop hcov` (`KSim.lean:295`). Inspection of `sim_stop` confirms that
coverage supplies a decoded instruction and rejects non-halting instruction
cases. The target-halt row condition `hNH` is still passed to `sim_halt`.

For incorporation, use `termination_transport_bundle/KSim.patch` and the
qualified module files under `lean/BusyBeaver/ZFC/`. The earlier loose
`termination_transport.patch` uses the scratch import
`import TerminationTransportK`; it is not the correctly located repository
patch. The bundle uses `import BusyBeaver.ZFC.TerminationTransportK` and its
adapter uses the correspondingly qualified generic-library import.

The review supports these prototypes within their stated scope. It does not
establish a fresh concrete K215 endpoint build, a new arithmetic-model
internalization, or a new ZFC calibration theorem.
