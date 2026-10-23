# Checked left-frame contracts for K215

This packet completes the principal generic proof obligation in the existing
`round13-left-frame` proposal and checks all 35 of its local templates against
the maintained literal `KTableCore.tm215`. It also proves that each template's
Continue or Break action respects an arbitrary preserved path prefix. It adds
no machine transitions and changes no production proof file.

## Checked result

The fresh Lean 4.32.0 builds cover 14 distinct modules: three new modules and
11 exact vendored dependencies. No project objects are supplied. The accepted
build logs contain no `sorryAx`, no new axiom declaration, and no warning in the
three new modules. There is one inherited unused-simp-argument warning in KZip.

* `KLeftFrame.sstep_frame` proves that a safe symbolic step commutes with
  appending any symbolic left frame, preserving both failure and success and
  preserving the progress bit. The safety guard excludes a step that would read
  an exposed empty left side. `unsafe_boundary_counterexample` checks why the
  guard is necessary.
* `KLeftFrame.runLocal_sound` lifts a checked fixed-length local replay to any
  frame, gap parameter, and valid register file. It requires only ordinary
  `Reach`. `local_home_sound` composes it with the existing positive Home return.
* `KLeftFrame215.all_checked` kernel-checks all 35 literal bodies, totaling
  444 symbolic operations. `template_prefix` proves their exact whole-tape
  positive contracts for every admissible prefix, every natural gap parameter,
  and every valid register list. The box and Home assumptions for tm215 are
  discharged using the maintained `KTape` theorem and a finite Home-ready check.
* `KLeftFramePaths215.prefix_action` proves, for every one of the 35 listed
  source actions and every Boolean word P,
  `action(P ++ suffix) = P ++ result`. The suffixes contain enough delimiters;
  the Break carry never enters P. No fixed-prefix testing substitutes for this
  universal theorem.

The exact assumption reports are preserved in `evidence/`. `sstep_frame`,
`all_checked`, and `prefix_action` use `propext`; `runLocal_sound` uses `propext`
and `Quot.sound`; the positive semantic contract uses the standard Lean trio
`propext`, `Classical.choice`, and `Quot.sound`. These are component reports,
not a new report for the complete ZFC endpoint.

## Current-source finite audit

`audit_assignments.py` independently reads the pinned source list, maintained
formal table, and maintained decoder-role graph. It binds all 4,751 leaf ports,
then verifies all 1,422 inherited control-template uses: 1,326 Continue and 96
Break. It checks the source action, exact routed state, preserved suffix,
Home-prefix scan bound, and symbolic gap identity. It accepts 721 prefixes
ending in zero. Exactly three control guards remain literal: `001/CB1`,
`1000111/CC3`, and `11011/CB1`.

These assignments and their data are inherited from the existing proposal.
The fresh contribution is the kernel proof and exact template instantiation,
plus the arbitrary-prefix path-action theorem and a current-source audit.
The assignment audit remains a finite Python check. It is not an all-leaf
semantic-coverage theorem.

The proposed coverage decomposition is 35 template bodies, three literal
control guards, 1,900 increment guards, 2,850 decrement outcomes, and one halt
guard: 4,789 expensive executions versus 6,176. All 6,176 coverage instances
remain required. This 22.46% reduction in proposed execution obligations is
neither a measured endpoint build speedup nor a measured production source-size
reduction. The current component adds 19,351 bytes in its two runtime modules;
the separate action module supplies an additional small proof.

## What remains before endpoint adoption

1. Formally bind each of the 1,422 source occurrences to the checked template
   data and the exact maintained `RoutedEntry` theorem.
2. Formalize the remaining symbolic right-endpoint normalization and gap
   reparameterization in the semantic leaf contract. For a source path Q of
   length at most 48, use local gap parameter `n + 48 - |Q|`; this makes its
   `n' + 16` gap equal to the current `n + 64 - |Q|` gap. The finite audit checks
   the exact suffix-length change at every occurrence.
3. Compose decoder entry, the checked local template, and Home, using the
   Source193 semantic coverage interface. Retain literal residual proofs for
   the remaining outcomes. Source193 already supplied a checked all-residual
   component; this packet does not claim that earlier result as new.
4. Rebuild all affected consumers and both endpoint audit clients, preserving
   the literal table/source hashes and endpoint assumption profiles. This
   packet does not rebuild the ZFC endpoint, provide an internal PA/ZFC proof,
   or certify an alternative 215-state machine.

## Offline component reproduction

Use Lean 4.32.0 (the accepted release commit is
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`). The compiler and its standard library
are the only external build requirements. Both output directories must be new.

```sh
python3 build.py --lean /path/to/lean --out /tmp/k215-left-frame-runtime
python3 build.py --lean /path/to/lean --out /tmp/k215-left-frame-paths \
  --target BusyBeaver.ZFC.KLeftFramePaths215
```

The driver uses the eleven files under `vendor/`, takes a shared compiler lock
for each compiler invocation, and creates source, imported-object, output-object,
and log hashes. Its recorded elapsed time includes lock waits and must not be
interpreted as pure compiler CPU time. The accepted receipts are in
`evidence/runtime/` and `evidence/paths/`; the summary binds the exact executed
driver. A first rejected attempt is retained under `evidence/history/build01/`:
it used the unavailable lemma name `List.reverse_map`, corrected to
`List.map_reverse`. Its failed output is not part of the accepted proof.

For regeneration and the current-source assignment audit, supply a checkout of
ProveIt commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`:

```sh
python3 generate_templates.py --repo /path/to/ProveIt
python3 audit_assignments.py --repo /path/to/ProveIt
```

The generator verifies the inherited formal-template input hash and reproduces
the checked template and action sources exactly. The generated data is
untrusted: the Lean equations prove the replay and path-action claims. The
finite Python audit is a distinct integration diagnostic.

## Attribution and provenance

All source inputs are pinned in `vendor_manifest.json`, the build receipts,
and `assignment_audit.json`. The inherited 35-template discovery is in
`k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime/`.
The packet supplies the proof that its earlier uncompiled proposal requested.
Dependency headers retain their attribution to the ProveIt contributors,
Elliot Glazer's k230-rocq, Jeff Ketchersid's m254 verification, and Wade's machine
framework. See the inherited license and notice files supplied with the parent
archive. No claim of original discovery of the 35 templates is made.
