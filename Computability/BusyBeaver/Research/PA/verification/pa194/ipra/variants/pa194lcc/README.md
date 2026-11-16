# PA194LC_C source simulation

The [delivered PA194LC_C table](../../../../../docs/pa194_loop_continuation_research_2026-11-14/machines/PA194LC_C/machine.tm)
has 194 working states and SHA-256
`7de80d804e5994db6008687421b0c5b4e96c9c87097fb293269406e9009a5753`.
Its delivered resolved instruction list is byte-identical to the primary
list of 3,673 instructions. The generator pins the delivered table, labels,
sites, and instruction list for both LC_C and LC. It verifies the compact
native-row override and shares 21 LC trie roots while adding 82 new nodes;
the generated Lean data is compared byte-for-byte with `PA194LCCData.lean`.

- `PA194LCCRows.rowAgreement` checks that the symbolic machine and its
  control labels match the literal dense table; `PA194LCCBoxAgreement`
  supplies its model-valued register operations.
- `PA194LCCModelStartup.modeledStartup` establishes that 58,320 steps from
  blank reach the common packed seed in every arithmetic `IΣ₁` model.
  `PA194LCCInitializer.startup_root` identifies the seed with the LC_C
  source root.
- The reusable `PA194TrieSourceController` proves the source simulation
  for a primary register layout and an arbitrary certified address trie.
  `PA194LCCController.halt_iff_controller` specializes it to LC_C.
- `PA194LCCNative.consistency_iff_literal_nonhalt` gives the iPRA
  consistency/nonhalting derivation conditional on the explicit
  `AllContracts data` premise. `PA194LCCFinal.consistency_iff_literal_nonhalt`
  supplies that premise from the checked finite coverage theorem and derives
  the unconditional iPRA equivalence. Its Lean axiom audit reports `propext`,
  `Classical.choice`, and `Quot.sound`.

The data, startup, conditional native, and complete 3,673-site coverage
stages have been source-replayed with staged dependencies. The repository
final theorem has also been checked against the coverage and native stages.

From the repository root, starting with a checked LC data stage produced by
`pa194lc/check.sh` (containing `PA194LCData.lean`, `PA194LCData.olean`, and
`leanpath.txt`), run:

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
lcc="$variants/pa194lcc"
bash "$lcc/check.sh" "$lc_base" /dev/shm/pa194lcc-data
bash "$lcc/check-startup.sh" /dev/shm/pa194lcc-data /dev/shm/pa194lcc-startup
bash "$lcc/check-controller.sh" /dev/shm/pa194lcc-startup /dev/shm/pa194lcc-controller
bash "$lcc/check-coverage.sh" /dev/shm/pa194lcc-controller /dev/shm/pa194lcc-coverage
```

Each output directory must be new. The startup replay kernel-checks 15
finite numerical chunks; the coverage replay checks all sites in 58 batches.
These scripts source-rebuild their listed modules and use the supplied staged
dependencies; they do not themselves rebuild the full dependency closure.

To combine a separately checked coverage stage with a newly checked controller
without rerunning the finite batches, use `check-final.sh CONTROLLER COVERAGE
NEW_OUTPUT`. It prioritizes the supplied controller when loading imports.
