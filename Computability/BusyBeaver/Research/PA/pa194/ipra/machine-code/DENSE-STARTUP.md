# Literal PA194 blank startup

`PA194DenseStartupComplete.startup_exact` checks the exact literal dense
PA194 run for 58,154 steps from `⟨0, [], []⟩`. It reaches
`⟨24, PA194StartupData.seedFrame.l, PA194StartupData.seedFrame.r⟩`; the tape
is precisely the seed tape from the earlier unfolded-parent startup result.
The dense table is pinned by SHA-256
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.

The generator uses an untrusted Python simulation to propose 456 checkpoints.
Lean checks the 455 blocks with the proved `PA196.FastRun.checked` evaluator,
checks the final seed-tape equality, and composes the blocks. All 46 block
modules and the final composition were checked; `startup_exact` reports
`[propext]`. A separate portable replay also rebuilt all dense blocks and the
composition from regenerated sources, but stopped at the following bridge
step because its scratch source path needed an explicit Lean root. The
corrected full wrapper, including the native sentence, is being replayed.

`PA194ModelDenseStartup.modelDenseStartup` combines this finite literal run
with the standard-numeral bridge to obtain the corresponding equation in
every candidate PRA model. [`PA194StartupSentence.nativeIPRA`](STARTUP-SENTENCE.md)
expresses the same fixed startup as a closed equality derivable in native
iPRA, using binary terms for the clock and right tape. It uses a fixed
external standard time; it does
not prove the source controller simulation for arbitrary model-length runs,
blank-to-refutation equivalence, either iPRA consistency implication, or the
desired biconditional.

From the repository root, the full check can be run with:

```sh
PA194_STARTUP_OVERLAY=/path/to/audited-parent-startup-objects \
IPRA_MODEL_OVERLAY=/path/to/audited-pa194-model-objects \
IPRA_FOUNDATION_OVERLAY=/path/to/audited-foundation-objects \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-dense-startup.sh
```

The retained parent overlay must contain the audited parent source-program and
primitive-simulation objects and their transitive imports. The model overlay
must contain the audited standard-configuration and zipper-stepper objects,
and the Foundation overlay supplies their Foundation prerequisites. The
script verifies hashes of the named parent and model objects and of selected
source files; it does not rebuild every transitive object in those overlays.
It regenerates the dense and parent checkpoint sources, rebuilds the literal
machine, parent seed data, and fast evaluator, then rebuilds the dense blocks,
the composition, four model bridge modules, and the native iPRA startup sentence. This is not an all-from-source
replay of the retained overlays. `PA194_DENSE_JOBS` sets the number of parallel
Lean block checks (default 2).

For a shorter setup check, set `PA194_DENSE_CHECK_BLOCKS=1`; this checks the
first batch only and explicitly does not check the complete startup theorem or
its model lifting. Temporary outputs are placed under `/dev/shm` by default.
