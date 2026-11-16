# Pinned PA194 source halt site

`PA194SourceHaltSite.lean` kernel-checks three concrete facts: source-tree site 10 is the explicit halt leaf at path `[false,false,true]`, that leaf resolves to the source `.halt` instruction, and the complete 3,673-leaf source list contains exactly one explicit halt leaf. All three theorem axiom reports are `[propext]`. This establishes neither that malformed/root-exit behavior is an explicit halt nor that any scheduler hit reaches the site.

The adjacent checked scheduler results have a different scope. `PA194ModelFairness.haltAt_iff` characterizes the modeled scheduler's halt bit as SHIFT with decoded top plus cache equal to 1. `PA194FetchCommand.parsed_command_halts` supplies a standard-natural source execution from a site-25 command frame to source halt in the corresponding parsed SHIFT case; `PA194SchedulerStandard.advance_standard` links the coded scheduler to the standard command operation. These facts are not rebuilt by this checker and do not constitute an all-model, model-length physical/source/scheduler correspondence.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-source-halt-site.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The replay pins the halt certificate, generator, and source-program module; regenerates the source tree after checking the packet's source grammar and upstream source hashes; and recompiles all three modules in a fresh common output. It additionally verifies that the packet's literal table has SHA-256 `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`. These matching packet inputs do not themselves prove that the physical table implements the source tree; that is a distinct simulation obligation. The replay checks named artifact hashes and `sorryAx`, but retains its upstream, machine, project, and package foundations as prebuilt dependencies: it is not a fully self-contained source build.
