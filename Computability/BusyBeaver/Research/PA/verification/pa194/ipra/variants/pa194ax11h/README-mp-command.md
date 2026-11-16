# AX11H ordinary MP command, source-level stage

This stage checks the exact candidate-source execution from dispatch site 25 to
site 48, including both fresh and nonempty instruction-stream paths, followed by
the MP dispatch and the exact ordinary MP source command returning to site 25.
The proofs work for model-valued registers in every PRA model satisfying IΣ₁.
`PA194AX11HMPCommand.fresh` and `.positive` assume zero X/Y scratch registers
and decoded opcode 1, and identify the complete resulting register file.
`PA194AX11HMPPositive.fromFetch` supplies a strictly positive clock by using the
distinct site 25 and site 48 controls. A scheduler-frame equivalence is not
established by this stage.

Replay with `./check-mp-command.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT`, after
the `check-mp-source.sh` and paused-reader stages. The provider file contains
the ordered Lean search path of checked dependencies; this stage rebuilds all
eight listed modules from repository sources in one output directory and
rejects reports containing `sorryAx`.
