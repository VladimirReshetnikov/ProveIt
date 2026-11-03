# Expanded compact/iPRA rebuild: stage 251 exact-warning retry

The rejected attempt emitted one `unnecessarySimpa` style warning. This retry
preserves the source and theorem interfaces and accepts only its complete,
source-pinned warning after path normalization. Mutation checks reject added,
missing and altered warnings; the baseline has no `error:` or `sorryAx`.
This warning exception is not an independent proof audit.

The runner rechecked the 425 source pins, selected overlay, prior receipts,
earlier exact warning baselines, and the rejected direct dependency guards. It
quarantined the rejected object, rebuilt the unchanged source, and validated
the full exact warning. Lean exited 0 in 3.371 seconds, direct guards remained
unchanged, and final wrapper checks passed at 251/425. The accepted and
quarantined object hashes both are
`b05e062b607425f9a3c651ac90d83b7be037384014a0b1553703b8dc3d6f47b2`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `e1c20c8e6fd34954be933250ff9e10dab7bf4f55e6edf4e8fcf217257da061b3`,
`77ab18510309dba5dc5bdfb258ed6bff1988bbd625d8b49e86aa5013b9b3169e`,
`8ada12747e090fa5db22e1b507bc35b463d3247b03d418868a593128b191a32c`,
`3a02a2e3941d6e5019aaf5939aaa5f320e0a5ec23f2f2e7c8cd76f7a38cdcd37`, and
`d201134eb523fb09439440b620dc33fbb12b416e66d5f18982d4c1f5df75d2b7`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring saw at most one Lean child and minimum sampled
MemAvailable 18,505,324 KiB; brief children or overlap can be missed between
samples. This author prefix is not an iPRA endpoint, independent replay, or
complete provider audit. 174 stages and the compact model-to-iPRA join remain;
package and dynamic ancestry are not authenticated.
