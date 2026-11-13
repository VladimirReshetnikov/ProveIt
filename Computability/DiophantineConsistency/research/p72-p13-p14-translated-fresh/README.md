# Fresh-project P13/P14 mapped translated consistency

This client checks the same two mapped Gödel–Gentzen corollary declarations
as the earlier captured-provider client, but imports P14 from the newly built
and independently audited 681-module current-source extension. Its source is
byte-identical to the captured version; consequently the source header says
“captured”, while the actual provider in this run is the fresh project build.
For each positive-shifted P13/P14 expression the theorem proves, in standard
iPRA, equivalence with `(Semiformula.lMap embedding sourceSentence)ᴺ` by
composing its checked mapped-refutation endpoint with `IPRABoundedRhoZFC.zfcEquiv`.

Actual outer session 81196 exited 0; dependency and compilation runs each
exited 0. Both explicit axiom reports in [compile.txt](attempt01/compile.txt)
contain exactly `propext`, `Classical.choice` and `Quot.sound`. The retained
[state](attempt01/state.json) SHA-256 is
`4ff660480d707567c0d2267087f038ecc5b0e3dd62b902238cdf27b687e61223`;
the output object SHA-256 is
`eaf40d67d9c83a790b2e1cfaada204b0d6d254f3e2eb8605a7b088d9f9e1d8c9`.
The source SHA-256 is
`324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a`;
the runner SHA-256 is
`cfdd0d172f518ba611dd28a4c5dbbe2b5c495c5f66a4cb0216d7af83ee9b5abc`.
The no-Lean preflight returned exit 0 in actual session 54218; it and the
postflight reran the independently reviewed 681-stage artifact checker.
They did not rerun that review's separate archive or 918-base checker.

The compile sampled peak session RSS 2,730,565,632 bytes and minimum host
available memory 18,970,660,864 bytes, with no stop, observed descendant or
monitor error. Limits are sampled; transient spikes, escaped descendants,
package-transitive and dynamic ancestry remain outside the guarantee. The
external JSON/byte and exact-degree checks remain separate; no Lean file
semantics or ZFC consistency decision is claimed.
