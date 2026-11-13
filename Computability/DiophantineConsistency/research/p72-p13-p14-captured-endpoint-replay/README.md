# Captured-provider P13 and P14 endpoint replay

This run compiles the exact current `Compact44/IPRAOrdinary72.lean` and
`Compact44/IPRAOrdinary72P14.lean` sources in order over a private overlay of
the independently audited captured P64/P65 provider. P13 is the package's
13-positive, 98-operation degree-28 equation; P14 adds a positive `E`, the
constraint `E=XY`, and a square, yielding 14-positive, 101-operation degree 24.
Both sources prove a positive-model bridge and native, standard and
equality-only iPRA biconditionals against mapped native ZFC refutation. The
recorded degree and JSON/port bindings are external to Lean.

Actual outer session 51877 exited 0; both `--deps` and compilation runs
exited 0 for each module, with no guard stop or sampled descendant. Each
endpoint's explicit axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. The retained [state](attempt01/state.json) SHA-256 is
`69b125385c7eff4a1ae2efcde94f777e16c591fb281b07e0132500173f9df2aa`.
The P13 object SHA-256 is
`d667e5803d918e9211c170e55a03d56d8b62b42f43b152d8ab526905ae26a3b3`;
the P14 object SHA-256 is
`3c47dcbbd39cbb2f89092e40d747366589cc618da7bdf9765016554d65e82468`.
The runner SHA-256 is
`0459eb2c455a9ce452468bf0189d406fb9523eae556a4dc2eacacc219c4fd235`.
Its private overlay has 2,217 inherited links and records direct-object and
companion guards. The P13/P14 compile peaks were 2,675,404,800 and
2,713,772,032 sampled RSS bytes, with 18,808,668,160 and 18,828,644,352
minimum sampled host-available bytes respectively.

The original generators were rerun on the current source: the [P13](p13-binding.txt)
and [P14](p14-binding.txt) gate blocks match the pinned 98- and 101-gate JSON
files and the six derived leaf recipes. For P13, the actual loaded P72Graph
object is inherited. A separate read-only [producer check](graph-producer-result.json)
rechecks the prior P65 receipt, canonical source, exact import-only shim,
object and successful log hashes, and confirms that object is the captured
provider's object. This is a recorded source/object link, not a Lean theorem
that parses the JSON or gzip payloads. Exact degree is the package's claim;
no new degree proof is made here.

This is **not a fresh current-base closure**: the inherited compact provider
has incomplete transitive/package and dynamic ancestry. The resource guards
sample a 5-GiB session RSS threshold and 10-GiB host floor with a 180-second
timeout and Lean `-M4000`; transient spikes, escaped descendants and forced
supervisor termination remain outside the guarantee. The maintained equation
PDF has not been changed.
