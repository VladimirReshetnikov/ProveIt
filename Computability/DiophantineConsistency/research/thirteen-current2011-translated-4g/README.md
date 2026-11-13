# Mapped translated consistency for the thirteen-variable forms

The client proves two standard iPRA biconditionals: the no-zero sentence of
positive-shifted `expressionAt70` or `expressionAt71` at the current port
tuple is equivalent to the mapped Gödel–Gentzen translation
`(Semiformula.lMap embedding sourceSentence)ᴺ` of the formal ZFC consistency
sentence. Each proof composes the checked standard mapped-refutation endpoint
with `IPRABoundedRhoZFC.zfcEquiv`. This is a Lean theorem about represented
formal derivability. The external graph/Lean source binding and exact degree
are separately reviewed; no Lean JSON parser is asserted.

Actual outer session 84256 exited 0; both nested Lean runs exited 0. The
[Lean output](attempt01/compile.txt) reports exactly `propext`,
`Classical.choice` and `Quot.sound` for each translated endpoint. The
[state](attempt01/state.json) SHA-256 is
`36fc9cef1a7a032b80464e293926d010c30fc526bc2c39146623d314bf879797`;
the client object SHA-256 is
`91f0f508a71fcc2a490414dac0b79602a6a23999d6fcc8585c49f46f91c726a7`.
The source SHA-256 is
`13234e68158103241a8d9d2a97bf4966b98065f9e121b7d586e16c4a3114be56`;
the runner SHA-256 is
`58195001697e6d2140cc57d36803f50cfd3785b7de5195f7251fb039c3d19a5b`.

The runner rechecks the authenticated Forms, completion and helper providers,
the standard axiom-report client, their outer-exit evidence, direct guards
and isolated links. Compilation ran 2.222 seconds, with peak sampled session
RSS 2,859,765,760 bytes and minimum sampled host available memory
18,835,726,336 bytes. No stop, descendant or monitor error was recorded.
The resource limits are sampled; transient spikes, escaped descendants and
complete dynamic/package-transitive ancestry remain outside scope.
