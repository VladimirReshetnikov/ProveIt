# Independent run2 readback

The saved six-library result is valid for its stated scope: 21 providers, six
fresh macro compilations and 15 exact-source reuses. The six fresh logs have no
warnings. The reused `TarskiComplete` log contains six previously accepted
warnings; the full smoke dependency set is therefore not warning-free. Source,
log and dependency-object hashes agree with the saved plan and receipts.

The unchanged `MacroSharing18Api` client passes with zero warnings. Its source
and complete compiler log are byte-identical to the accepted phase17 baseline
client, and all ten printed assumption profiles match exactly. It checks the
qualified `L2K.AS` type, positional construction, record updates, dot projections,
shared run contracts and the local rotated fetch cases.

The separate `MacroNamespace18Probe` fails with exit 1 at `L2K.AS.mk` and
`L2K.AS.np`; diagnostics print the aliased `L2.AS.mk` and `L2.AS.np` names. Its
two partial reports contain `sorryAx`, there is no accepted object, and these
reports are excluded from acceptance. The outer v2 runner consequently fails
its namespace-probe assertion and never writes `client-result.json`. Do not
present that runner as an overall all-probe pass.

This is the predicted namespace consequence of replacing the separate old
record with the shared `L2.AS` type. A fresh census of all four maintained roots
finds no constructor/projection/recursor spelling or old-AS namespace opener
that requires the retired generated names. I support documenting this explicit
compatibility change rather than adding unused wrappers. The evidence proves
the two concrete failures; it does not individually test every generated name.
The complete selected closure still needs its separate acceptance result.

The [readback](smoke-run2-readback.json) pins the evidence; the
[census](smoke-run2-caller-census.json) records current source scope. The original
prototype review remains unchanged. No compiler, generator or supplied script
was executed by this peer, and no canonical file was edited.
