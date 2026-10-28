# Adaptive four-factor unit extraction: author record

26 October 2026. Root authored and fully read the73-line main,28-line
checks and complete private driver before execution. Both first fresh
Lean4.32 builds pass4.566s/2.655s, with empty main and five standard-only
axiom reports. No failed source or driver attempt occurred in this packet.
Independent review is separate.

The four displayed functions are the literal adaptive cuts 1+A0,1+A1,
Fs and Fa, with Z,N,U,a,c,D,f,I,V,y supplied as arbitrary signed integers.
For each factor, cast a hypothetical negative unit into ZMod4 and reject
it by a finite kernel-checked `decide` computation. No native_decide or
external computation oracle is used. The multiplier q^3(q-1) and the
actual discriminant a^2+4a+3 are retained exactly. An integer product1
therefore forces each of its four factors to1, in both directions.

No factor positivity is assumed: the focused control permits zero and
negative factor values, and another supplies an actual all-unit tuple.
These are generic factor tests, not complete thirteen-input equation
zeros. The proof supplies upstream unit extraction before the separate
A0/A1 bootstrap. It does not bind all88 historical graph rows, prove a
new metric, identify a positive source, or assert an HA/consistency endpoint.

Main b9bc1883c478f5e236c32b7d06ab4d132a80b3fd55e317df0650e55c497447cb;
checks4ba76919056b926309c3a914b54c4a488bdc363775eacfdc6e4b6774e672ec98.
Objects50287a90e3309ce90c28cfa0eaca01683cee972e9cdfc10909cb25602ec80b3c
and48d8578042c2536945b0e5457f7101fa22bac0aa4f0e95953e0ee9459459eea2.
[Replay](native-adaptive-unit-factors-replay.json) SHA
be118b13e49d8c55ddeab16b010a973c99280264297ed2f11d6736ba07edd2de;
[nine-file manifest](native-adaptive-unit-factors-replay/FILES.json) SHA
21d6536806d37a6a31cf8eabb38fa1c3c4b8832a0fdb6cf3476af3a201396553.

Private output `/tmp/native-adaptive-unit-factors-root-author-dnx06vax/lib`.
The sole import is NativePellBootstrap. All25 cached current-source custom
modules,22 explicit external boundaries,66 companions and1523 inherited/
explicit observations reauthenticate before/after. Only two leaves are
fresh; no Foundation/dependency build, source/cached-object overwrite or
resource increase. Commands use -M6000 -j1 -DElab.async=false, regular
nonsymlink outputs and512MiB disk guard. The earlier factor-three packet's
precompiler errors are not repeated or counted as failures of this packet.
