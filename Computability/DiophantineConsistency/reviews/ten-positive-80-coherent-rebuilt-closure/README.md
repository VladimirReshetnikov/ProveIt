# Actual serialized closure of the rebuilt 80 iPRA union

After the v6 127-stage replay completed with internal PASS and captured outer
exit 0, `scan.py` read the actual serialized direct-import headers of every
selected project object in its fresh single union, in 28 guarded Lean batches.
All 1,765 headers match the expected captured imports. Traversal from
`Direct80SymbolicFixedIPRA` reaches exactly those 1,765 project names and 80
outside names. The scan also checks selected project and outside object and
companion presence and hashes against the replay's initial or rebuilt
baselines before and after the header reads. It refuses shadowed outside
names in the project union and missing, repeated or malformed header records.

The result is `observations/attempt01/result.json`, SHA-256
`75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276`.
It records every path, companion hash, direct header and batch command, plus
per-batch preflight and postflight resource samples. Each launch required at
least 8 GiB available and fewer than two existing Lean processes; point samples
do not prove resource availability between samples. The scanner exited 0 in
the observed tool result; no separate outer-process terminal receipt was
created. The paths refer to temporary providers and may not persist.

This strengthens the selected serialized-closure evidence; it is not a fresh
source rebuild of the other 1,638 project modules and does not authenticate
their complete historical source-to-object ancestry. It checks selected
outside objects and companions, not outside-transitive package provenance or
dynamic dependencies. It does not bind an external JSON/PDF or prove the
different direct-BFS coefficient equal to the original-order symbolic kernel.
