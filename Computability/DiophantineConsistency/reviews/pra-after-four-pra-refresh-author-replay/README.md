# PRA bound graph after the upstream merge

The author build and two independent replays rebuild the ten local modules affected by the upstream changes to the IOpen completeness bridge, fstIdx derivation binding, ext rewriting binding, and bit binding. The checked dependency closure directly authenticates both `PRASppow2WitnessBound` and its checks, plus their reachable local dependencies, including the negative and positive sqrt/lenbit bounds, negative pow2, both lenbit bounds, positive pow2, ext, and bnd rewriting.

The packet authenticates 236 unchanged local parent source/object pairs in the reachable graph, all rebuilt source/object/log hashes, the parent terminal PASS state, and selected Foundation source/object anchors. It inherits the rest of the Foundation and Mathlib transitive package graph; it is not a source rebuild of those packages. No full `ppow2Def`, exponential, refutation or HA equivalence result follows from this refresh.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-after-four-pra-refresh-author-replay/replay.py --parent /tmp/pra-sppow2-witness-bound-onigimpv/lib
```
