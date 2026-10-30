# Arbitrary-tail bounded packing

`PRAParameterPackingN.packed n` encodes two parameters by one bounded pair while retaining any finite tail. `packed_bounded` proves the matrix is Σ₀; `modelPacking` proves uniform recovery in arbitrary candidate-PRA models. `packAll_bounded` shows finite syntactic iteration preserves Σ₀. Iterated model recovery, induction transfer and general conservation are not yet proved. `PRAModelTupleCoding` is independently recompiled alongside this work.

The author run `/tmp/pra-arbitrary-packing-author-n69pmhda` and private replay `/tmp/pra-arbitrary-packing-independent-jrju4xne` passed against the 49-module author provider `/tmp/pra-after-prenex-merge-refresh-py8nth3k/lib`. The root independent replay `/tmp/pra-arbitrary-packing-independent-84cvdutu` also passed against the independently accepted 49-module provider `/tmp/pra-after-prenex-merge-independent-m_2gvh6i/lib`. The root replay state, snapshots and logs are retained. The manifest SHA-256 is `9ee4a66f9d060b5932b2f58477d0cabf968bdaec6518662d48cb19162928f39d`; it authenticates five direct parent source/object pairs and the four output modules. Foundation, Mathlib and the remaining parent graph are inherited. Logs and source snapshots are retained; the simple author driver did not write a state file.

```sh
python Computability/DiophantineConsistency/reviews/pra-arbitrary-packing-author-replay/replay.py --parent /tmp/pra-after-prenex-merge-refresh-py8nth3k/lib
```
