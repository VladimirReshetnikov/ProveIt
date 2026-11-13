# Independent review: captured BFS80 soundness cone

`check.py` independently traversed the historical replay's captured serialized project headers from `DirectBFS80ModelHalt`, obtaining exactly 739 project ancestors and 43 directly reached outside names. Starting with `DirectBFS80Carry` and `Direct80FixedSlots`, it recomputed the reverse dependency closure within those 739 names and obtained exactly the retained 21 project modules, including both seeds and the halt endpoint. Every affected module's retained direct-import list and object hash matches the pinned prior BFS replay receipt. The checker result is in `result.txt`.

This is a dependency inventory in one captured header graph, not a Lean replay, a mathematically minimal adaptation plan, or evidence that analogous trace75 clients compile. It does not prove reverse completeness, iPRA equivalence, external coefficient/PDF binding, or full historical/package/dynamic provenance.
