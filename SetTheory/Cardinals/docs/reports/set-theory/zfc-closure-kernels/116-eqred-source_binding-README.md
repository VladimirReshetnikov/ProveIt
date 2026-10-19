# Ordinary source and enumerator supplement

`ORDINARY_PROOF.md` is the uniform ordinary mathematical proof. It is not a
new Lean/Rocq theorem or a proof about a binary transition table.

From the package root:

    python3 -O source_binding/check_binding.py

This replays 26 complete source identifications against the pinned 219-node
reference, validates exact AX formulas/parser arity, records source/provider
hashes, and rejects four adversarial mutations. The bundled inputs are data;
the checker imports no emitter or optimizer. The top-level `tools/replay_all.py`
runs it in a fresh temporary copy, leaving the distributed receipt unchanged.

The original report's workspace paths are retained as provenance. For this
standalone copy, only the checker's input/provider path roots are adapted.
The mathematical proof names reused existing Lean providers; hashing their
source is not a fresh kernel build, and their full dependency closure is not
bundled. The ordinary source-to-derivability result does not verify decoder
allocation, a binary runtime, blank startup, or a new state bound.
