# External comparison of the nine-variable JSON and Lean recipe

`check.py` parses the 45 concrete Lean `Dag.snoc` stages and compares each
constructor, reference index, exponent expression, finite binder and input
with the corresponding pinned JSON node. It also checks the JSON seed and
coefficient-macro metadata, stage order and output index. It rejects a changed
node at each of the 45 positions and four further metadata or Lean-source
mutations. The author run exited 0; `result.json` records both input hashes.

This is an external, narrow parser of the pinned source fragments, not a Lean
proof about JSON, a verified Lean parser, a coefficient expansion, or a PDF
binding. In particular, its own parser correctness and its correspondence with
Lean's language semantics remain outside the theorem. The separate audited
Lean recipe-to-endpoint equality applies to the Lean recipe. An [independent
review](../../reviews/nine-seed33-jones-json-lean-structural-independent/README.md)
passed, using a separate canonical renderer and replaying the mutation controls.
