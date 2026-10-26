# Attribution

Prepared with AI assistance for Vladimir Reshetnikov and ProveIt.

The literal parent is from ProveIt package173, `source/anchor219`, at
commit `ecb9a4b4dda617512952525d50f17343700aac52`. Its CRT-anchor,
constructor-depth, affine-horizon and boundary-valid label-separation
arguments are credited to that package. The simultaneous signed-index
and power pooling theorem is from package176. The acyclic monic
elimination method is inherited from package152 and reused in176/177.

`code/dag_parent.py`, `code/search.py`, `code/producer.py`, and
`code/verify_projection.py` are adapted from the corresponding package176
tools, with source indices, paths, types and pinned inputs updated.
The new joint-source emitter, literal port instantiation, selected pivot
lists, resulting circuits, complete interface checker, evaluator and
ordinary composition proof are this submission's contribution. The
full interface checker was independently written by a separate AI
research agent without importing the producer or search.

Copied proof sources and endpoint files remain attributable to their
original repository authors. `inherited/SOURCE_PATHS.json` identifies
the older pinned arithmetic and Lean endpoints. The license copied
from package173 accompanies these artifacts.
