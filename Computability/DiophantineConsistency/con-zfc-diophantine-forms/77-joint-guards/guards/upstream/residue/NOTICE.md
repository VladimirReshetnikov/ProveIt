# Attribution and scope

This contribution builds on ProveIt, pinned to commit
9cca523d9f27ad39d52993f4065cbd7e58f8bdd4, and in particular:

- source64, `integer41/`: the 41-variable parent, delayed-radix sign proof,
  large scale, and complete source34 coefficient specialization;
- source62, `quartic42/companions/`: centered first-root and triangular
  coordinate elimination;
- sources34 and36: the native coefficient tuple and signed Pell proofs;
- the named native compiler and K215/refutation calibration.

The new work is the absolute-value power recovery with an unrestricted
sign of X, the modulo-three orientation, and the three resulting literal
equations. The new verifier uses the source34 finite coefficient recipe,
with its origin stated in its docstring, and supplies an independent sparse
polynomial checker. No upstream program is executed by it.

Retained files are unchanged and authenticated in SOURCE_PINS.json.
Their original licenses and notices are preserved under upstream/licenses/
and upstream/LICENSE.ProveIt. New material follows ProveIt's MIT license;
see LICENSE. Claims of mathematical novelty are relative to the inspected
repository and are not assertions of publication priority.
