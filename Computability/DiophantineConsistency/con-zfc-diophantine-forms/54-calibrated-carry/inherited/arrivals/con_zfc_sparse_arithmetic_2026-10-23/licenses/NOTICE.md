# Attribution and scope

This package was prepared with OpenAI assistance for Vladimir Reshetnikov's
ProveIt project. New contributions are the support-sensitive source,
packed successor translation, concrete target certificate, strengthened
arithmetic square separator, and explicit specialized arithmetic circuits.
The short positive-variable variants add the squared-modulus auxiliary
quotient and its reconstruction proof. Their parent circuits, native tuple,
compiler proof and Pell recovery are inherited from the pinned repository.
No global priority or minimum theorem is asserted.

The31-variable quadratic parent, complete native coefficient tuple, K215
calibration, and native-window/Pell compiler are inherited from ProveIt.
The ten-variable finalizer originates with Sun's cited results and the
repository's package31/package40 implementations. The nine-variable ratio
and finalizer route is inherited from the repository's Jones1982 proofs
and package45. The Bose--Chowla weights themselves are unchanged.

`code/build.py` and `code/circuit.py` adapt the package40 builder and
package31 circuit framework. `code/verify_full_circuit.py` adapts package40's
independent formula audit. `code/polynomial.py` retains its sparse algebra
primitives. `nine/build_nine.py` and `nine/circuit.py` adapt package45's
builder/framework. The other new audits are independent implementations
or explicit adaptations identified by their comments. Exact source file
hashes and repository paths are in SOURCES.json.

Inherited files retain their original notices. The included ProveIt license
applies as stated; no third-party rights or license terms are overridden.
