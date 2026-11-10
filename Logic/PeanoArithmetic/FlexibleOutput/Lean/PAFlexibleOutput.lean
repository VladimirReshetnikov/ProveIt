import PAFlexibleOutput.ProofCore
import PAFlexibleOutput.MathlibAssembly
import PAFlexibleOutput.Statement

/-!
# A divergent program with every possible output in a model of PA

Import surface of the project. The three modules are independent of one
another:

* `PAFlexibleOutput.Statement` defines the concrete target
  `PAFlexibleOutput.FullySpecifiedMainClaim` and the named obligations still
  to be discharged. It proves nothing.
* `PAFlexibleOutput.ProofCore` proves the logical core over an abstract
  interface (namespace `FlexibleOutput`).
* `PAFlexibleOutput.MathlibAssembly` obtains the self-referential program from
  Mathlib's `Nat.Partrec.Code.fixed_point₂`, conditional on an arithmetic
  bridge and a proof-search implementation (namespace `FlexibleOutputMathlib`).

The concrete theorem for first-order Peano arithmetic is not yet proved; see
the project README for the remaining obligations.
-/
