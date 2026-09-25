# Algebra

- [`JacobianConjecture/`](JacobianConjecture/) contains independent Lean 4
  and Rocq/Coq verifications of Alpöge's explicit dimension-three
  counterexample, a lower-degree stable representative, and exact reductions
  down to a cubic counterexample.
- [`PolynomialFormulas/`](PolynomialFormulas/) contains independent Lean 4 and
  Rocq/Coq verifications of the linear, quadratic, Cardano cubic, and Ferrari
  quartic formulas, together with root-collection functions and entrywise
  correctness and exhaustiveness theorems.
- [`SurrealNumbers/`](SurrealNumbers/) contains a Lean 4 library that
  constructs the surreal field `No` as an ordered field of sign sequences,
  proves it real closed and the surcomplex numbers `No[i]` algebraically
  closed, constructs Conway's omnific integers inside `No` and proves their
  basic arithmetic (constant term, units, floor, integer roots, finite
  quotients), and formalizes further results from 63 research reports on
  `No`, `No[i]`, the omnific integers and related structures
  ([`docs/`](SurrealNumbers/docs/README.md)). It is a self-contained Lake
  package (`lake --dir Algebra/SurrealNumbers build`) whose default build
  also runs an axiom audit; its [README](SurrealNumbers/README.md) and agent
  guide describe its workflow.
