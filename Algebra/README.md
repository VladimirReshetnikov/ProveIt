# Algebra

- [`JacobianConjecture/`](JacobianConjecture/) contains independent Lean 4
  and Rocq/Coq verifications of Alpöge's explicit dimension-three
  counterexample, a lower-degree stable representative, and exact reductions
  down to a cubic counterexample.
- [`PolynomialFormulas/`](PolynomialFormulas/) contains independent Lean 4 and
  Rocq/Coq verifications of the linear, quadratic, Cardano cubic, and Ferrari
  quartic formulas, together with root-collection functions and entrywise
  correctness and exhaustiveness theorems.
- [`SurrealNumbers/`](SurrealNumbers/) is the former
  [VladimirReshetnikov/Surreal](https://github.com/VladimirReshetnikov/Surreal)
  repository, merged here with its full history: 63 research reports on the
  surreal field `No`, the surcomplex numbers `No[i]`, Conway's omnific
  integers and related structures ([`docs/`](SurrealNumbers/docs/README.md)),
  and a Lean 4 library that constructs the actual surreal field, proves it
  real closed and the surcomplex numbers algebraically closed, and formalizes
  results from the reports. It remains a self-contained Lake package
  (`lake --dir Algebra/SurrealNumbers build`); its own
  [README](SurrealNumbers/README.md) and agent guide describe its workflow.
