# Primitive-recursive function codes: independent replay

29 October 2026. The new `PRAFunctionCodes` module defines arity-indexed
zero, successor, projection, composition and primitive recursion codes, with
an evaluator on natural-number vectors. For each fixed code, Lean proves its
function primitive recursive. Conversely, every Mathlib `Primrec` vector
function has some code with equal evaluation. A concrete recursion-defined
addition example is checked. The converse uses classical choice; this result
does not claim an effective extraction algorithm from an arbitrary proof of
`Primrec`.

The main and Checks sources were read and independently rebuilt in a fresh
private output directory using Lean 4.32 with `-M6000 -j1 -DElab.async=false`.
Both object hashes and both full logs match the author's independent build.
The main log is empty; the five printed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The replay used existing Mathlib package
objects and did not rebuild or authenticate their entire transitive source
closure. The replay driver, state and complete logs are retained in
[pra-function-codes-root-replay](pra-function-codes-root-replay/).

This is standard-natural syntax and semantics, not yet a PRA object theory,
proof calculus, encoding, decidable code equality, uniform PR evaluator,
conservation theorem or proof of the requested equivalence in PRA. The
function-valued composition constructor makes effective coding an explicit
next obligation.
