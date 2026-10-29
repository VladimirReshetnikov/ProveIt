# Finite primitive-recursive codes: independent replay

29 October 2026. `PRAFiniteFunctionCodes` replaces function-valued composition
children with a mutually inductive, arity-indexed finite list. Both syntax
types have decidable equality. A surjective map to `PRAFunctionCodes.Code`
shows that each finite code evaluates to a primitive-recursive function and
that every Mathlib `Primrec` vector function is represented. The surjectivity
proof uses classical choice; it is not an executable extraction from a proof
of `Primrec`.

A fresh independent Lean 4.32 build of both source files passed with
`-M6000 -j1 -DElab.async=false`, matching both author object hashes and the
complete focused-check log. The main log is empty and all four printed axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The parent
object came from the independently replayed `PRAFunctionCodes`; cached
Mathlib package objects were reused without a complete package-source replay.
The [replay evidence](pra-finite-function-codes-root-replay/) preserves both
attempts. The first exited with an import-path error because the fresh module
namespace shadowed the parent provider; the second links the checked parent
object into the private namespace and passes. The author main log was not
retained separately, so the main object and the empty independent main log
are checked, without claiming a byte comparison to an author main log.

Numerical encoding/decoding, PRA axioms and derivations, and the conservation
argument are still open. No uniform primitive-recursive evaluator is asserted.
