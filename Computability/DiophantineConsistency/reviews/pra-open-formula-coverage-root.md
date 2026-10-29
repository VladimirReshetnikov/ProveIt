# Foundation open-formula coverage, conditional on an equality bit

`PRAOpenFormulaCoverage` parses every Foundation open semisentence with
finitely many bound inputs into the compiler's syntax and proves exact
formula equality. Combined with the conditional compiler, it yields a fixed
PR characteristic code and closed candidate-PRA correctness proof for each
such formula, **assuming** the two candidate-PRA equality-bit certificates.
Those certificates remain unproved here; this is not an unconditional
formula compiler or a general Σ₁ witnessing theorem.

The independent replay `/tmp/pra-open-coverage-root-hqtqv9s2` passed both
modules without warnings, matched author object hashes, and reported only
`propext`, `Classical.choice`, and `Quot.sound`. It used the independently
reviewed conditional compiler and current-source arithmetic providers.
Foundation, Mathlib, PRATheory and earlier code objects remain inherited
cache boundaries. The [evidence packet](pra-open-formula-coverage-root-replay/)
preserves the author’s failed parser/tactic attempts and final builds.
