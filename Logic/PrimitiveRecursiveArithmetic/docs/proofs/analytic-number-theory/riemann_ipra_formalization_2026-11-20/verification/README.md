# Verification records

- **build.txt** records a build from a fresh copy of the submitted project sources. Previously built external dependencies were available in the pinned Mathlib cache.
- **Audit.lean** imports the project entry point and prints representative declarations and kernel dependencies. **lean-audit.txt** records its output. An object derivation has a conclusion headed by `Prf PRAAx`. Some semantic and ambient Mathlib arguments use `Classical.choice`, propositional extensionality or quotient soundness.
- **examples.txt** records the output of every top-level `check_*.py` file, in filename order, and each exit code. The tests include signs and field schedules, exact rational logarithm brackets, Taylor data, Gram determinants and finite energies.
- Reproduction commands, the Lean toolchain and the Mathlib revision appear in the main README. Section 8 of the main report maps the scope of verification to the mathematical criteria.
