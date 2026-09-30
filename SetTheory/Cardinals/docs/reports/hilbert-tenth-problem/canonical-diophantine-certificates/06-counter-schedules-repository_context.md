# Repository context and source audit

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspection date: September 30, 2026.

The recursively listed repository tree returned commit:

`e8bb0931d67f80d9fce87a8cddb0f661ff19f956`

Inspected repository documents through the GitHub connector:

- Root `README.md`, for the repository map and computability topics.
- `Computability/HilbertTenthProblem/README.md`, for the documented MRDP, universal-equation, corrected-Jones-paper, and register-machine work.
- `Computability/HilbertTenthProblem/Lean/STATUS.md`, for the documented finite-trace, bounded-quantifier, primitive-recursive and MRDP interfaces and the distinction between completed and pending work.

The relevant README was returned with modified timestamp `2026-09-30T04:10:33Z`. The tree hash records the snapshot observed; main-branch document reads were performed during the same inspection rather than by rebuilding a local checkout. No claim is made that the entire repository was inspected or that its formal proofs were independently rebuilt.

## Why this extension was selected

A generic “this interpreter is computable, therefore Diophantine” article would duplicate machinery already documented in the repository. The supplied study instead tracks exact local resource semantics, auxiliary-witness multiplicity, compressed powers, and canonical concurrent traces. Its direct compiler does not use an MRDP backend. MRDP enters only the later substrate-universality and normal-form consequences.

## Trust boundaries

The new theorems are proved directly in the article. They do not rely on an unverified result elsewhere in the repository. The code is newly supplied prototype code with finite tests, not an addition to the repository and not a kernel-checked formalization. No files in the GitHub repository were modified.

The proposed integration boundary is a unique-solution compiler theorem, stronger than a mere existential Diophantineness predicate. Porting only existential reachability while dropping the fiber-cardinality contract would lose one of the central results.

## Primary research references

The article bibliography records Anisimov–Knuth (trace sorting), Zetzsche (bicyclic/graph-monoid storage), Matiyasevich (MRDP and finite-fold representation), Cantone–Cuzziol–Omodeo (single-fold specifications), Grunewald–Segal (quadratic decision procedures), and Jones–Matiyasevich (register-machine exponential Diophantine representations).

The study distinguishes classical ingredients from its explicit constructions and does not establish comprehensive historical priority for equivalent formulations. No general finite-fold conjecture, single-fold conjecture, or cubic Diophantine classification is claimed to be resolved.
