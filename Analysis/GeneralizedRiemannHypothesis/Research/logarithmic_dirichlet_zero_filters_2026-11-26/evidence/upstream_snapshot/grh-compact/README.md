# The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4

Research artifact. Not maintained and not accepting contributions.

The proof is Levent Alpöge's, with Claude.
The Lean text and the documents in this project were written by Claude (AI).

This project holds a Lean 4 proof of the Riemann Hypothesis. It also proves the Generalized Riemann Hypothesis for Dirichlet L-functions. The proof builds on Mathlib. It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

This project is a shorter rewriting of Levent Alpöge's Lean proof (see <https://alpo.ge/remark.pdf>). It follows that proof's method; many steps are proved by other arguments, and parts of it, mostly background material, were ported from there and then rewritten.

This is the compact edition, about 76,000 lines of code. A readable edition, about 300,000 lines, is in [../grh](../grh/); some of its steps use other arguments.

## Theorems
`src/Statements.lean` states the theorems in Mathlib's terms. `src/Main.lean` proves five theorems:
- `riemannHypothesis`: Mathlib's `RiemannHypothesis`.
- `riemannZeta_eq_zero_re`: every zero s ≠ 1 of ζ other than −2, −4, … has real part 1/2 (s = 1 is the pole).
- `LFunction_ne_zero_of_half_lt_re`: L(s, χ) ≠ 0 for re s > 1/2, except at s = 1 for the principal character of each modulus (the pole).
- `LFunction_eq_zero_re`: every zero of L(s, χ) with 0 < re s < 1 has real part 1/2.
- `LFunction_eq_zero_re_of_isPrimitive`: the special case of primitive χ.

All moduli N ≥ 1 and all characters are covered, primitive or not. The last three theorems say nothing about zeros with re s ≤ 0. To trust the result, read `src/Statements.lean`, which imports only Mathlib, the five statements in `src/Main.lean`, and the list of axioms, and build or replay the files. All other definitions occur only inside the proof.

## Build
The build needs Lean v4.35.0, set in `lean-toolchain`. It needs Mathlib at commit 56a005855ea17e0b0958f73ec801ae140b0a1679, set in `lake-manifest.json`. Run `lake exe cache get`, then `lake build`. If the cache is missing, Lake builds Mathlib from source (about 85 minutes on 12 cores). A build takes one to two hours on 12 cores; allow 24 GB of memory. The build prints some linter and deprecation warnings. `lakefile.toml` raises the heartbeat limit and the stack size. To list the axioms, run `lake env lean scripts/PrintAxioms.lean`. The first of its five results is `'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Checks
Every file in `src` compiles with the pinned Lean and Mathlib, without errors or `sorry`, and was replayed through the kernel of Lean. The first theorem has Mathlib's type `RiemannHypothesis`, the other four have the types fixed in `src/Statements.lean`, and all five depend only on the three axioms above. These checks show that Lean accepts the proof of the stated theorems.

`Challenge.lean` states the five theorems with `sorry` in place of proofs, and `comparator.json` sets up the tool [Comparator](https://github.com/leanprover/comparator), which compares them with `src/Main.lean` and checks the proofs again. Nothing imports `Challenge.lean`, and `lake build` does not build it. We ran Comparator v4.35.0 on this folder (Linux, with a stand-in for its sandbox and `ulimit -s unlimited`), and it accepted the proofs; allow 64 GB of memory and a few hours.

## Layout
The proofs are written to be short, not to be easy to read. About 76,000 lines of code; 95,000 non-blank lines with comments; 113,000 lines in all.
- `src/Lib` (573 files): background results, classed as known in the literature, that Mathlib lacks, with the steps of their proofs. It imports nothing from `src/New`.
- `src/New` (219 files): the set-up and the steps of the argument. Start at `GUIDE.md`, which gives the reading order and the letters, and at `src/New/Main.lean`. A comment near the top of that file lists the inputs, what cancels, the scales and the errors. It proves the main inequality `star_inequality`, the one-sided bound `eventually_primeError_le_rpow` and `New.grh`.
- `src/Lib/General/LinearAlgebra/Base.lean` holds settings that apply to all of `src/Lib` and `src/New`: instance priorities, classical decidability, and `simp` lemmas taken out of the default set or added to it. They add no axiom, and `src/Statements.lean` does not import them.
- `REFERENCES.md` lists the citations and says which were compared with their sources.

## Acknowledgements
We thank the colleagues at Anthropic whose direction and suggestions shaped this rewriting.

## License
Apache 2.0; see `LICENSE`, `NOTICE` and `ATTRIBUTION.md`. The project depends on Mathlib (Apache 2.0), which it does not include; some declarations are adapted from it.
