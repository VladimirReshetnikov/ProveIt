# Constructive Number Theory in iPRA

**Prepared for Vladimir Reshetnikov — 22 November 2026**

Start with **`number_theory_ipra.pdf`**. Its 101 number-theoretic results and five foundational lemmas have human-readable proofs designed for intuitionistic primitive recursive arithmetic. The collection includes lemmas and corollaries; consequences within one numbered block are not counted separately. The report is a substantial selection from the requested topic scope, not an exhaustive treatment of number theory.

## Contents

| Path | Purpose |
| --- | --- |
| `number_theory_ipra.pdf` | Complete report, result inventory, validation appendix, and bibliography |
| `number_theory_ipra.tex`, `chapters/` | Complete editable LaTeX source |
| `theorem_inventory.json` | All 106 numbered statements, labels, source locations, and proof status |
| `*_manifest.json`, `chapters/diophantine_manifest.json` | Additional topic-specific witnesses, bounds, dependencies, and porting notes |
| `lean/` | Semantic definitions, goal interfaces, explicit ProveIt object-language targets, and formalization plans |
| `code/` | Exact-arithmetic reference implementations, finite checks, and inventory generator |
| `verification/`, `code/validation_*.json` | Recorded finite-check results and mathematical review records |
| `provenance.json` | Inspected source URLs, repository revision, source blob hashes, and toolchain pins |
| `SHA256SUMS` | SHA-256 digests of delivered files other than this manifest itself |

## Coverage

| Chapter | Numbered results | Representative topics |
| --- | ---: | --- |
| Foundations | 5 | Boolean reflection, bounded search, clocked loops, finite descent, pigeonhole principle |
| Elementary number theory | 32 | Division, Bézout, factorization, CRT, Euler/Fermat/Wilson, RSA, Lucas/Kummer, divisor functions, Möbius inversion, even perfect numbers |
| Quadratic theory | 22 | Prime-field root counts and primitive roots, reciprocity, two-square classification, four squares |
| Diophantine theory | 20 | Rational roots, Pythagorean triples, quartic descent, continued fractions, finite approximation, bounded Pell existence and powers |
| Finite analytic number theory | 15 | Sieve identities, dyadic Chebyshev bounds, prime reciprocal divergence, zeta and Euler-product errors, finite probabilistic identities |
| Algebraic, p-adic, and partition theory | 9 | Nonunique factorization in Z[sqrt(-5)], capped valuations, Hensel lifting, compatible residue names, partition bijections |
| Explicit transcendence | 3 | Liouville truncations, finite polynomial bounds, uniform separation from nonzero integer polynomials |

## Proof and verification status

The report develops finite mathematical proofs with primitive-recursive algorithms, explicit bounds, and induction invariants. It explains how bounded statements are compiled to Boolean equations so that only quantifier-free induction is needed. Statements involving real or p-adic numbers are presented as the specified arithmetic assertions about fixed rational or residue names.

**The new Lean files are uncompiled blueprints.** No `lean`, `lake`, or `elan` executable was available during preparation. Goal records list outstanding obligations and are not claimed to be inhabited. In particular, an ambient Lean proof about `Nat` would not by itself establish the existence of a derivation in the explicitly encoded iPRA calculus. The report and `lean/README.md` explain that additional layer.

All six Python finite-check suites passed. They provide supplementary checks of algorithms and identities on the recorded ranges, not universal proofs and not Lean proof certificates. Huge worst-case bounds are proved symbolically; the report does not claim to have enumerated them. `verification/final_review.md` records the resolved mathematical review findings.

The inspected ProveIt snapshot is commit `bbb85238dac533fc4b7b84a750cca864fe35fed5`. The toolchain is `leanprover/lean4:v4.32.0`; Mathlib is pinned to `81a5d257c8e410db227a6665ed08f64fea08e997`. Existing source interfaces were inspected, but the complete transitive dependency closure was not rebuilt. The repository's arithmetic prime-number-theorem endpoint is documented separately and is not counted among the self-contained results proved in this report.

## Reproduce the readable report and finite checks

From the package directory:

```sh
sha256sum -c SHA256SUMS
make check
make pdf
```

The finite checks require Python 3 with its standard library. The PDF build requires `latexmk`, pdfLaTeX, Latin Modern fonts, and the usual TeX packages named in the preamble. The hash check should be run before regenerating files: recompilation can change PDF metadata and rerunning checks can change timing fields in JSON records.

The delivered PDF was compiled with no unresolved references and no overfull boxes, then rendered and visually inspected. Intermediate TeX build files and Python bytecode are excluded from the archive.

For proposed Lean replay and remaining proof work, see `lean/README.md` and the formalization chapter. Completing those proofs is additional work; `lake build` is not reported as a successful validation command for this package.

## Source use

The requested Wikipedia article and immediate topic links determine the scope. The report supplies the arguments rather than treating encyclopedic summaries as proofs. The bibliography identifies the mathematical references and exact ProveIt source locations used for orientation and interface inspection. External repository dependencies are not vendored in this archive.
