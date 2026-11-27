# Robust entropy-scale prime products

Research note for ProveIt, 27 November 2026.

* `entropy_products.tex` — self-contained classical proof, with standard analytic inputs cited explicitly.
* `entropy_products.pdf` — compiled note.
* `SOURCE_AUDIT.md` — precise source paths, blob hashes, dependency graph and verification scope.
* `check_finite.py` and `finite_checks.json` — executable small finite checks and recorded output (Python standard library only).
* `InputAudit.lean` — optional interface / axiom audit of the pinned upstream exports, not a formal proof of the new results. Not executed here.
* `Makefile` — rebuild PDF and rerun checks.

## Claims

For primes up to `(log q)^A`, A>2, a uniform quadratic quotient law at prescribed subset size holds after arbitrary fixed-density deletions. For majority retention the quotient is trivial. The sufficient length constant is `(A-1)/(A(A-2))` under Dirichlet GRH for all moduli and `1/(A-1)` unconditionally for almost all prime moduli. Strict inequality above these constants is required. The unconditional typical-residue threshold is sharp. For majority retention, joint disjoint-block products mix in total variation even if their union uses any fixed fraction less than one of the retained primes.

The result concerns almost all residue classes or target tuples, not every one. The global novelty of the result has not been certified. The conditional theorem assumes the precise Dirichlet GRH export and the classical explicit formula; no independent upstream kernel replay or formal verification of the new theorems was carried out.

## Reproduce

Run `make` (standard pdflatex packages and Python 3). For the interface audit, use the separate `vendor/grh-lean/grh` Lake package at its specified toolchain; copy `InputAudit.lean` there, build according to its README and run `lake env lean InputAudit.lean`. Do not import the root ProveIt Mathlib version for this audit. The source repository was not modified.
