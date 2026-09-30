# Provenance and claim audit

## Repository anchor

Repository: VladimirReshetnikov/ProveIt

Inspected commit:
`11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5`

The Git commit endpoint independently confirmed this identifier as a commit
(author/committer timestamp 2026-09-30T01:03:26Z), with root tree:
`b6c36d01edb3963af1c55fde93986dc5116f9495`.

Relevant directory:
`SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/nonreal-roots-in-iterative-equations/`

The merged `article.tex` at the pinned commit was independently confirmed by
GitHub's file-content endpoint to have blob:
`b52eba816e4c6a108d740e4e4e0edd5b1f8631ec`.

Repository URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5/SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/nonreal-roots-in-iterative-equations

The repository advanced during preparation; this package does not claim to
incorporate subsequent commits. The relevant source is pinned, rather than
identified only by the moving `main` branch.

## Exact question inspected

The merged README describes Part III as *The Decreasing Spectral Core: Complete
minimal spectra, finite-smoothness rigidity, and global polynomial conjugacy*.
The original Part III was retrieved from the user's Library as
`article(20260929-151305).tex` (with its corresponding PDF). Its Section 11.7 asks
for exact algebraic degree, exceptional compositions, and relations between
polynomial-coordinate families. Its earlier discussion proves rational solutions
affine and records the upper bound deg H.

The article resolves exact degree for polynomial-coordinate maps with all
nonzero scalar multipliers. It resolves the same-coordinate family question,
not the broader question for arbitrary unrelated H and G. Its theorems do not
use the source report's smoothness classification as a premise.

## External primary references inspected

1. Michael E. Zieve and Peter Mueller, *On Ritt's polynomial decomposition
   theorems*, arXiv:0807.3578. Relevant full-preprint sections: Lemma 2.2,
   Corollary 2.9, Remark 2.16. Polynomial intermediate fields and normalized
   same-degree right-factor uniqueness are classical ingredients, not novelty
   claims of this package.
   https://arxiv.org/abs/0807.3578

2. Dijana Kreso and Robert F. Tichy, *Diophantine equations and the monodromy
   groups*, arXiv:1601.07316. The full-preprint Morse/symmetric-monodromy discussion
   was inspected. The article supplies the local covering and transposition
   argument and verifies the critical-point hypotheses for its examples.
   https://arxiv.org/abs/1601.07316

3. Szymon Draga and Janusz Morawiec, *Reducing the polynomial-like iterative
   equations order and a generalized Zoltan Boros' problem*, Aequationes
   Mathematicae 90 (2016), 935-950, arXiv:1503.00570. Used for the
   characteristic-root/order-reduction context, not as proof of novelty by
   absence of a statement.
   https://arxiv.org/abs/1503.00570

No exhaustive historical-priority determination is claimed. No source PDFs or
font files are redistributed in this package.

## Proof and computation boundaries

The field theorem uses polynomial Luroth theory and an explicit coefficient proof
of normalized right-factor uniqueness. The geometric Galois conclusion uses the
classical complex monodromy/normal-closure correspondence. The real constructions
use elementary one-variable calculus. The all-degree near-reflection existence
argument uses a nonzero discriminant polynomial and a finite exceptional set.

The checker compares a theorem-based right-factor algorithm with independent
polynomial gcds of generic fibers. It also verifies displayed curve identities,
resultant multiplicities, discriminant formulas, and exact squarefreeness
certificates in stated finite ranges. These computations supplement the proofs;
they are neither a proof assistant nor a proof of universal statements.

The compiled PDF was rendered and visually inspected. Compilation warnings and
reference resolution were checked. The included PDF has 25 pages.
