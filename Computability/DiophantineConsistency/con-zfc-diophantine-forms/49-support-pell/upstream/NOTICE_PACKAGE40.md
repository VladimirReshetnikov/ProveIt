# Attribution, provenance, and scope

This AI-assisted research package was prepared for Vladimir Reshetnikov's
ProveIt project on 23 October 2026, using repository snapshot
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

## New material

The package contributes a direct simultaneous encoding of 22 quadratic
residuals, certified quadratic-monomial weights, a concrete ten-integer
polynomial of exact degree 237,520,456, its 782-operation evaluator, and
reproducible algebraic and finite verification artifacts. The article
explains the construction and identifies its inherited dependencies.

OpenAI's assistant collaboration supplied the new construction, source
and finalizer reviews, code, and exposition. Independent reviews here
mean separate reviews within that collaboration; they are not external
human endorsements or proof-assistant certificates. No global minimality
or discovery-priority claim is made.

New material follows ProveIt's MIT No Attribution terms in `LICENSE`.
Inherited third-party components retain their original licenses and
notices; this statement does not relicense them.

## Mathematical sources and inherited constructions

The general reduction to ten unrestricted integer unknowns and the
Lucas/binomial bridge results are credited to Zhi-Wei Sun, notably:

- *Further results on Hilbert's Tenth Problem*, Science China Mathematics
  64 (2021), 281-306, arXiv:1704.03504v7.
- *Ten unknowns for Hilbert's tenth problem over the integers*,
  arXiv:2609.01594v2, 2026 preprint.

The weight construction draws on the classical Bose-Chowla method for
sets with distinct bounded sums. The delivered finite weight set is
independently certified by checking all 528 unordered pair sums; the
article gives the precise attribution and role of that construction.

ProveIt's package `31-sun10` supplies the existing ten-integer finalizer,
the complete 121-by-8801 native coefficient tuple, and reference copies
of the parent construction. The 31-positive-variable parent with 22
quadratic residuals originates in package `30-quartic31`. The packed
Wang/native-Pell compiler and the machine calibration have the earlier
provenance retained in the copied source documents. This package changes
the source packing and preserves all four native ports together.

The literal 215-state machine and its endpoint are credited to the
ProveIt contributors and the source authors identified in
`coefficients/licenses/NOTICE-K215.md`. That inherited notice credits,
within their respective stated scopes, Mira and ProveIt, Elliot Glazer,
Jeff's busy-beaver/Rocq work, Andrew James Wade, BusyCoq, and the Coq
Library of Undecidability. Retained original license texts and notices
appear under `coefficients/licenses/`. Copied notices sometimes contain
relative links into their original source packages; those historical
links are not assertions that all linked files are bundled here.

## What the verification establishes

The supplied code verifies finite coefficient recipes, source and machine
bindings, symbolic parent residual identities, monomial separation,
fixed coefficient bounds, norm expansion, operation counts, and exact
degree certificates. It does not decide the infinite blank computation,
prove consistency, or independently reprove every inherited theorem.

The main result is an ordinary mathematical equivalence formalizable in
ZFC, conditional only on the explicitly cited mathematical dependency
chain in the usual sense of a proof using earlier theorems. No consistency
assumption is added to the statement. The included Lean endpoint excerpt
is an inherited source reference, not a newly compiled certificate for
the entire delivered polynomial.

## Unfinished compiler candidate

`research_candidate/` is a separate receiver-factorization investigation.
It includes proved local decoder facts and finite certificates, together
with an explicit remaining synchronization-interface obligation. Its
coefficients are not used by `data/polynomial.json`, and its proposed size
reduction is not presented as an established new complete consistency
equation. Its source copies, K215 notices, and license texts are preserved
inside that directory.

