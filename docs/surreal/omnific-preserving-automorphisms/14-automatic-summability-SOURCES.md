# Sources and scope of comparison

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `3d40856953f4bb0f5d069e45a3b4bab6eda33040`

The principal inspected source is:

`docs/surreal/omnific-preserving-automorphisms/article.tex`

Its introduction and principal criterion explicitly concern strong
coefficient-fixing 1-automorphisms. The article here credits its coefficient
reconstruction and convex-scale criterion, re-proves the criterion, and supplies
an automatic-strongness argument for all automorphisms of the real pair.

The repository's root README and documentation catalogue were also inspected
for scope, verification status, relevant work, and the distinction between
class-sized surreals and set-sized Hahn workspaces. This was a targeted comparison,
not an exhaustive audit of every file or every historical manuscript. The
repository describes its reports as AI-assisted drafts and separates mathematical
arguments, finite computations, and formal Lean coverage.

No writes were made to the repository.

## Primary literature

1. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
   of generalised formal power series*, arXiv:2107.03362v3 (2022).
   https://arxiv.org/abs/2107.03362v3
   Background: general and strongly additive automorphisms, their decomposition,
   and an example distinguishing strong additivity from arbitrary automorphisms.

2. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the
   automorphism group of the surreal numbers*, arXiv:2509.22374v3 (23 April 2026).
   https://arxiv.org/abs/2509.22374v3
   Background: surreal automorphisms and the separation of strong and
   exponential-compatible structures. No open question from that paper is
   claimed resolved merely by citing its abstract.

3. Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann, Daniel Panazzolo,
   and Michele Serra, *Automorphisms and derivations on algebras endowed with
   formal infinite sums*, arXiv:2403.05827v2 (2025).
   https://arxiv.org/abs/2403.05827v2
   Background: formal summability and automorphism--derivation correspondence.
   That correspondence is not used in the main automatic-strongness proof.

4. Richard Blute, Robin Cockett, Pierre-Alain Jacqmin, and Philip Scott,
   *Finiteness spaces and generalized power series*, arXiv:1805.09836v1 (2018).
   https://arxiv.org/abs/1805.09836v1
   Important antecedent: Theorem 3 and Lemmas 4.1--4.2 identify the appropriate
   support-duality structure. The present article does not claim to originate
   finiteness-space duality or all its Hahn specializations.

5. Santiago Camacho, *Truncation in Hahn Fields is Undecidable and Wild*,
   arXiv:1706.03722v1 (2017).
   https://arxiv.org/abs/1706.03722v1
   Context for distinguishing summability invariance from naming arbitrary
   coefficient truncations.

Classical background is cited to Conway's *On Numbers and Games* and Gonshor's
*An Introduction to the Theory of Surreal Numbers*.

The user-supplied Wikipedia article was used as an orientation source only:
https://en.wikipedia.org/wiki/Surreal_number

## Novelty statement

The proposed main contribution is automatic strongness from preservation of
real omnific arithmetic, together with its application to the full real
stabilizer. The exact priority of that application, the detector's formulation,
and the explicit full-class dual counterexample requires independent review.
The literature search is not a certificate of absence of antecedents.
