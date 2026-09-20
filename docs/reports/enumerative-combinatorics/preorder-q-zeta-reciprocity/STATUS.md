# Status and scope

## Main claims

1. A complete proposed proof of the full q-refinement of Athanasiadis–Chapoton
   Conjecture 4.9 (arXiv:2605.26916v1, equation (21)), strengthened to an
   exact-support identity, in multivariate form. The user's manifest explicitly
   left that refinement out of its previously listed ordinary q=1 result.
2. The same strengthened identity proved a **second** time by an
   architecturally independent argument (the transfer involution), and, inside
   the first proof, by a **second** interchangeable geometric engine.
3. Positive integral formulas for `(-1)^n Z_q(P_tau, [-r]_q)` at every r >= 1,
   with a colored-composition interpretation, monic degree rn and lowest
   exponent equal to the number of maximal equivalence classes. Reachable only
   by the second proof.
4. The arbitrary normalized-height variant, with exponent `h(1_supp(b))`.
   Reachable only by the first proof.
5. Consequences: a transversal-matroid/Tutte evaluation and an independence
   complex h-polynomial for the same coefficient; the cofinality criterion for
   which supports occur; explicit coefficient formulas including `[t^(n-2)]`;
   the product rule over disjoint unions; the multivariate matrix identity.

## Proof dependencies

The proofs import Hall's theorem (proved in Appendix A), Postnikov's
lattice-point formula, and Ehrhart–Macdonald reciprocity. Engine 1 of the first
proof imports one further result, Postnikov's bipartite draconian duality;
Engine 2 and the second proof do not, and Engine 2 derives the instance of that
duality it needs from the lattice-point formula alone. The second proof uses no
matching theorem at all. The target is never assumed. Every additional
reduction is written out in the article. No earlier user research package is
used as a proof source.

Three specific overlaps with the earlier package
`enumerative-combinatorics/preorder-polytope-reciprocity` are acknowledged
rather than concealed, and flagged at the places where they occur: the
independent-capacity reciprocity reproved here, the enumerator formula
re-derived here, and the ordinary q=1 case, which continues to be presented as
covered there and not as a fresh result.

## Checks actually performed

Three independent verifiers, which test three different theorems and do not
subsume one another, plus ten unit tests. Between them: all 7,332 labelled
preorders on zero through five elements checked twice over, with all support
coefficients, all associated interior counts and the unit-source assignment
model; 48 further preorders on six through eight elements from seed 20260920
and 192 further from seed 26092049; 1,560 negative-evaluation polynomial
identities at r = 1..4; 1,250 direct capacity and reciprocity counts; 1,170
inverse-matrix evaluations; positive-multichain interpolation checks at four
positive integer q-values, one of them with a nonlinear height; and the
bipartite Euler lemma tested standalone on all 5,058 small labelled bipartite
graphs plus 300 seeded ones. The two nontransitive and capacity-two
counterexamples are computed and checked to fail the extensions they refute.

The PDF build was clean at 45 pages: no overfull or underfull boxes, no
unresolved references and no LaTeX warnings.

## Limits

This is an AI-assisted, unrefereed mathematical draft, not a proof-assistant
verification. Finite computation corroborates the proofs but cannot replace
them. That three separate drafts reached the same two statements by three
different routes is evidence of internal consistency, not of correctness: a
shared misreading of the source's conventions would not have been caught by
that agreement, which is why those conventions are restated and audited
explicitly. Focused searches did not identify a separate resolution of the
full conjecture; this is not a certification of priority. The claimed results
do not include the source's other real-rootedness or positivity conjectures,
no canonical pointwise bijection is supplied for the support–interior
identity, and no direct sign-reversing involution is constructed. Two open
problems are recorded rather than solved.

See `notes/source_audit.md` for source versions and the version-date anomaly,
`notes/proof_audit.md` for the dependency map and the delicate transitions,
`notes/manifest_provenance.txt` for the verbatim manifest entry, and
`data/verification*.json` for recorded results and reproducible test inputs.
