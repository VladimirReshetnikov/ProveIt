# Source, novelty, and verification audit

## Repository version

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned comparison commit:

    efc5446229dbf61a97bdd5edae91dba20af9d131

The GitHub commit record was read through the connected GitHub tool. Its timestamp is 2026-09-23T23:35:05Z and its subject is “Prove the arithmetic homeomorphisms of omnific separation quotients.” The repository was evolving during research; the comparison is against this pinned snapshot, not an assertion about later commits.

The initial repository README and documentation catalogue were also read. They identify the reports as AI-assisted, unrefereed research drafts and separate manuscript claims from exact Lean coverage.

## The specific gap

Primary comparison file:

    docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex

Pinned source:
https://github.com/VladimirReshetnikov/Surreal/blob/efc5446229dbf61a97bdd5edae91dba20af9d131/docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex

Blob SHA reported by GitHub:

    9fd5bd460a19448b9078a4ef7f012e647f545e59

Relevant inspected source regions:

- Lines 1330–1500: unit-orbit valuation examples, finite exceptional indices, differential coefficient recurrences, and bounded-cost exterior obstructions.
- Lines 2020–2150: the sharp pure dilation criterion, the partial-theta witness, and the distinction between actual torsion and residual torsion.
- Lines 2150–2220: `hol:lem:bivariate`, `hol:thm:mixed`, and the nonzero noncofinal-valuation mixed theorem.
- Lines 2220–2228: the limitation after the mixed theorem. The report distinguishes the separate pure conclusions from a mixed result, points to another argument when the value group has no order unit, and explicitly leaves the mixed unit-valuation classification unasserted when an order unit exists. It points to `hol:q:mixedunit`.

Theorem 10.1 and Corollary 10.2 of the present article address that missing *linear* assertion. Theorem 10.4 generalizes the existence criterion to finitely many commuting scalar dilations generating a torsion-free group.

The present article does not claim that the pure q-difference theorem, the recurrence-escape mechanism, the order-unit definition, or the partial theta function is new. Those components are credited and their needed proofs are reproduced. Nor does it claim a resolution of every question about nonlinear mixed equations.

## Other repository comparison

The README and catalogue report a theorem that every ring map from the full omnific ring to a set-sized ring factors through the ordinary constant term. The companion report is:

https://github.com/VladimirReshetnikov/Surreal/tree/efc5446229dbf61a97bdd5edae91dba20af9d131/docs/surreal/set-sized-quotients-of-omnific-integers

The present article uses that reported theorem only to explain why its coefficient-coding construction is not a contradiction: extracting the coefficient at omega^omega is not a ring homomorphism. The correctness of the new coding theorem does not depend on the small-quotient theorem. No independent full audit of that companion report was performed.

## Published primary sources

1. **Conway normal forms and surreal foundations:** A. Berarducci and V. Mantova, *Surreal numbers, derivations and transseries*, JEMS 20 (2018), 339–390, https://arxiv.org/abs/1503.00315. Standard background is imported; the new derivative in the present work is D_z, fixing Hahn coefficients.
2. **Hahn support and formal sums:** B. H. Neumann, *On ordered division rings*, Trans. AMS 66 (1949), 202–252; and V. Bagayoko, L. S. Krapp, S. Kuhlmann, D. Panazzolo, M. Serra, *Automorphisms and derivations on algebras endowed with formal infinite sums*, https://arxiv.org/abs/2403.05827, consulted version 2. Positive-support summability is imported, not derived from a real-valued norm. The modern source was consulted directly; the Neumann reference is credited as the historical source rather than represented as a full independent historical-paper audit.
3. **Skolem–Mahler–Lech:** C. Lech, *A note on recurring series*, Ark. Mat. 2 (1953), 417–421, https://doi.org/10.1007/BF02590997; and J. P. Bell, *The Skolem–Mahler–Lech theorem*, Documenta Mathematica, Mahler Selecta (2019), 173–178, https://ems.press/content/book-chapter-files/27398. This zero-set theorem is an essential imported result, not a new theorem or a supplied decision procedure. Bell’s PDF was read and visually inspected.
4. **Related valuation-growth work:** C. Fuchs and S. Heintze, *On the growth of linear recurrences in function fields*, Bull. Aust. Math. Soc. 104 (2021), 11–20, https://arxiv.org/abs/2006.11074, https://doi.org/10.1017/S0004972720001094. Their one-variable function-field results provide related context. The article does not claim to improve their effective constants; it gives an exact existential profile for a different, arbitrary-rank Hahn setting.
5. **Different generalized-recurrence setup:** L. S. Krapp, S. Kuhlmann, M. Serra, *Generalised power series determined by linear recurrence relations*, https://arxiv.org/abs/2206.04126, published in Journal of Algebra (2025). Their exponent-indexed setup is distinguished from ordinary-natural-number-indexed recurrences with Hahn-valued terms. No theorem from that work is silently imported.
6. **Positive characteristic boundary:** H. Derksen, *A Skolem–Mahler–Lech theorem in positive characteristic and finite automata*, Invent. Math. 168 (2007), 175–224, https://doi.org/10.1007/s00222-006-0031-0. The elementary counterexample in Section 11.3 is proved directly; this paper provides context for the different characteristic-p theory.

The user-supplied Wikipedia page was read for orientation. It is not used as the principal source for a technical theorem.

## Candidate-original content and dependence

- **Uniform coefficient algebra:** proved from the Hahn support lemma and finite binomial identities.
- **Periodic unit valuations:** proved by taking the least coefficient that is not an identity on a residue class, and then applying classical Skolem–Mahler–Lech.
- **General exact affine valuations:** proved by grouping roots with equal valuations, applying the unit result, and comparing finitely many affine functions in the actual ordered group.
- **Finite coefficient-condition compression:** proved using the finitely generated sequence algebra and Hilbert’s basis theorem. The proof selects a finite subset of the original conditions.
- **Omnific coefficient universality:** proved directly by shifting a reverse-well-ordered normal form. Independent of Skolem–Mahler–Lech.
- **Mixed unit and multibase rigidity:** proved from the valuation profile and the explicitly reproduced recurrence-escape mechanism.
- **Determinantal profiles:** derived by applying the recurrence theorem to finite exterior powers.

“Candidate-original” means developed and proved at manuscript level in this work, with no matching result identified in the targeted comparison. It does not establish priority. Neither repository keyword searches nor a finite literature search can establish worldwide novelty.

## Mathematical boundary checks

The manuscript explicitly handles:

- arbitrary-rank values rather than silently Archimedeanizing them;
- zero recurrence terms, zero characteristic roots, and finite initial exceptions;
- residual roots of unity versus actual torsion in the dilation group;
- infinite Hahn supports and the first-nonidentity coefficient argument;
- infinitely many coefficient conditions without taking an infinite union of exceptional sets;
- class-sized surreal ambient fields by localization of each finite recurrence to a set-sized Hahn field;
- strong evaluation before cancellation;
- the distinction between support restrictions and the integer constant-term condition in full omnific membership;
- pre-encoded data versus effective computation in the coefficient-coding example.

## Checks actually performed

- `python3 verify.py`: **4,605 exact finite checks passed**. The retained output is `verification.txt`.
- Multiple `pdflatex` passes: successful compilation, no undefined references or citations, no overfull boxes.
- Final PDF: **22 pages**, rendered page by page and reviewed in contact sheets; all page text bounds were checked against the page edges. The title, equations, proof paragraphs, table, and bibliography show no clipping or overlapping text.
- No Lean build of these new results was attempted; no new Lean proof is included.
- No exhaustive audit or rebuild of the source repository is claimed. No repository files were modified.

The exact checks concern finite examples, not a formal proof of the new theorems. The PDF compilation check concerns document integrity, not mathematical truth.
