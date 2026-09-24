# Proof and source audit

## Exact scope

The mathematical arguments and audit were prepared by the same assistant.
This is not an independent review. No theorem was verified by Lean or by
another proof assistant. No external mathematical reviewer was consulted.
The calculations were executed locally with Python/SymPy, not through the
Wolfram connector. The article does not use computation as a substitute for
proof of an infinite statement.

## Repository pin and comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `958b5c4865819bd55ea1f5ffc050282aea7ef570`.

The GitHub connector was used to read the repository and the relevant
reports. Main exact comparisons:

1. `docs/surcomplex/autonomous-dilation-relations/article.tex`, Section 13:
   - `adr:thm:order-two`: prior single-scale infinite-support example;
   - `adr:thm:all-orders`: prior independent-monomial special case;
   - `adr:prop:rank-bounds`: finite-support rank at least three was bounded
     but not settled in general.
2. The same report, Section 16:
   - Question 1 is answered affirmatively in full by our finite-support theorem.
   - The rational-rank part of Question 2 is answered: order n forces rank <= n.
   - A relative-rank part of Question 8 is answered: a relation in m distinct
     dilates gives relative rank <= m - 1. Lattice generation, denominator
     growth, support order type, and full support classification are not settled.
3. `docs/surcomplex/single-dilation-hahn-support/README.md` at the same pin:
   prior exponent-dilation definitions, strongness, additive equations,
   definability, and proper-class caveats.

The root/documentation guides and selected other report guides were
surveyed to avoid duplicating the large quotient, curve rigidity,
automorphism, and analytic programs. This was not a line-by-line review
of every manuscript or every incoming companion in the repository.

## Published primary sources

- L'Innocente and Mantova, arXiv:1710.07304v5 (2024): normal forms,
  omnific integers, and Hahn background. The first page was visually
  inspected as well as reading parsed text. Their factorization and
  prime theorems are not claimed as contributions here.
- Edmonds, *Matroids and the greedy algorithm*, Mathematical Programming
  1 (1971), 127–136, DOI 10.1007/BF01584082: classical greedy-basis context.
  Publisher metadata was consulted; the ordered/Hahn argument needed here
  is proved directly, not imported from an unread theorem.
- Beecken–Mittmann–Saxena, arXiv:1102.2789: Theorem 6 and the surrounding
  text identify the classical characteristic-zero Jacobian criterion.
  Both forms used in the manuscript have proofs included.
- Chyzak–Dreyfus–Dumas–Mezzarobba, arXiv:1612.05518v2, Remark 2.18:
  explicitly contains the decreasing-denominator Mahler series. This is
  credited as prior, not a newly invented construction.

The user-supplied Wikipedia page was consulted as an orientation source,
not used as the technical foundation of a proof. Targeted web searches
were not an exhaustive priority investigation. No matching complete
package was identified in the consulted sources; this does not prove
that individual results are absent from other literature.

## Proof checkpoints

### 1. Greedy leading determinant

- Support is reverse well ordered, not merely bounded.
- Coefficient vectors span the required finite dimension.
- Greedy basis exists even if infinitely many dependent terms precede a pivot.
- Any independent sorted basis is componentwise <= the greedy basis.
- Rearrangement is strict for distinct positive rational weights.
- Dependent exponent choices have determinant zero before exponent selection.
- Hahn finite fibres justify regrouping the determinant expansion.
- Unique largest nonzero term prevents cancellation; other terms may cancel.

### 2. Relative support theorem

- Quotient V/H is a vector quotient; no quotient ordering or convexity is used.
- Functionals are Q-linear, vanish on H, and have an invertible selected minor.
- Coefficientwise Euler operations are actual strong derivations.
- D_l S_q = q S_q D_l, with q nonzero in characteristic zero.
- All chosen derivations vanish on the entire full Hahn subfield over H.
- The nonzero Jacobian implies independence by a least-degree polynomial argument.

### 3. Finite and rational profiles

- Finite support permits a rational monomial field upper bound after clearing
  denominators separately for each finite set of dilation parameters.
- The field of all rational dilates is contained in an algebraic extension of
  a fixed support-rank rational function field.
- Rational-profile coefficient vectors and Hahn support vectors have the same
  annihilator; rank is compared in finite-dimensional coefficient space.
- The Jacobian-rank upper bound is used only in a finite rational function
  field, not in an arbitrary Hahn field.
- A noninjective exponent parametrization must be reduced to a certified
  rationally independent basis before applying the rank algorithm.

### 4. Free omnific families

- Inner and outer normal-form supports are different and tracked separately.
- The base is a set; its entire support span and union of inner supports are sets.
- A fresh ordinal bound exists above the negatives of those inner supports.
- Ordinary ordinal operations define beta; surreal negation and monomials
  define the new scales. Distinctness and strict descent are explicit.
- New support spaces form a rational direct sum modulo the base exponent space.
- Joint independence uses block derivations, not just pairwise independence.
- Coefficients Z and Z[i] give embeddings into Oz and Oz[i]; coefficients C
  require the nonnegative-support surcomplex ring, not Oz.
- No independence over the entire proper class is claimed.

### 5. Telescoping hierarchy

- Unbounded denominators modulo a finite-rank lattice give infinitely many
  character conjugates and therefore preclude algebraicity over its monomial field.
- Algebraic-closure base change preserves the support and polynomial degree bound.
- Characters of a subgroup extend because the algebraically closed coefficient
  field has divisible multiplicative group; the extension proof is included.
- The finite difference is a finite-support rank-r element.
- Independence of r finite differences plus transcendence of the telescope
  gives r+1 independent consecutive transforms.
- Every forward transform lies in a field of transcendence degree r+1.
- Finite approximations retain their final boundary term. Infinite support
  reindexing, not valuation convergence, proves the infinite identity.

## Non-claims

No solution of a named published classical conjecture; no certified worldwide
priority; no full classification of finite-rank infinite supports; no
arbitrary-surreal equality algorithm; no positive-characteristic extension;
no claim about the Gonshor exponential, analytic continuation, omnific primality,
or a preferred surreal derivation; no proof-assistant verification.

## Actual finite validation

`verification_results.json` records 549 named cases and 1,918 subsidiary
independent-basis comparisons. They include a full independent determinant
expansion for 390 cases, finite boundary identities, rational-profile
matrices, two worked polynomial checks, and explicit characteristic/sign
counterexamples. They do not certify the infinite theorems.
