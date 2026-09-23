# Proof, provenance, and verification status

## 1. Mathematical assumptions

The main results assume an elementary class embedding j: V -> M, where M is a transitive inner class containing every ordinal and kappa is the critical point. Set formation using the relevant class parameters is allowed. A normal ultrapower from a measurable cardinal is a sufficient ZFC instance, with the normal measure as a set parameter. The more general presentation uses an amenable embedding in a class theory.

All support sizes and external indexing sets are evaluated in the ambient V. Every normal-form support and every summation index set is a set. “Strong summation” is Hahn summation: reverse-well-ordered union of exponent supports and finite coefficient fibers. It is not convergence in the order topology.

Section 13 adds M^lambda subseteq M and j(kappa) > lambda >= kappa, sufficient to put the actual seed j``lambda in M. Its conclusions are not claimed from measurability alone.

## 2. Classical inputs

The article uses Conway normal forms, the constructive sign-expansion theorem, ordered-field arithmetic on surreals, real closedness, Hahn reindexing and the Neumann lemma, Gonshor's canonical exponential and its purely infinite formula, and quantifier elimination for real-closed and algebraically closed fields. It also uses the standard elementary-embedding and derived-ultrafilter machinery of large-cardinal theory.

The normal-form absoluteness lemma (Lemma 2.4) is the most important interface between the classical surreal theory and the large-cardinal construction. The proof explicitly uses canonical sign reconstruction, not an arbitrary Hahn-field isomorphism. It should receive particular attention in an independent or formal review. Lemma 12.1 similarly identifies the recursive exponential construction across the two universes.

## 3. Main written-proof inventory

| Result | Location | Claimed status |
|---|---|---|
| Strong companion H_j and its uniqueness | Theorem 3.3 | Standard Hahn mechanism, specialized and proved |
| Exact missing-index defect and first defect term | Theorem 4.1 | Candidate original theorem, written proof |
| Short-support equalizer and exact image intersection | Theorem 5.1 | Candidate original theorem, written proof |
| Canonical projection isomorphism of immediate image fields | Theorem 5.4 | Candidate original theorem, written proof |
| Explicit witnesses and incomparable images | Theorem 6.1 | Written consequences with explicit series |
| Exact positive-family cardinality threshold | Theorem 7.1 | Candidate original theorem, written proof |
| Intrinsic positive strong-sum escape from J(No) | Theorem 7.4 | Candidate original theorem, written proof |
| Normal measure recovered from a defect coefficient | Theorem 8.1 | Candidate original coefficient realization of a classical measure |
| Hadamard character and measurable-cardinal criterion | Theorems 8.4–8.5 | Classical ultrafilter mechanism in the stated mask algebra |
| Omnific equalizer, intersection, fraction field, and measure code | Theorems 9.1–9.2 | Written transfers and refinements |
| Surcomplex and Gaussian omnific transfer | Theorem 10.1 | Written coordinatewise transfer |
| Logarithmic defect homomorphism | Theorem 11.3 | Written proof |
| Exact exponential compatibility locus | Theorem 12.2 | Candidate original theorem, written proof |
| Exponential closure distinctions | Corollaries 12.3–12.4 | Written consequences with witnesses |
| Logarithmic versus strong-sum closure of the common field | Theorem 12.5 | Candidate original theorem, written proof |
| Supercompact seed coefficient | Theorem 13.1 | Written proof with additional closure hypothesis |

“Candidate original” means that the formulation was not found in the targeted material inspected for this draft. It does not establish priority. The foundational equivalence of measurability with a suitable ultrafilter is not claimed as new. The paper does not claim to resolve a named published open conjecture, nor to prove any new large-cardinal consistency result.

## 4. Distinctions required for correct use

- The domain equalizer is not the same class as the common image; the maps identify the former with the latter.
- Outer support size is not birthday and does not bound the complexity of the exponents themselves.
- J(No) is not identified with No^M, and H_j(No) is not claimed to lie inside No^M.
- The projection deleting exponents outside J(No) is a field isomorphism only on the specified image J(No). It is not a field homomorphism on all No.
- The exact cardinality test for arbitrary families needs strictly positive terms. Signed families can have cancellation.
- A zero selected coefficient need not mean the entire defect is zero.
- The character theorem uses Hadamard multiplication of masks, not ordinary surreal multiplication.
- The supercompact seed code depends on the chosen enumeration, which is explicitly part of its data.
- The logarithmic-closure statements are universal properties among class subfields; no collection of all classes is formed.

## 5. What was checked computationally

The standard-library Python program was actually run with seed 20260923. It passed:

- 500 finite exponent-reindexing cases with three identities each, plus leading-term checks for the 432 nonzero inputs;
- 251 finite ordered-index deletion and positive-shift cases;
- 500 exact rational tests of the universal difference-of-homomorphisms product identity;
- enumeration of 16,384 candidate Boolean characters on the four-point power-set algebra, finding exactly its four principal characters;
- an explicit distinction between Hadamard multiplication and convolution multiplication.

These finite models are deliberately not represented as finite elementary embeddings with a critical point. There is no such finite analogue of the large-cardinal assumption here. They test only elementary algebraic implementation identities and do not certify the article's transfinite proofs.

The PDF was compiled with pdfLaTeX/latexmk. The final log had no overfull-box warning or unresolved reference/citation warning. Rendered page contact sheets and representative full-size pages were inspected for layout. None of this constitutes mathematical proof-assistant verification.

## 6. Literature and repository coverage

The bibliography gives the classical and contemporary primary references. The principal contemporary comparison is Kaplan–Krapp–Serra on strong maps and surreal automorphisms; the large-cardinal comparison is Neeman's derived-measure and supercompact-seed account. Their established inputs are distinguished from the exact critical-point conclusions here.

Repository snapshot: 0865f043aec113c14c69ef45006bbc7546a4e75a. Selected root documentation, catalogue entries, two foundational report READMEs, and a source preamble were inspected. The full repository and every report proof were not audited. No new Lean files were written or checked, and the existing repository build was not rerun.

## 7. Open work

All twelve questions in Section 16 remain proposals, not results. In particular, the article does not establish optimal consistency strength for an abstract pair of embeddings, recover the entire ambient elementary embedding from the defect data, classify all such image pairs, prove their linear disjointness, determine compatibility with the canonical surreal derivation, or construct an enumeration-free supercompact invariant.
