# Claim ledger

All theorem references refer to `polish_presburger_glazer.pdf` and its LaTeX
source. “Proved” means a mathematical proof is supplied in this manuscript;
it does not mean independent refereeing, a priority determination, or a
machine-checked proof.

| Location | Claim | Evidence / boundary |
| --- | --- | --- |
| Theorem 2.1 | Real-coordinate Polish model and effective Baire-space model, with structural consequences | Proved in the later sections; answers Glazer's Question 2 as written |
| Proposition 3.2 | A divisible ordered group lex Z is a Z-group | Classical construction, proved explicitly |
| Section 3.2 | One-step periodicity is insufficient for arbitrary predicates on nonstandard groups | Explicit counterexample; no defect alleged in the repository's integer theorem |
| Lemma 3.4 | Coset-invariant finite search on Z-groups | Proved; requires full mG-coset invariance |
| Theorem 3.5; Corollary 3.6 | Quantifier elimination, completeness, and the entire additive induction scheme | Classical method reproved over the precise carriers, including parameters |
| Proposition 3.7 | Definable least-element principle | Proved from the finite-candidate elimination argument |
| Lemma 4.1; Theorem 4.2 | Polish-subspace fact and exact G-delta positive-cone criterion | Background topology proved and applied; topology is not the arithmetic order topology |
| Section 4.2 | Complete metrics, local compactness, and absence of isolated points for the real example | Explicit construction |
| Theorems 5.1–5.2 | Explicit homeomorphism with Baire space and computable addition/division | Constructive proof; executable codec; finite-prefix tests only |
| Theorems 6.1–6.2 | All definable relations are Delta-0-2; uniform finite-mind-change truth approximations | Proved using elimination; effective bounds relative to parameter oracles |
| Theorem 6.3 | Open or closed arithmetic order forces discreteness | General proof assuming continuous successor; gives optimal order rank in uncountable Polish models |
| Propositions 7.1–7.2; Theorem 7.3 | Euclidean self-similarity and exact discontinuity loci for predecessor/truncated subtraction | Proved for the stated examples |
| Theorem 8.1 | Set-sized additive, order-preserving embeddings into omnific integers | Explicit fixed-support normal forms; no ring closure or class-wide topology asserted |
| Theorem 9.2; Corollary 9.3 | No unital semiring expansion when a cofinal infinite additive element exists | Purely algebraic proof; applies to both examples, even for discontinuous multiplication |
| Theorem 10.1 | Every unital additive endomorphism of the real model is positive real scaling | Full algebraic classification; continuity is a consequence |
| Theorem 10.2 | Elementary submodels classified by rational vector subspaces of R | Proved; only the standard submodel and the full model are Polish in the inherited topology |
| Theorem 10.3 | Proper clopen elementary self-copies of the Baire model | Explicit shifts; intersection of their iterates is the standard submodel |
| Lemma 11.1; Corollary 11.2 | Compact cancellative monoids are groups; compact Hausdorff carriers excluded | Classical compact-semigroup fact reproved and applied |
| Section 12 | ProveIt implementation interface and dependency graph | Proposed work only; not new checked Lean files |
| Section 13 | Ten further research questions | Proposed directions; no assertion that an exhaustive literature search established each is open |
| Appendix A.1–A.3 | Symbolic examples and checks | Illustrations, not additional axioms |
| Appendix A.4 | Proof audit checklist | Explicit hypotheses and scope distinctions |

## Executed evidence

`verification_results.json` records 17,930 successful exact checks. They
exercise finite-rank instances, enumeration round trips, finite candidate
identities, and prefixes of stream operations. These tests do not prove
Polishness, induction, arbitrary infinite-stream properties, or universal
quantification over all model elements.

## Claims deliberately not made

- No independently established first-solution or priority claim.
- No proof of Glazer's Question 1.
- No uncountable Polish model of full Peano arithmetic.
- No continuous arithmetic order on these nondiscrete spaces.
- No terminating decision of arbitrary infinite-sequence equality.
- No ring embedding of either example into the omnific integers.
- No formalization of the article in Lean or Rocq.
- No modification of the user's GitHub repository.
