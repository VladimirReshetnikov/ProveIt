# Theorem and dependency ledger

“Proof supplied” means an ordinary mathematical proof in `article.tex`, not a
kernel-checked theorem and not a claim of historical first publication.

| Statement | Main hypotheses | Dependencies | Status |
| --- | --- | --- | --- |
| Theorem 1.1, perfect gap after countably many parameters | F = R or Q_p; proper analytic K; K relatively algebraically closed in F; countable external C | Lemma 4.1; Proposition 4.2; Proposition 5.2; Mycielski | Proof supplied; assembled contribution; priority unverified |
| Theorem 1.2, arithmetic-to-Hahn gap | Nonstandard Borel M satisfies full PA | Theorem 2.4 and Sections 3–10 | Proof supplied using the stated external inputs |
| Lemmas 2.1–2.2, definable traces and Turing ideal | Nonstandard M satisfies full PA | Internal finite comprehension and deterministic oracle traces | Proof supplied; no weakening to EFA asserted |
| Lemma 2.3, analytic standard system | Borel arithmetic presentation | Fixed standard remainder predicates; analytic/coanalytic separation | Proof supplied |
| Theorem 2.4, no full Borel standard system | Borel EFA model | Glazer, February 2024, slide 4 | External input; not reproved |
| Proposition 3.3, faithful ideal-to-field passage | Turing ideals S,T | Ternary-gap and p-adic digit encodings | Proof supplied |
| Lemma 3.4, oracle-computable individual roots | Polynomial coefficients computable from one oracle | Finite nonuniform isolating data; real bisection; p-adic Newton estimates | Proof supplied; no uniform all-roots selector claimed |
| Theorem 3.5, scalar-field closure and elementarity | Turing ideal S; analytic/proper S for corresponding qualifiers | Lemma 3.4; real closed field QE; Macintyre QE | Proof supplied with QE as input |
| Lemma 4.1, no positive countable transcendence degree | Analytic K in R or Q_p | Characteristic-zero derivation extension; analytic graph; Borel automatic continuity | Full proof supplied; priority unverified |
| Proposition 4.2, proper countable algebraic hulls | Theorem 1.1 hypotheses | Lemma 4.1; analytic closure under projections | Proof supplied |
| Proposition 5.2, null and meager dependence relations | Theorem 1.1 hypotheses | Proper hulls; Fubini; Kuratowski–Ulam | Proof supplied; no enumeration of uncountable coefficient fields |
| Corollary 5.3, real Hausdorff dimension zero | Proper analytic relatively closed real hull | Edgar–Miller theorem | Inherited consequence; not a new dimension theorem |
| Theorem 6.2, simultaneous local perfect families | One nonstandard Borel PA model; countable C_v at every place | Open coordinate projections; Mycielski | Proof supplied; no fixed common-digit or computable parametrization |
| Theorem 7.1, exact p-adic residue image | Any nonstandard PA model, not necessarily Borel | Definable traces; total internal block recoding; ordinary residues | Full proof supplied |
| Theorem 7.3, exact profinite image | Any nonstandard PA model | Factorial residue codes; explicit overspill for a coherent nonstandard prefix | Full proof supplied; single shared oracle required |
| Corollary 7.4, idempotents recover the standard system | Turing ideal from a nonstandard PA model; proper for strictness | Exact profinite image; local integral domains; effective finite CRT | Boolean reconstruction and strict product inclusion proved |
| Proposition 8.1, tail-ring finite quotients | Subfield L of R; negative-support rational Hahn tails | Constant extraction; coefficient division by ordinary integers | Elementary proof supplied |
| Theorem 8.2, completion versus canonical image | Nonstandard PA ring; tail ring | Theorem 7.1; Proposition 8.1 | Proof supplied; includes explicit 1/(p+1) distinction |
| Corollary 8.3, no unital map D to Z or the tail ring | Nonstandard PA model | Preservation of ordinary residues | Proof supplied; included as a scope safeguard |
| Theorem 9.1, coefficientwise Hahn independence | Fields K subset L; ordered abelian SET-group G | Finite polynomial relations; coefficient extraction | Elementary proof supplied |
| Theorem 10.1, invisible same-scale omnific family | Restricted real coefficient field H; Cantor P independent over H | Theorem 9.1; rational Hahn-to-Conway normal forms; tail divisibility | Proof supplied on a set-sized slice |
| Section 10.2, topology distinction | Family r*omega with distinct real r | Real differences times omega exceed every standard integer | Proof supplied; image is discrete in surreal order |
| Section 12, formalization | Proposed interfaces, not executable Lean | Current repository documentation | Plan only; no build or new machine-check claimed |
| Section 13, eleven research questions | Individually stated | Results and boundaries of this article | Further questions; not represented as previously published open problems |

## Executed checks and their limits

`verify.py` checks finite digit recoding, finite rational Laurent-tail algebra,
rational Newton identities, factorial-residue coherence, and finite
Chinese-remainder idempotents. It uses exact arithmetic and fails with a
nonzero exit status on a failed check. None of these checks certifies any
infinitary row of this ledger. They are not a substitute for the mathematical
proofs or for a future proof-assistant development.
