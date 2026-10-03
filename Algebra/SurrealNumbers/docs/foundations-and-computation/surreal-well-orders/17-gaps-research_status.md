# Research status and proof boundary

Date: 3 October 2026.

## Status

This is an AI-assisted mathematical research manuscript with ordinary written proofs. It is not a record of an independent referee review, and it contains no compiled Lean development. The module names in the formalization section are proposed names only. The finite-check results do not certify infinite mathematics.

The source audit was targeted: the pinned merged article, README, research-question sections, and the relevant source proofs were read. It was not an exhaustive literature or repository audit. The manuscript claims no historical priority.

## Contributions relative to the pinned source

The source explicitly left questions about the minimal slice's point characters and cut spectrum, recognition of exhaustive global branches, automorphism extension, and class-realization dependence. The follow-up gives written proofs for:

1. Alphabet gap classification, stability under deletion of fewer than mu labels, and the exact minimal-slice invariants and gap spectrum.
2. Exact eta_r saturation and fusion for at most cf(mu) dense open sets.
3. The minimum cardinality of additional moved positions in supported extension of a set partial injection.
4. Necessary-and-sufficient recognition of injective Ord-word cuts by straddling cylinders at every ordinal length, plus a separate exhaustiveness condition.
5. An exact criterion for extending a core automorphism and a nonextendible core automorphism obtained by conjugating an exhaustive branch gap to a nonexhaustive one.
6. Equivalence between an enumeration being old and its represented core cut being old in a same-set GBC class extension, and existence of new represented cuts in every proper such extension.
7. The precise maximal finite-adjacency components of unrestricted orders and density of their condensation.

The text identifies its inherited results: set-alphabet cardinality and ordinal universality, word compression, elementary comparison of arbitrary labelled class well-orders, supported prefix completion, core interpolation and its surreal order-isomorphism, uniform diagonalization, raw convex fibres, and the adjacency criterion. The source's singular-cardinal binary-coding transition is background, not a new claim here.

## Exact hypotheses and conventions

- Set-sized cutoff theorems: ZFC; kappa is an infinite initial cardinal; X is the sign-sequence order No_{<kappa}; mu = 2^{<kappa}; enumeration length is the initial ordinal mu. No regularity or equation mu=kappa is assumed.
- A genuine gap is a proper partition into a lower part with no greatest element and an upper part with no least element. Point cuts are excluded from the gap spectrum.
- Cellularity is the supremum of sizes of pairwise disjoint nonempty open families; attainment of this supremum is not asserted.
- Core recognition uses an open lower cut: it has no greatest element, while its complement may have a least element.
- Global results: GBC with one specified baseline class bijection Ord -> No. Uniform set-indexed families are given by one class evaluation relation.
- A class well-order requires a least element in every nonempty admitted subclass. Set-likeness is a further condition.
- Higher-order orders are predicates on class variables or are interpreted externally in a specified larger universe. No ordinary class whose members are proper classes is formed.
- The automorphism extension is a uniform operator on individual class enumerations, not a GB class function whose arguments are proper classes.
- Same-set extension results use two transitive GBC models with identical sets, nested class parts, and a common baseline.
- The reserve formula minimizes the number of extra moved coordinates beyond the mandatory moved domain/range union; it does not minimize an ordinal support bound or a birthday.

## Delicate arguments checked in the written development

The proof distinguishes cf(kappa), which controls cylinders, from cf(mu), which controls point characters. It separately handles coordinate cuts, failure at proper limit prefixes, and full-length nonexhaustive injections. Fusion explicitly enumerates all labels rather than merely taking a coherent union. Core reconstruction quantifies over set prefixes and set codes, with class parameters, so it does not invoke class-valued transfinite recursion. The infinite shift example distinguishes infinite support deficiency from finite partial-permutation completion. Adjacency condensation identifies maximal blocks, not just arbitrary finite cylinders.

## Finite checks actually run

All assertions in `finite_checks.py` passed. The JSON records:

- 533,418 predecessor-signature comparisons.
- 266,272 finite adjacency-pair checks.
- 16,072 convex prefix-cylinder checks.
- 852 finite cut-level straddling checks.
- 15,126 finite partial-injection extensions.
- 961 sign coefficient-code comparisons.
- 160,000 word-code comparisons, on 400 words.

These tests do not check singular-cardinal cofinality, limit-length cut existence, class comprehension, class back-and-forth, or infinite reserve necessity.

## Unresolved scope

No full isomorphism classification is supplied for the minimal slice. Arbitrary nonminimal enumeration types and noncardinal birthday cutoffs are not classified. The entire automorphism group, arbitrary baseline changes, higher residual blocks, and the exact strength of their iterative recursion remain research topics. The condensed unrestricted order is not identified with the set-like comparison or with No. The class-extension theorem is not an unlabelled reconstruction theorem for the whole class realization.
