# Effective-language chapter audit

- File: `effective.tex`.
- Sixteen theorem/lemma/proposition environments, all with human-readable proofs.
- No Lean compilation or checked object-level iPRA derivations are claimed.
- Definitions, exact Lean goals E01--E16, machine encoding, compiler clauses,
  and object-level completion checklist are in `lean/EffectiveOutline.lean.txt`.

## Key safeguards

1. Universal machine simulation is bounded by an explicit time parameter.
2. Compilation of a PR verifier is a schema for each fixed definition; there
   is no primitive recursive universal evaluator for all PR definitions.
3. Recursive decisions require stated totality; a PR clock is stronger data.
4. Two complementary recognizers give a constructive decider only with a
   supplied exhaustiveness disjunction. Complement nonrecognizability is
   proved independently via P iff not P.
5. Iteration/substitution of unbounded certificate languages carries one
   explicit certificate list. No unproved bounded collection is hidden.
6. Noncontracting grammar membership uses V=sum_{i=0}^{n}m^i finite vertices,
   loop erasure, and a bounded search for a path with fewer than V edges.
7. Noncontracting union/reversal/regular-intersection are fully constructed.
   General CSL complement and unrestricted grammar/TM equivalence are not claimed.
8. The explicit trace language bin(e)#c^t is PR and has an undecidable erasing
   homomorphic image. No complexity bound is inferred from PR membership.

## Primary background citation

Turing, A. M., “On Computable Numbers, with an Application to the
Entscheidungsproblem” (1936/37), original paper PDF:
https://theory.stanford.edu/~trevisan/cs172-07/turing36.pdf

Suggested BibTeX key: Turing1936. Citation supports historical background on
finite machine descriptions/universal simulation only. The modern halting
proof in this chapter is explicitly supplied afresh, not attributed as a
verbatim result in Turing's exact original formulation.

Finite graph reachability and the no-universal-PR-evaluator proposition are
reused from foundations labels `base:graph` and `base:noeval`; the chapter
contains unnumbered recalls rather than duplicate theorem counts.

Theorem `eff:nc-pr-separation` adds the constructive strict inclusion
noncontracting-grammar languages < PR-decided languages: binary diagonal
J(bin(e))=1-D_2(e,bin(e)), with explicit separator bin(e) for each code e.
The uniform evaluator D_2 is for the restricted grammar syntax only.
