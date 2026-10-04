# Sources, provenance, and proof-status audit

Audit date: 4 October 2026.

## Primary literature

1. Junhong Chen, Joel David Hamkins, Ruizhi Yang: announced joint work on surreal
   arithmetic and set theory. The March 2026 announcement explicitly states the
   birthday-enriched surreal/ZFC bi-interpretation and calls the work in progress.
   https://jdh.hamkins.org/surreal-arithmetic-cuny-logic-workshop-march-2026/
   The 2025 announcement provides an earlier dated precedent:
   https://jdh.hamkins.org/surreal-arithmetic-notre-dame-logic-seminar-nov-2025/

2. Hamkins's March 2026 primary slides were inspected, including the set-coding,
   round-trip, bounded-cut, and concluding theorem material. The concluding
   theorem slide says that details are still being checked. The manuscript does
   not claim to have verified every intrinsic axiom scheme proposed there.
   https://jdh.hamkins.org/wp-content/uploads/Slides-Elementary-theory-of-surreal-arithmetic-Hamkins-CUNY-March-2026.pdf

3. Friedman–Visser, *When bi-interpretability implies synonymy*: the 2025 version
   is used, not the superseded 2014 preprint. Supports terminology and the
   finite-axiomatizability invariant. The report also proves the specific
   finite-axiomatizability lemma it needs.
   https://arxiv.org/abs/2506.01028

4. Kameryn J Williams, *The Structure of Models of Second-order Set Theories*
   (2018 dissertation): primary source for class-theory conventions,
   realizations, and the standard finite axiomatizability of GBC noted in the
   proof of Corollary 3.11. The report does not claim that Williams proved its
   specific numerical reformulations.
   https://arxiv.org/abs/1804.09526
   https://arxiv.org/html/1804.09526v1

5. Emil Jeřábek's 2011 MathOverflow answer: primary expert discussion of omnific
   axiomatization, the complete-theory obstruction, and the known fact
   `Frac(Oz)=No`. The report supplies its own whole-support-shift proof of the
   fraction fact and does not claim it as new.
   https://mathoverflow.net/questions/72691/

6. Classical background: Conway, *On Numbers and Games*; Gonshor, *An
   Introduction to the Theory of Surreal Numbers*; Kaye–Wong on arithmetic and
   finite set theory; Lévy on reflection; Gödel's 1931 incompleteness paper.
   Full bibliographic entries and persistent identifiers appear in the PDF.

## Repository audit

Requested repository:
https://github.com/VladimirReshetnikov/ProveIt

Pinned revision:
`bd1de458b7145f535cfcef0bef47d851c2e82463`

Directly fetched at that revision:
`Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md`

The README explicitly documents earlier full-universe and bounded birthday
coding work, credits CHY, and says its `hset:` labels lack a Lean implementation
mapping. It was not treated as a substitute for auditing the complete proofs
of its many cutoff claims.

Repository search provided additional attribution excerpts from the source
 audit and the definable-surreal report, initially at indexed revision
`fb2287290fb5b253ec8aa18d996887855119eb9c`.
The different indexed and directly fetched revisions are disclosed in the
bibliography. Search for quotient/birthday material was not a proof that the
repository contains no earlier instance of the operation introduced here.
No exhaustive nonduplication or novelty guarantee is made.

## Contribution classification

- **Reconstructed prior result:** birthday-enriched surreal numbers recover ZFC.
- **Explicit presentation developed here:** round-trip coherence axioms that
  turn the structural reconstruction into a theory-level bi-interpretation.
- **Extension developed here:** omnific integers with binary quotient birthday,
  including the exact-recovery axiom O4 and both interpretation round trips.
- **Classical deduction applied here:** reflection and incompleteness prevent a
  ZFC-interpretable theory from interpreting finitely axiomatized NBG, assuming
  Con(ZFC). This is not a new inconsistency result.
- **Direct argument:** class-diagonal obstruction with the precise elementary
  comprehension hypothesis.
- **Class transport developed here:** saturated code classes, the second class
  round trip, and preservation of the ordering of class realizations.
- **Unresolved in this report:** elimination of binary quotient birthday in
  favor of unary birthday; the pure omnific language; a minimal intrinsic
  axiom system; the listed weak-foundation and formalization questions.

## Logical limitations

All principal interpretations are uniform finite-dimensional first-order
interpretations, allowing definable quotient equivalence. Positive constructions
are parameter-free. The NBG reflection obstruction also permits admissible
finite tuples of set parameters. It does not establish a blanket theorem about
arbitrary predicates carrying independent class-theoretic strength.

The class lift uses first-order two-sorted/Henkin semantics and retains class
objects. It is not a claim that every external subclass of a set model belongs
to its specified class realization. The larger-universe example explicitly
changes the universe and is not presented as a same-universe solution.

No proof assistant was run. Finite tests passed, but do not verify the
transfinite interpretations, infinite axiom schemes, class comprehension,
reflection, or consistency. A proof and provenance ledger appears in Appendix B.
