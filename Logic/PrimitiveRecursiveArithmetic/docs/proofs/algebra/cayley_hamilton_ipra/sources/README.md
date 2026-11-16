# Sources and provenance

## Scope source

The user-specified article was inspected at revision 1375228092:

https://en.wikipedia.org/w/index.php?title=Cayley%E2%80%93Hamilton_theorem&oldid=1375228092

The manuscript provides original derivations, corrects missing hypotheses,
and does not adopt every assertion in that article as a proved premise.

## Repository source

`proveit_sources_audit.json` records the inspected commit and Git blob hashes.
The iPRA proof system and translation interfaces were read through the GitHub
connector. No remote repository changes were made for this task.

The delivered-packets inventory is located at:

`Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`

It is a sibling of ConciseIPRA, not a file beneath ConciseIPRA. Its descriptions
of incoming packets are explicitly marked as unchecked at placement. No
mathematical lemma from those packets is assumed in this development.

## Primary mathematical references

- Stacks Project, section 10.16, https://stacks.math.columbia.edu/tag/05G6
- Brian Conrad, Generalized Cayley–Hamilton and integrality,
  https://math.stanford.edu/~conrad/210BPage/handouts/cayleyhamilton.pdf
- William Stein, Algebraic Number Theory, a Computational Approach, chapter 2,
  https://wstein.org/books/ant/ant/Ch2.html
- Fuzhen Zhang, Quaternions and Matrices of Quaternions, LAA 251 (1997), 21–57,
  DOI 10.1016/0024-3795(95)00543-9;
  https://nsuworks.nova.edu/math_facarticles/100/
- Yongge Tian, Matrix Representations of Octonions and Their Applications,
  https://arxiv.org/abs/math/0003166v2 (identifies the matrix theorem not proved here).

The manuscript does not rely on an omitted proof in these references to
establish its finite identities. They provide background and source context.

## Mathlib comparison

Mathlib tag v4.32.0, `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` and
`Coeff.lean`; blob hashes are recorded in the JSON audit. The host theorem
`Matrix.aeval_self_charpoly` and remainder corollaries are separate reference
targets, not internal iPRA derivations.

