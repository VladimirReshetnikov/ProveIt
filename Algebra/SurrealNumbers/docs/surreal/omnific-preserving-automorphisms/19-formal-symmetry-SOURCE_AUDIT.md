# Source, proof, and novelty audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `889b87c7d2ee2c69ad929fd96c553ffa374ef4f0`

Commit timestamp reported by GitHub: 2026-09-23T23:41:39Z.
The manuscript is dated 23 September 2026; final compilation and file packaging
occurred after midnight UTC on 24 September.

The repository changes rapidly. Statements about what it already contains or
leaves open refer to the inspected snapshot, not to an unpinned future branch.

## What was inspected

The GitHub connector was used to read repository metadata, the root README,
`docs/README.md`, and the following relevant report material:

1. `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`:
   catalogue and source descriptions, including existing divisibility and
   quotient results. The connector response was truncated; the complete
   underlying 164-page report was not audited.
2. `docs/surreal/omnific-preserving-automorphisms/README.md`:
   source provenance and report structure, especially Part II / source 02 and
   later automatic-strongness work. The requested opening range was 1–150;
   the response was truncated after a substantial portion of the text.
3. `docs/surreal/omnific-preserving-automorphisms/article.tex`, at the pinned
   commit, with requested source-line ranges 1300–2100, 2550–3000,
   3000–3450, 3200–3355, and 3350–3740. Several broad-range responses were
   truncated. The 3200–3355 response was complete and contained the Euler
   formal-flow section. The 3350–3740 response included the formal-directions
   question and its stated scope. Only actually returned text was used.

The review covered the relevant arguments and labels, not all 61 reports
mentioned in the catalogue. An empty GitHub search result is not treated as
evidence that a theorem is absent. Comparisons are based on the returned source
text and its precise labels.

## Explicit repository question answered

Path:
`docs/surreal/omnific-preserving-automorphisms/article.tex`

Label: `opa:par:q:directions`

Heading: “Formal directions.” The question asks which derivations of Oz
preserve its purely infinite ideal and which have an iterative integral
Hasse–Schmidt extension Oz -> Oz[[s]]. Its accompanying status limits the
existing sufficient constructions to specified families.

Answer proved in this report: every ring derivation does both; its unique
iterative extension has nth component delta^n/n!. This does not classify all
derivations by support, nor prove all of them strong. Those are distinct,
explicitly retained research questions.

## Earlier results not counted as new

The inspected report already contains:

- the intrinsic divisible ideal and arithmetic reconstruction ingredients;
- root-covered domains and unbounded-root field arguments;
- polynomial and Laurent coefficient rigidity and strong cancellation;
- locally nilpotent rigidity;
- finite-type and pointed algebraic-parameter rigidity;
- the Euler derivations, their independence, and their integral formal flows;
- restrictions and examples involving positive-shift Hahn flows;
- the bounded-scale fraction-field warning for fixed exponent groups.

In particular the article credits `opa:par:thm:Db`, `opa:par:thm:formal`,
`opa:par:thm:cancellation`, `opa:par:thm:pointed`,
`opa:par:lem:rootsfield`, and `opa:par:prop:fracworkspace`.
The present article reproduces short proofs of some background statements
where needed for a self-contained argument.

No proposed automatic-strongness classification in the repository is used as
an input to the new proofs. Existing Lean coverage is reported only as the
repository reports it; the Lean build was not run here.

## Proposed extensions

The following form the research contribution relative to the inspected text:

1. Removing all strongness, linearity, and support restrictions from the formal
   integration question by using the uniquely divisible ideal.
2. The complete integral exponential–logarithm description of the relevant
   formal automorphism group, including all Hasse–Schmidt sequences and finite
   jets.
3. Exact nilpotency class and nonsplitting of every successive nontrivial jet
   extension, proved by explicit noncommuting Euler multiples.
4. Classification of all marked coefficient sections, common fixed series,
   and the intersection of all coefficient copies.
5. A uniform existential coefficient formula in polynomial/Laurent extensions,
   its behavior after formal completion, and a fresh-scale proof that no
   coefficient section is definable with any set of parameters.
6. Uniform formal denominator consequences for the full omnific classes and
   the associated formal fraction-field identities.

The genus-one device, formal characteristic-zero Lie theory, and the generic
complete-ring section argument are classical mechanisms. Their use is not
represented as discovery of those mechanisms. The package does not certify
that every application or formulation above is absent from all literature.

## Public literature checked

Primary sources supplied the technical context. The article has a conventional
bibliography with stable identifiers.

- L'Innocente and Mantova, *A factorisation theory for generalised power series
  and omnific integers*, arXiv:1710.07304v5 (2024).
  https://arxiv.org/abs/1710.07304
  The PDF's normal-form/omnific background was consulted; its first page was
  also inspected as a rendered page. Not a complete independent proof audit
  of that paper.
- Hazewinkel, *Hasse–Schmidt derivations and the Hopf algebra of noncommutative
  symmetric functions*, arXiv:1110.6108 (2011).
  https://arxiv.org/abs/1110.6108
  Bibliographic record and abstract-level context were consulted, not the
  entire paper. No theorem of this paper is imported without a proof here.
- Narváez-Macarro and Tirado Hernández, *On the bracket of integrable
  derivations*, arXiv:1912.11635 (2019).
  https://arxiv.org/abs/1912.11635
  Bibliographic record and abstract-level context were consulted.
- Bagayoko, *A formal Lie correspondence*, arXiv:2604.04224v1 (5 April 2026).
  https://arxiv.org/abs/2604.04224
  The current primary arXiv abstract was checked. An HTML full-text access
  attempt failed; a full-paper review is not claimed. It is cited for broader
  context, not for any specific omnific conclusion.
- The Stacks Project, Section 53.12, “Riemann–Hurwitz,” tag 0C1B.
  https://stacks.math.columbia.edu/tag/0C1B
  The official statement and discussion were consulted. The article gives
  the specific genus-one argument and explains finite-witness descent.
- Hirano, *On the uniqueness of rings of coefficients in skew polynomial
  rings*, Publications Mathematicae Debrecen 54 (1999), 489–495.
  https://doi.org/10.5486/PMD.1999.2085
  The primary PDF was consulted for strong-invariance terminology and
  historical context only.

The user-supplied Wikipedia page was consulted for orientation, not used as the
technical authority for the new proofs:
https://en.wikipedia.org/wiki/Surreal_number

This was a targeted source comparison, not an exhaustive priority search.
No external referee, journal decision, or formal verification is implied.

## Proof and computation boundaries

The written proof has three main independent branches:

- uniquely divisible ideals and T-adic operator algebra;
- positive-genus rational-function rigidity;
- set-sized supports and fresh inner-exponent coordinates.

Their interaction is explained in the article's dependency appendix.
The full surreal statements explicitly handle the set–class distinction:
collections of class maps are external, each normal-form support and each
formal sequence is a set, and no proper-class summation is used.

`code/verify.py` is an exact-rational finite regression suite in
`A0 = Z + X Q[X]`. The delivered run passed 1,576 checks. These checks do
not prove general summability, completeness, real closedness, genus,
nondefinability, or any quantification over all class maps. They verify finite
operator signs, factorials, truncations, and the explicit jet witnesses.

No actual-surreal evaluation of the external formal variable is asserted.
The formula for polynomial coefficients contains the inequation b != 0;
positive-existential definability is not claimed. The surcomplex-field
completion has a parity exception, treated separately. The nondefinability
of a coefficient section does not prevent interpretation of the residue ring
as a quotient.
