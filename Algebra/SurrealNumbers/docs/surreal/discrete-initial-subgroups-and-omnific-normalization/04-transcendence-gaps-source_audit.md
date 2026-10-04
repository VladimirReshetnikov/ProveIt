# Source and novelty audit

Research manuscript dated October 3, 2026. This audit records which mathematical
sources support the article and what was not verified. It is not an exhaustive
literature search or a certificate of novelty.

## Research-interest match

The intersection is established by Glazer's own mathematical work on explicit
models of arithmetic, together with his credited contribution to transcendence
over set-theoretic real subfields. It does not rely on employment-profile
metadata or infer mathematical claims from the supplied LinkedIn page.

### Glazer: standard systems

Elliot Glazer, *Explicit models of arithmetic do not have full standard system*,
MOPA seminar, February 27, 2024.

- Announcement: https://nylogic.github.io/mopa/2024/02/27/explicit-models-of-arithmetic-do-not-have-full-standard-system.html
- Slides: https://nylogic.github.io/files/GlazerSlides022024.pdf

The 22-slide text was consulted; slide 4 was also inspected as a rendered page
to verify the quantifiers, Borel-quotient superscript, and arithmetic strength.
The manuscript uses the ordinary Borel-model corollary of the no-full-standard-
system theorem and does not reprove it. The new arithmetic coding arguments
use full PA, so the seminar's EFA and reverse-mathematical strength are not
silently inherited by the new deductions.

### Glazer: topology

Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1 (2023).

https://arxiv.org/html/2311.13699v1

Used to document the research overlap with automatic continuity and arithmetic
presentations. Its unresolved questions are not claimed solved by this article.

## Close prior work included in the novelty check

### Fatalini–Schindler and the Glazer/de Bondt observation

Azul Fatalini and Ralf Schindler, *The transcendence degree of the reals over
certain set-theoretical subfields*.

https://arxiv.org/html/2412.00616v2

DOI: https://doi.org/10.1017/jsl.2025.19

The initial search located v1; the final audit checked v2, revised January 12,
2026, and the bibliography now identifies v2. Section 2, especially Proposition
2.4 and Corollary 2.5, is the relevant comparison. The introduction and Section
2 explicitly credit independent observations of Ben de Bondt and Elliot Glazer
about extensions adding any new real. The paper's “really closed” hypothesis
is not the same as the analytic relative algebraic closure hypothesis here.
The manuscript does not reproduce or claim the finite-Cohen-real main theorem.
The correction to the source paper's later implicit-function proof is not a
dependency of our arguments.

### Ye–Yu–Zhao

Jinhe Ye, Liang Yu, Xuanheng Zhao, *When is A+xA=R*.

https://arxiv.org/html/2505.00556v2

DOI: https://doi.org/10.1017/jsl.2026.10232

The May 10, 2026 preprint version and the publisher's 2026 online publication
information were consulted. Proposition 2.6 treats analytic proper subfields
of R and Q_p and maximality while omitting a chosen point. This is explicitly
recognized as nearby work. Our countable-basis derivation argument is written
out independently; the comparison does not establish historical priority.

### Edgar–Miller

G. A. Edgar and Chris Miller, *Hausdorff Dimension, Analytic Sets and
Transcendence*, author preprint dated June 8, 2001.

https://math.osu.edu/~edgar/preprints/miller/hdimpre.pdf

The proper analytic real-closed-subfield dimension-zero theorem is used only
as an attributed consequence. The article's perfect-gap proof does not depend
on the dimension theorem, and no p-adic dimension-zero result is inferred.

## Classical inputs

- Jan Mycielski, *Independent sets in topological algebras*, Fundamenta
  Mathematicae 55 (1964), 139–147, DOI 10.4064/fm-55-2-139-147. The operative
  countable-family, finite-arity meager-relation formulation was checked in
  Theorem 1 of the primary research paper by Martin Doležal and Wiesław Kubiś:
  https://arxiv.org/html/1510.05127v1 . The original Mycielski PDF was not
  successfully fetched; no claim of reading that original PDF is made.
- Angus Macintyre, *On definable subsets of p-adic fields*, JSL 41 (1976),
  605–610, DOI 10.2307/2272038. Quantifier elimination in the power-predicate
  language is an external input. The local-constancy/Tarski–Vaught deduction
  used for the coefficient field is supplied in the article.
- Alexander S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
  is the standard reference for analytic regularity and category facts. No
  claim is made of a new proof of the full background theory. The specific
  analytic-graph characterization of the derivation is supplied explicitly.
- Alessandro Berarducci, Salma Kuhlmann, Vincenzo Mantova, and Mickaël
  Matusinski, *Exponential fields and Conway's omega-map*, arXiv:1810.03029v2:
  https://arxiv.org/html/1810.03029v2 . Author names and the normal-form/Hahn
  framework were checked. Only the set-sized rational-exponent Hahn slice
  is used for the actual surreal application, not a global proper-class
  Hahn field treated as a set.

## ProveIt: exact repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `7d9b8b957fa6a1cc28636ac8fce3cfaa6d230031`.

Repository material was accessed through the GitHub connector. The relevant
inspected documentation is:

1. `Algebra/SurrealNumbers/README.md`

   https://github.com/VladimirReshetnikov/ProveIt/blob/7d9b8b957fa6a1cc28636ac8fce3cfaa6d230031/Algebra/SurrealNumbers/README.md

   Relevant claims: constructed normal forms, omnific constant extraction,
   finite quotients, p-adic completion and its canonical image. The README's
   distinction between formalized foundations and AI-assisted unrefereed
   reports is retained. These source statements motivate the bridge; the
   elementary tail-ring arguments actually needed here are reproved.

2. `Logic/PeanoArithmetic/ListCoding/README.md`

   https://github.com/VladimirReshetnikov/ProveIt/blob/7d9b8b957fa6a1cc28636ac8fce3cfaa6d230031/Logic/PeanoArithmetic/ListCoding/README.md

   Relevant claims: genuine PA formulas for finite codes and digits. The
   explicit boundary between standard-natural evaluation and internal PA
   derivability is important. Our nonstandard proof requires the latter;
   the formalization plan identifies that obligation rather than treating
   the standard-model documentation as an existing formal proof of it.

The root README and directory/commit metadata were also consulted for
navigation. Neither all repository reports nor all formal source files were
reviewed. No Lean/Rocq build, kernel audit, or independent verification of the
repository's broad research claims was performed in this task.

## What the search supports

The evidence supports a direct mathematical intersection and identifies close
prior results that must be credited. The manuscript supplies a proposed unified
arithmetic-to-local-field-to-Hahn theorem, including exact profinite images
and Boolean reconstruction from idempotents, with explicit ordinary proofs and
scope boundaries. It does **not** support a claim that every lemma is new, that
the package is peer reviewed, or that a famous published open problem has been
conclusively resolved. The eleven final questions are explicitly questions
arising from this manuscript, not an invented list of established open problems.

No third-party source PDFs, private account material, or font files are included
in this package. The links above are for provenance.
