# Source and novelty audit

Review date: September 21, 2026. This is a targeted review, not an exhaustive
bibliographic or priority certification. No external articles are redistributed
in this package.

## Motivating repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `39f2be6667ade51bca2b45daa47e289d69c09764`.

The review used the repository tree, `docs/README.md`, the READMEs for
`docs/surcomplex/analysis/` and `docs/surcomplex/analytic-geometry/`, and the
opening framework of the analytic-geometry article (source lines 1–210).
These establish the project's existing coverage and its distinction between
fixed domains, common-domain germs, radius-free germs, and formal coefficients.
A connector search for `linearization` returned no indexed matches. This is
recorded as a limited search result, NOT proof that no file in the repository
contains any related observation. The entire repository was not line-by-line
audited, and its Lean library was not built for this task.

No unrefereed repository theorem about Noetherianity, the Nullstellensatz,
residues, or global analytic geometry is an input to the proofs here.

## Primary literature and its role

**Graham Higman (1952), Ordering by Divisibility in Abstract Algebras.**
Proceedings of the London Mathematical Society (3) 2, 326–336.
DOI: https://doi.org/10.1112/plms/s3-2.1.326
The classical word well-quasi-order theorem supplies the support lemma.
Appendix A proves the special case used. Neither this theorem nor Neumann's
support lemma is claimed new.

**Bjorn Poonen (2026), Units in Hahn–Mal'cev–Neumann rings.**
Manuscript dated January 14, 2026, 4 pages.
https://math.mit.edu/~poonen/papers/malcev.pdf
The positive-support geometric-series and unit framework is classical;
Poonen's account provides a recent precise source. The manuscript's date and
its unit theorem were checked directly. It is cited as a manuscript, not given
an invented journal publication.

**Javier Ribón (2012), Embedding smooth and formal diffeomorphisms through the
Jordan–Chevalley decomposition.**
Journal of Differential Equations 253(12), 3211–3231.
https://doi.org/10.1016/j.jde.2012.09.009
https://arxiv.org/abs/1107.3601
A close predecessor for formal logarithms, flow embedding, and finite-order/
unipotent decompositions. Those mechanisms are not new claims here. The
candidate contribution is their arbitrary-Hahn-support, same-coefficient-domain
implementation and the consequences proved from it.

**Timoteo Carletti and Stefano Marmi (2000), Linearization of analytic and
non-analytic germs of diffeomorphisms of (C,0).**
Bulletin de la Société Mathématique de France 128(1), 69–85.
https://www.numdam.org/articles/10.24033/bsmf.2363/
https://doi.org/10.24033/bsmf.2363
A close predecessor for formal versus analytic linearization, arithmetic
conditions, and regularity classes. Appendix A is also a source for the
continued-fraction estimates. The diagonal cohomological operator is classical.

**Jean-Christophe Yoccoz (1995), Théorème de Siegel, nombres de Bruno et
polynômes quadratiques.**
In Petits diviseurs en dimension 1, Astérisque 231, 3–88.
https://smf.emath.fr/publications/petits-diviseurs-en-dimension-1
The publisher's excerpt confirms the article title and its start on printed
page 3; the digital archival wrapper includes front matter in its page range.
The quadratic Brjuno theorem is an external classical input, not a result
claimed proved in this manuscript.

**Xavier Buff and Arnaud Chéritat (2004), The Brjuno function continuously
estimates the size of quadratic Siegel disks.**
https://arxiv.org/abs/math/0401044
The author abstract explicitly recalls Yoccoz's equivalence between the Brjuno
condition and linearizability of the irrationally indifferent quadratic.
This supplies an additional precise primary-source statement of the comparison
used in Section 10. We cite the preprint without guessing later metadata.

**Alessandro Berarducci and Vincenzo Mantova (2019), Transseries as germs of
surreal functions.**
Transactions of the American Mathematical Society 371, 3549–3592.
https://doi.org/10.1090/tran/7428
https://arxiv.org/abs/1703.01995
Relevant surreal analytic background. The coordinate derivatives in the present
article are not the authors' surreal-field derivation, and no global
composition on all surreals is inferred from their work.

**Raf Cluckers and Leonard Lipshitz (2011), Fields with analytic structure.**
Journal of the European Mathematical Society 13(4), 1147–1223.
https://ems.press/journals/jems/articles/3467
https://doi.org/10.4171/JEMS/278
Broad valued-field analytic background. No claim is made that the present
coefficient categories lie outside every framework treated by that paper.

## Proposed originality and its limits

The specific candidate-new package is Theorem 1.1 with Sections 8–10:
sharp universal linearization criteria for the five coefficient categories,
finite dependence at each arbitrary Hahn weight, radius/degree certificates,
first-weight necessity examples, and the explicit arithmetic and critical-scale
separations. The same-domain versions of the flow, fixed-ideal, centralizer,
and finite-order normal-form theorems support that package.

Searches included Hahn/surcomplex holomorphic dynamics, linearization and small
divisors, formal logarithms and flow embedding, and the named repository. They
identified the substantial precedents above, but no exact published match to
the combined category/support classification. General search-engine absence
is weak evidence; the source comparison, rather than a count of search hits,
is the basis of the qualified novelty statement.

No named published open problem is presented as solved. Priority remains
uncertified. The general proofs are not machine-checked; the included exact
checks validate only finite algebraic identities and the displayed examples.
