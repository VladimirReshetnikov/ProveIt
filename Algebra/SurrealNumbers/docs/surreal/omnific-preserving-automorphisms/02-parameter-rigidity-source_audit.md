# Source and novelty audit

## Scope and date

Prepared 23 September 2026 for the request to develop new results about
surreal numbers, surcomplex numbers, and omnific integers using the
VladimirReshetnikov/Surreal repository. The article selects a new theorem
package rather than claiming to settle a named factorisation conjecture.

Repository comparison snapshot:
`fb5c4b530e3ec04b5661347d51d5382526d5aa02`.

## Repository material actually inspected

The repository metadata, documentation catalogue (`docs/README.md`), root
README portions, the first 220 source lines of the principal omnific
Diophantine-geometry manuscript, the first 220 lines of the universal
set-sized-quotient manuscript, and the latter report's README were read.
The two principal manuscript reads were pinned to the commit above.
Directory listings were used to identify the relevant reports.

This was a targeted comparison. It was not a full read or mathematical
audit of the entire 51-report collection, the eleven incoming source
manuscripts mentioned in the catalogue, or every Lean declaration.
GitHub code search returned no matches for a trial combined query; this
was not treated as evidence of absence from the repository.

The quotient and Diophantine reports were used to distinguish the present
subject from their existing results. No new theorem in either draft is
used as a logical premise. The present proof uses standard normal-form
and Hahn support arithmetic, followed by the full arguments in the article.

## Literature

- L'Innocente and Mantova, *A factorisation theory for generalised power
  series and omnific integers*, arXiv:1710.07304v5, published in Advances
  in Mathematics 442 (2024), 109513. Primary article consulted for normal
  forms, support arithmetic context, and the existing infinite quotient
  example involving omega+1.
- Hirano, *On the uniqueness of rings of coefficients in skew polynomial
  rings*, Publ. Math. Debrecen 54 (1999), 489–495. The publisher PDF and
  its rendered first page were inspected for strong-invariance terminology.
  No theorem from that article is invoked as a black box in our proofs.
- Chitayat and Daigle, *On the rigidity of certain Pham–Brieskorn rings*,
  arXiv:1907.13259. Primary metadata and the rigidity framework were
  consulted. Our paper does not address their specific conjecture.
- Kaplan, Krapp, and Serra, *Decomposing the automorphism group of the
  surreal numbers*, arXiv:2509.22374v3. Primary HTML consulted for
  class-function conventions and the established character-automorphism
  and derivation setting.
- Conway and Gonshor are cited as classical background references;
  no fresh cover-to-cover review of those monographs was undertaken.

The bibliography in article.tex supplies full bibliographic details and
clickable source locations. Search terms included omnific + cancellation,
omnific + polynomial rings, omnific + locally nilpotent, strongly
invariant rings, infinitely divisible + strongly invariant, and surreal
automorphisms. Searches did not locate the principal omnific statements
in the form presented here. Search incompleteness prevents a priority
claim. Search results about other claimed conjecture resolutions were
not audited, imported, or represented as established here.

## Proposed contribution versus standard machinery

Proposed contribution: the linked omnific/Hahn-integer package of
coefficient-preserving embeddings, strong cancellation, finite-type
embedding rigidity, stable locally nilpotent rigidity, and
nonalgebraizable formal directions; the exact monomial orbit-field
transcendence formula makes the contrast quantitative.

Not claimed new: normal-form definitions, Hahn inverses, strong-invariance
terminology, the general Makar-Limanov framework, ordinary Euler derivations,
formal exponential identities, Vandermonde independence, or character twists.
The abstract ring arguments may have prior generalizations not located by
this targeted search. The manuscript therefore uses “proposed” originality.

## Verification boundary

All central deductions have conventional mathematical proofs in the article.
There was an additional manual proof review of the finite-type constants
lemma, injectivity assumptions, Laurent degree argument, cancellation
hypotheses, formal factorial division, formal orbit-field formula, and the
set-versus-class distinctions. The pointed finite-type parameter theorem
was strengthened in review: the augmentation alone forces its algebraic
constant field to equal the base field; no relative-algebraic-closure
hypothesis on the whole fraction field is needed.

`verify.py` uses exact rational arithmetic. Its 7,041 passing assertions
check finite coefficient identities and Vandermonde determinants only.
They do not verify quantified infinite support statements, cancellation,
class arguments, or theorem novelty. No Lean formalization was produced
or run for these results. No peer review is claimed.

The included build audit reports the actual PDF build and visual inspection,
not proof-assistant verification. Source papers, repository originals,
and font files are not redistributed in this archive.
