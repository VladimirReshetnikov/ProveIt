# Source notes and provenance

Inspected on 29 September 2026.

## Repository sources actually used

Repository:
https://github.com/VladimirReshetnikov/ProveIt

Principal group README:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/Transseries/docs/series-and-transseries/README.md

Closest inspected comparison:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/Transseries/docs/series-and-transseries/Action_Accumulation_Nonlinear_Inversion/README.md

The last source discusses action-measure inversion, hidden oscillations,
Poisson–Bessel formulas, and Hardy-field obstructions. Its editorial notes
explicitly distinguish those results from the canonical open realization
question labelled `plt:rmk:ext-open-realization`. The present article respects
that scope boundary; a positive-measure identifiability theorem is not a
realization of every left-finite Hahn element.

The Transseries subtree listing retrieved through GitHub had tree SHA
`81058854a185ab903d9012f6de6f93da345b31d6`. This identifies the inspected
listing, not a fully downloaded or audited repository. The live path was
`Analysis/Transseries`, rather than earlier paths under FabiusFunction.

An indexed GitHub code search for `Stieltjes` restricted to the Transseries
path returned ten matches; `Wigert` returned zero. The search output used
index ref `9250bbf8af80dacf7b252d9d0320b122c80961ba`. That is a search-index
reference, not asserted to be the current repository HEAD. Searches are not
proofs of novelty or completeness. The canonical volumes and every sibling
research article were not read theorem by theorem.

## Primary mathematical references

- G. D. Lin and J. Stoyanov, *Moment Determinacy of Powers and Products of
  Nonnegative Random Variables*, Journal of Theoretical Probability 28
  (2015), 1337–1353. DOI: 10.1007/s10959-014-0546-z.
  https://arxiv.org/abs/1403.0301
  Used for the classical Hardy/Carleman and generalized gamma context. The
  author manuscript and the pertinent pages were inspected. The needed
  factorial-square criterion is proved directly in the article.

- T. S. Chihara, *A Characterization and a Class of Distribution Functions
  for the Stieltjes–Wigert Polynomials*, Canadian Mathematical Bulletin 13
  (1970), 529–532. DOI: 10.4153/CMB-1970-098-7.
  Classical provenance for the Stieltjes–Wigert moment setting.

- J. S. Christiansen, *The moment problem associated with the Stieltjes–Wigert
  polynomials*, Journal of Mathematical Analysis and Applications 277
  (2003), 218–245. DOI: 10.1016/S0022-247X(02)00534-6.

- J. S. Christiansen and E. Koelink, *Self-adjoint difference operators and
  classical solutions to the Stieltjes–Wigert moment problem*, Journal of
  Approximation Theory 140 (2006), 1–26.
  DOI: 10.1016/j.jat.2005.11.010.

- L. Di Vizio and C. Zhang, *On q-summation and confluence*, Annales de
  l'Institut Fourier 59 (2009), 347–392. DOI: 10.5802/aif.2433.
  https://arxiv.org/abs/0709.1610
  Used for the distinction between specified q-summation procedures and
  arbitrary positive-real realizations, not to identify our families with
  a canonical sum.

- N. Nikolaev, *Gevrey asymptotic implicit function theorem*,
  L'Enseignement Mathématique 70 (2024), 251–282.
  DOI: 10.4171/LEM/1061.
  https://ems.press/journals/lem/articles/13969317
  Used to distinguish a sectorially selected summable implicit function
  from the present coefficient-plus-positivity realization question.

- NIST DLMF, Chapter 17, Section 17.8:
  https://dlmf.nist.gov/17.8
  Classical Jacobi triple product. The exact normalization used here is
  explicitly fixed in equations (5.6)–(5.7).

## Attribution and limits

The existence of moment-indeterminate gamma and Stieltjes–Wigert measures,
the order-two determinacy guarantee, Lagrange inversion, and Jacobi's
identity are not claimed as new. The article gives self-contained proofs
of its specific constructions and quantitative nonlinear conclusions,
using classical background as stated. No exhaustive priority claim is made
for equivalent formulations of those conclusions.

Only original article and support files are distributed. No external paper
has been copied into the package, and the GitHub repository was not modified.
