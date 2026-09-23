# Source audit and scope

## Repository snapshot

Repository: VladimirReshetnikov/Surreal
Commit: bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59
Comparison date: 23 September 2026

Primary file:
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`

Blob: 86fc4925b4c3997b984894e6b4756e327f27a4c6

Pinned source:
https://github.com/VladimirReshetnikov/Surreal/blob/bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59/docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex

Inspected portions included lines 1–180, 2000–2320, 2340–2570, and 4100–4360.
The relevant question and its explanatory status paragraph were present in the
returned later excerpt. Some responses were truncated after relevant content;
no absence claim is based on their unreturned portions.

Exact comparison labels:
- `hol:q:mixedunit`: the unresolved mixed unit-valuation case, with an order unit.
- `hol:thm:mixed`: existing mixed rigidity at a nonzero noncofinal valuation.
- `hol:q:severaldilations`: the several-dilation research direction.
- `hol:q:nonlinear`: the separate nonlinear order-unit question left unresolved.

The repository already treats pure differential and cyclic pure dilation
rigidity, partial theta, escape chains, and stronger nonlinear statements
without an order unit. These are not claimed as new in this manuscript.

## Contributions claimed within the manuscript

- A proof of eventual periodic-affine valuations for Hahn-valued exponential
  polynomials with arbitrary well-ordered coefficient supports.
- The estimate for v(P(n,q^n)) at a nontorsion valuation-zero q, which supplies
  the precise missing step identified by the repository.
- An affirmative answer to `hol:q:mixedunit`, with additional uniformity and
  polynomial-forcing statements.
- An exact existential mixed-linear criterion for a finite prescribed dilation
  set, under exclusion of actual root-of-unity ratios: one cofinal relative
  valuation is necessary and sufficient.
- An explicit witness using two prescribed dilations and first derivatives.

The finite-set criterion addresses an existential portion of the repository's
several-dilation direction; it does not classify all specified operators or
simultaneous systems.

## Literature and its role

- C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417–421.
  DOI: 10.1007/BF02590997. Primary reference for the characteristic-zero SML
  theorem. Bibliographic metadata was verified; the detailed accessible account
  consulted was Bell's chapter below.
- J. P. Bell, The Skolem–Mahler–Lech theorem, Documenta Mathematica, Extra Volume
  Mahler Selecta (2019), 173–178. The accessible PDF was read, including visual
  inspection of the first two pages. The imported theorem and its formulation
  over arbitrary characteristic-zero fields were checked there.
  https://ems.press/content/book-chapter-files/27398
- B. H. Neumann, On ordered division rings, Trans. Amer. Math. Soc. 66 (1949),
  202–252. DOI: 10.1090/S0002-9947-1949-0032593-5. Foundational attribution for
  support calculus; the required support lemma is proved in the manuscript.
- C. Fuchs and S. Heintze, On the growth of linear recurrences in function
  fields, Bull. Aust. Math. Soc. 104 (2021), 11–20.
  DOI: 10.1017/S0004972720001094. The author version and publisher metadata were
  consulted as related work; their result is not an input to our proof.
  https://arxiv.org/abs/2006.11074
- H. Gonshor, An Introduction to the Theory of Surreal Numbers, Cambridge
  University Press, 1986. DOI: 10.1017/CBO9780511629143. Standard normal-form
  background; publisher metadata was checked. No claim of rereading the full
  monograph is made.
- H. Derksen, A Skolem–Mahler–Lech theorem in positive characteristic and finite
  automata, Invent. Math. 168 (2007), 175–224. Background for a proposed
  positive-characteristic direction, not an input to any new proof here.
  https://arxiv.org/abs/math/0510583

The user's Wikipedia reference was consulted for general orientation; no new
technical theorem relies on it. Literature searches were targeted, not an
exhaustive historical-priority audit.

## Proof-review priorities

1. Finiteness of all contributing word lengths at a fixed Hahn exponent.
2. Selection of the least coefficient sequence which is not identically zero,
   rather than an invalid maximum over infinitely many exceptional indices.
3. Eventual affine comparisons in arbitrary rank, where the smallest slope
   need not win.
4. The exact derivative/dilation order and shifted coefficient index.
5. Relative rather than absolute dilation valuations in the cost estimate.
6. The existential quantifiers in the two-dilation sufficiency construction.

## Explicit non-claims

No independent referee report, no Lean formalization, no first-principles
proof of SML, no certified novelty, no solution of the general nonlinear
order-unit problem, no unconditional torsion-block theorem, no general
algorithm for arbitrary surreal input, and no nonpolynomial series entire on
the full proper class No[i]. Omnific integers enter as permissible coefficients,
not through a newly claimed factorization or definability theorem.
