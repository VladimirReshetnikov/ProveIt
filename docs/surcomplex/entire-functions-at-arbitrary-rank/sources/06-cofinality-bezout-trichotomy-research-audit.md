# Research and source audit

## Repository snapshot and scope

Repository: https://github.com/VladimirReshetnikov/Surreal

Final source-check commit:
`4896a2808ce30e01b1c86ae3ba2295a64762d246`

This is the actual commit returned by the GitHub branch API, not a tree or
blob identifier. The working branch changed during preparation. The four
files below were re-read at this fixed commit, and the article's repository
links are pinned to it.

| Read file | Blob identifier |
|---|---|
| README.md | 204eaef4ca14e39afd2670c4f60c79d9877a97ae |
| docs/README.md | 13153d81c980852c65563ce68458b95142b9cd2a |
| docs/surcomplex/rank-one-berkovich/README.md | 105aef397dad2194bf357a61e86ded0267520a66 |
| docs/surcomplex/global-divisors/README.md | 3607292c39873b09cc63f4381ac05ce03b20d5dc |

The review was targeted at the catalogue, the relevant report descriptions,
and their declared mathematical categories. It was **not** a line-by-line
proof audit of all manuscripts or an independent build of the repository.

The rank-one report already treats preparation, zeros, and a partial-theta
canonical product over C((t^R)). Those topics are credited, not presented as
absent from the repository. The global-divisor report treats Hahn series with
ordinary holomorphic coefficients on a common complex domain. Its divisor,
interpolation, and Picard obstructions are in a different function ring from
the strongly entire ring in the new article.

The root README reports finite algebra and Hahn support formalizations. Those
are identified as potential prerequisites; they do not formally verify the
new results. Missing implementation is not treated as an open mathematical
problem.

## Primary literature used

1. B. Poonen, *Maximally complete fields*, L'Enseignement Mathématique (2) 39
   (1993), 87–106. Author's text:
   https://math.mit.edu/~poonen/papers/amsval.pdf
   The support constructions and Corollary 4 are the relevant inputs.

2. W. Cherry, *Existence of GCD's and factorization in rings of non-Archimedean
   entire functions*, Contemporary Mathematics 551 (2011), 57–69.
   https://arxiv.org/abs/1007.0984v2
   The paper explicitly records classical one-variable product factorization
   and gives GCD/factorization results for complete real-valued
   non-Archimedean fields. Those results are antecedents, not new claims here.

3. J. van der Hoeven, *Operators on generalized power series*, Illinois
   Journal of Mathematics 45 (2001), no. 4, 1161–1190.
   https://www.texmacs.org/joris/noeth/noeth.html
   This is the generalized-series operator and support-control antecedent.
   The article gives its own explicit preparation recursion.

4. M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps
   valué complet*, Publications Mathématiques de l'IHÉS 14 (1962), 47–75.
   https://www.numdam.org/item/PMIHES_1962__14__47_0/
   The bibliographic record was checked. This is a historical reference,
   not a claim that the full paper was proof-audited during preparation.

5. M. Aschenbrenner, L. van den Dries, and J. van der Hoeven,
   *On numbers, germs, and transseries*.
   https://arxiv.org/abs/1711.06936
   Used to cross-check the Conway/Gonshor bibliography and standard surreal
   background. The Conway and Gonshor books were not re-audited in full.

General web searches were also attempted; several returned irrelevant
results. Those were not treated as evidence of absence. No exhaustive
bibliographic novelty search or independent expert assessment was performed.

## Novelty ledger

The principal proposed original contribution is the explicit arbitrary-rank
failure of the Bézout property (Theorem 7.4), and the cofinality–rank
classification built from it (Theorem 1.2). The exact strong-summability
criterion (Theorem 3.1), workspace-extension criterion (Theorem 10.1), and
persistence of the obstruction (Corollary 10.2) are additional proposed
contributions. Their precise combination was not located in the primary
sources examined.

The rank-one factorization specialization is classical. Standard Hahn field
algebra, algebraic closedness, finite polynomial algebra, and support lemmas
are not claimed as original. All-surcomplex polynomial rigidity is credited
to the repository's pre-existing all-scale theme, not claimed as an
independently new conclusion.

No named published conjecture is claimed solved. A future discovery of an
antecedent would change the priority discussion, not the displayed statement
or its proof. The newly posed research questions in Section 11 are explicitly
questions arising from this work, not falsely attributed to existing papers.

## Mathematical and computational assurance

The article includes full mathematical arguments and a proof-dependency and
hypothesis audit. In particular, it distinguishes strong Hahn summation from
valuation convergence, checks attained minima where strict inequalities are
needed, and does not assume that a fixed positive exponent has cofinal
integer multiples in an arbitrary ordered group.

The finite verification program passed 831/831 assertions, including a second
run after the final source check. It uses exact rational arithmetic. It is
not a proof assistant and does not establish the infinite theorems. No
independent referee or Lean kernel has checked these proofs.

The final PDF was compiled, all 26 pages rendered and visually inspected,
and all extracted text spans checked against page bounds. The final log has
no errors, undefined references/citations, or overfull/underfull box warnings.
These are document checks, not mathematical certification.
