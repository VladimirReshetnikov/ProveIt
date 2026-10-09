# Source and novelty audit

Access date: October 8, 2026. Sources were consulted as primary mathematical publications, author-hosted text, or the original repository. No third-party summary is used as a technical lemma.

## Classical background

1. F. R. K. Chung, R. L. Graham, R. M. Wilson, *Quasi-random graphs*, Combinatorica 9(4), 345-362 (1989), DOI 10.1007/BF02125347.
   Author-hosted PDF: https://mathweb.ucsd.edu/~ronspubs/89_05_quasi_graphs.pdf
   Role: original quasirandomness framework. The scanned introduction was visually inspected. The present article proves the quantitative kernel claims it needs rather than attributing its constants to this source.

2. D. Conlon, J. Fox, B. Sudakov, *Hereditary quasirandomness without regularity*, Math. Proc. Cambridge Philos. Soc. 164(3), 385-399 (2018); arXiv:1611.02099.
   Author-hosted PDF: https://www.its.caltech.edu/~dconlon/hereditary.pdf
   Preprint record: https://arxiv.org/abs/1611.02099
   Role: Section 4 discusses quantitative forcing, the balanced two-block girth obstruction, and the even-cycle exponent. This supplies the explicit novelty boundary: the fourth-root exponent and balanced construction are not new. The global count condition must not be confused with hereditary count conditions.

3. W. T. Gowers, *A quasirandomness implication*, November 10, 2018.
   https://gowers.wordpress.com/2018/11/10/a-quasirandomness-implication/
   Role: analytic/bipartite perspective. The post is not cited as a source for the new higher-order envelope.

## Supplied repository

4. https://github.com/openai/math
   README blob SHA inspected: 50feb63d396138f30dc1ff1e0af121d0263bf5a3.
   The README says the collection contains manuscripts at differing verification stages and warns that unformalized results may have issues. That warning is respected: no repository theorem is assumed here.

5. Repository manuscript folder:
   https://github.com/openai/math/tree/main/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026
   Specific source inspected: `build/sections/introduction.tex`, lines 1-110.
   Blob SHA: 32890ea14c106eeb0556da93226165ac93739371.
   Role: finite-kernel subgraph densities and passage to simple finite graphs as methodological inspiration. Its headline claimed counterexample is not verified or relied upon. No copy of its source or PDF is redistributed in this package.

## Search scope and limits

Queries included combinations of “four-cycle”, “cut norm”, “sharp”, “quasirandomness”, and “higher order”, together with searches for the original quasirandomness and quantitative forcing literature. The inspected sources did not identify the exact local analytic envelope, its higher-order coefficients, or the equality classification in the indicator-set normalization proved in this manuscript. This is a targeted search, not an exhaustive priority investigation. Failure to find a prior statement cannot establish novelty.

## Claims deliberately avoided

No claim is made that the optimal exponent 1/4 is new, that the method is an algorithmic speedup for arbitrary graph cut norms, that a major named conjecture has been solved, that the supplied repository's claimed Sidorenko counterexample is correct, or that this manuscript has been peer reviewed or formally verified.
