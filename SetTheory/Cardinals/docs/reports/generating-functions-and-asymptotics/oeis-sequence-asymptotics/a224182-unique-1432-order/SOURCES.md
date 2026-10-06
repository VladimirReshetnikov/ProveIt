# Source provenance and scope

Sources were checked on October 2, 2026. No third-party paper is redistributed
in this archive. The article and executable certificate are sufficient to
replay the stated finite computations offline. The analytical inputs remain
ordinary cited mathematical theorems, not formally verified library imports.

- OEIS A224182, https://oeis.org/A224182/internal. The entry defines exactly
  one 2341, with offset 1. Reversal gives exactly one 1432. Initial terms at
  n=4,...,8 are 1, 11, 87, 625, 4378, independently reproduced here. The
  research source snapshot was read directly; it is not included as a raw
  scrape. OEIS availability can vary.
- Brian Nakamura, Approaches for enumerating permutations with a prescribed
  number of occurrences of patterns, arXiv:1301.5080 (2013), Section 3.2,
  Theorem 4 (FE2341), https://arxiv.org/pdf/1301.5080. Directly inspected.
  Provides prior exact enumeration and initial coefficients, not the present
  asymptotic proof.
- Andrew R. Conway and Anthony J. Guttmann, Counting occurrences of patterns
  in permutations, Electronic Journal of Combinatorics 32(1) (2025), P1.3,
  Section 5.3, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p3/pdf/.
  Directly inspected. They conjecture order 9^n/n^3 and the amplitude ratio
  C1/C0 approximately 0.0375, possibly 3/80. Their Section 5.5 repeats
  identifier A224182 for another class; this report uses the OEIS definition.
- Alexander Burstein, A short proof for the number of permutations containing
  pattern 321 exactly once, Electronic Journal of Combinatorics 18(2) (2011),
  P21, https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_18/PDF/v18i2p21.pdf.
  Directly inspected through the web PDF reader. The unique global-321 split
  motivates the present construction. Its extension to a supported tail is
  proved here, not assumed. An earlier failed local download was HTML and
  was not treated as a paper.
- J. Backelin, J. West, G. Xin, Wilf-equivalence for singleton classes,
  Advances in Applied Mathematics 38 (2007), 133-148, Proposition 2.2,
  https://doi.org/10.1016/j.aam.2004.11.006. Original attribution for the
  shape-Wilf result. The original conference abstract was accessible at
  https://igm.univ-mlv.fr/~fpsac/FPSAC01/SITE01/PROGRAM/62.html; the journal
  full-text retrieval failed. We do not claim to have inspected that full text.
- Christian Krattenthaler, Growth diagrams, and increasing and decreasing
  chains in fillings of Ferrers shapes, Advances in Applied Mathematics
  37 (2006), 404-431, https://arxiv.org/pdf/math/0510676 (version 2).
  Section 2, Theorems 1-3, pages 3-7 were directly checked. French/southwest
  boards, at most one point per row/column, and rectangle containment of
  decreasing chains are essential. Boundary conjugation preserves strict
  changes and therefore each occupied row/column. This is the primary
  growth-diagram proof actually used, after rotating our board 180 degrees.
- Amitai Regev, Asymptotic values for degrees associated with strips of Young
  diagrams, Advances in Mathematics 41 (1981), 115-136,
  https://doi.org/10.1016/0001-8708(81)90012-8. Fixed-strip asymptotic used
  as prior work. For the three-row class, C0=81 sqrt(3)/(16 pi).
- Toufik Mansour, Reza Rastegar, Alexander Roitershtein, Finite automata,
  probabilistic method, and occurrence enumeration of a pattern in words
  and permutations, SIAM Journal on Discrete Mathematics 34(2) (2020),
  1011-1038, https://doi.org/10.1137/19M1262206; arXiv:1905.05646v1,
  https://arxiv.org/html/1905.05646v1#S3.SS1. Theorem 3.1 proves equality
  of fixed-occurrence and avoidance exponential rates. Its proof also
  displays f_m^xi(n) <= n sum_{r<m} f_r^xi(n-1), which at m=1 would give
  the same upper order. The published author manuscript was also checked
  at https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7144682/?report=xml.
  The report does not rely on that one-step estimate and independently
  proves its own marked-split upper bound. No claim of upper-order novelty
  or worldwide priority is made.

The source check was scoped, not an exhaustive worldwide literature review.
No repository publication, outside contact, or external submission is part
of this deliverable.
