# Public mathematical sources and computational scope

These references identify the public sequence definitions and relevant
literature. No external resource is required for offline replay. The full
foundation proof is included unchanged as source and PDF in
foundation141/. Report142 extends that foundation; it makes no claim
of worldwide novelty or priority for its methods.

1. OEIS A258219, https://oeis.org/A258219 and
   https://oeis.org/A258219/internal. Weighted Dyck paths use the peak
   factor (x+k y)/y. The record includes Peter Bala's comment dated
   2022-07-28 concerning the Riccati identity and continued fraction.
2. OEIS A258220, https://oeis.org/A258220 and
   https://oeis.org/A258220/internal. The Newton transformation is
   Delta^m p_N(0)/m!, and the diagonal T(2n,n) is A292692.
3. OEIS A292692, https://oeis.org/A292692 and
   https://oeis.org/A292692/internal. The numerical asymptotic form and
   conjectural algebraic rate are attributed in that record to Vaclav
   Kotesovec, 2024-03-17. Its public data file is
   https://oeis.org/A292692/b292692.txt. Report142's new coefficient
   computation neither reads these values nor fits to them. Report141
   discusses separately labeled exact and diagnostic data. No numerical
   source-data fixture is included in this continuation bundle.
4. R. J. Martin and M. J. Kearney, “An exactly solvable self-convolutive
   recurrence,” Aequationes Mathematicae 80 (2010), 291–318,
   https://arxiv.org/abs/1103.4936. Section 2.4, Theorem 3 concerns relevant
   fixed-parameter Gamma asymptotics. A fixed-parameter result alone does
   not establish the proportional-index Newton-coefficient expansion.
5. Michael Borinsky, “Renormalized asymptotic enumeration of Feynman
   diagrams,” https://arxiv.org/abs/1703.00840. Section 6.4.1 and Table 10
   give relevant fixed-theory/source asymptotic expansions. They provide
   context for asymptotic methods, not a substitute for the particular
   proportional-ratio argument in Report142.
6. SymPy project documentation, https://docs.sympy.org/latest/index.html.
   code/second.py uses exact rational symbolic operations and derivatives;
   the tested version is 1.14.0. code/finite.py uses only Python standard-
   library exact arithmetic and has an independent saddle implementation.

The article proves a fixed-order expansion on compact subsets of the open
interior ratio range. It does not include either endpoint, convergence of
the formal asymptotic series, uniformity for a growing number of terms,
effective remainder constants, or a finite numerical threshold certificate.
The inverse conclusion is a bracket with uncertainty inside ceilings.

All new computational sources and exact fixtures in this companion are
self-contained. The complete external OEIS pages, data files and papers are
not redistributed; their original authorship and licensing remain intact.
