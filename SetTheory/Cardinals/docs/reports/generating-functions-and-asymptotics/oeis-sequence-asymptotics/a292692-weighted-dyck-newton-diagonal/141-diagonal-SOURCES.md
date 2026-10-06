# Public provenance and scope

Sources were consulted on 2026-10-02. The package is self-contained for
replay; links below identify public definitions and prior literature.
A site's database-wide footer date is not an individual sequence edit date.

1. OEIS A258219, https://oeis.org/A258219 and
   https://oeis.org/A258219/internal. Weighted Dyck paths have peak factor
   (x+k y)/y. Peter Bala's comment dated 2022-07-28 records the conjectural
   Riccati identity and continued fraction addressed by the article.
2. OEIS A258220, https://oeis.org/A258220 and
   https://oeis.org/A258220/internal. The Newton transformation uses
   Delta^m p_N(0)/m!, with diagonal T(2n,n)=A292692.
3. OEIS A292692, https://oeis.org/A292692 and
   https://oeis.org/A292692/internal. The numerical asymptotic form and
   conjectural algebraic rate are attributed there to Vaclav Kotesovec,
   2024-03-17. The data file is
   https://oeis.org/A292692/b292692.txt. Its terms n=0 through 10 are
   independently recomputed by code/exact.py. Its selected terms at
   n=40,80,160,290 are embedded explicitly in code/replay.py only for
   normalization diagnostics. The latter values are not claimed to be
   independently enumerated in this package.
4. R. J. Martin and M. J. Kearney, "An exactly solvable self-convolutive
   recurrence," Aequationes Mathematicae 80 (2010), 291-318;
   https://arxiv.org/abs/1103.4936. The inspected Section 2.4, Theorem 3,
   gives relevant fixed-parameter Gamma asymptotics. Such a statement does
   not alone justify a Newton coefficient index growing proportionally
   with the main index.
5. Michael Borinsky, "Renormalized asymptotic enumeration of Feynman
   diagrams," https://arxiv.org/abs/1703.00840. In particular Section 6.4.1
   and Table 10 provide relevant fixed-theory/source asymptotic expansions.
   No priority claim is made for the Riccati/Feynman asymptotic methods or
   fixed-parameter results.

The bounded literature/source comparison is not a worldwide novelty search.
The article gives its own complete formal bridge and diagonal argument;
finite agreement with OEIS is not its proof. The result includes exactly the
first relative correction and its O(n^-2) remainder, not an all-orders
expansion. The inverse statement is an inside-ceiling asymptotic bracket,
not an effective finite threshold certificate.

Only short mathematical data excerpts are bundled. The external OEIS pages,
b-files, and research papers retain their respective source authorship and
licensing; this package does not redistribute their complete text.
