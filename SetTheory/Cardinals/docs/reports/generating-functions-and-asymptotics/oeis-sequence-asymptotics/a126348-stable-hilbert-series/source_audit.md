# A126348 source and scope audit

Checked 2026-10-01. Local mathematical research only; no publication or repository write.

## Exact sequence and mathematical relevance

https://oeis.org/A126348 defines coefficients of

F(q)=product_{k>=1}(1+q^k/(1-q)), a_0=1.

Its live page contains generating functions and a 10,000-term table but no asymptotic formula. It also describes colored compositions whose associated color partition has distinct parts.

Jianping Pan and Tianyi Yu, *Top-degree components of Grothendieck and Lascoux polynomials*, Algebraic Combinatorics 7(1) (2024), 109--135, DOI10.5802/alco.326, Proposition6.10 identifies F with the Hilbert series of the stable span of top-degree Grothendieck/Lascoux polynomials. The full paper was inspected; it has no asymptotic section or occurrence of “asympt”.
Primary full text: https://www.numdam.org/item/10.5802/alco.326.pdf

Beimar J. Naranjo and José L. Ramírez, *On colored partitions and Euler-type identities*, Integers26 (2026), A20, published19January2026, identifies A126348 in Section2.1 as colored partitions with distinct colors. Its results are bijective/enumerative, with no asymptotic theorem.
Primary full text: https://math.colgate.edu/~integers/aa20/aa20.pdf

## Related asymptotic literature and limits of the search

Richard J. McIntosh, *Some asymptotic formulae for q-shifted factorials*, Ramanujan Journal3 (1999),205--214, DOI10.1023/A:1006949508631, provides polylogarithm/Bernoulli expansions for q-products. The accessible publisher abstract establishes this tool-level relevance; the full paywalled text was not inspected.
https://link.springer.com/article/10.1023/A:1006949508631

Arash Arabi Ardehali and Hjalmar Rosengren, *A New Product Formula for (z;q)_infinity, with Applications to Asymptotics*, Constructive Approximation, published19September2026, DOI10.1007/s00365-026-09783-2. The open text gives an exact gamma-product formula and uniform q-product expansions. Corollary2 imposes Re(y)>=-Y for fixedY in (e^{-y};e^{-beta})_infinity; our y=log(1-e^{-t})+t±i*pi has Re(y)->-infinity, so direct invocation of that stated uniform corollary is unjustified. It is valuable background, not a located coefficient theorem for this sequence.
https://link.springer.com/article/10.1007/s00365-026-09783-2

The searches included exact IDs A126348 and A022629 with asymptotic/proof/theorem; the defining products; colored partitions with distinct colors/sizes; and current primary q-product papers. No published A126348 coefficient asymptotic or inverse-growth theorem was located. This is a bounded search result, not a claim of literature-wide absence.

The current ProveIt origin/main snapshot1512ef8 was checked read-only through the supplied path inventories and a git grep across textual docs: no A126348,A022629,A266891,A124380 match. Parent has the full duplicate inventory.

## Ranked screen handed into the selected projects

1. A022629: product(1+kq^k), natural colored distinct-size partitions. Live OEIS explicitly calls log a_n~sqrt(n/2)(log(2n)-2) a conjecture. The meaningful follow-up is relative/all-order coefficient asymptotics and inversion, because the weak logarithmic equivalent is elementary. The deeper attack is assigned to the other worker.
2. A126348: the selected Hilbert-series/colored-partition problem above.
3. A124380: [q^n]sum_{k>=0}q^k product_{j=1}^k(1+jq). Live OEIS labels loga_n~(n/2)logn-(n/2)(1+log2) conjectural (September2024). Cerbai--Claesson--Sagan, *Self-modified difference ascent sequences*, Advances in Applied Mathematics170(2025),102929, Theorem4.5/Lemma4.6, supplies a natural restricted-growth interpretation but no asymptotic theorem. Primary full text https://users.math.msu.edu/users/bsagan/Papers/Old/smd-pub.pdf. A plausible exact starting point is sum_k [u^(2k-n)]Gamma(k+u+1)/Gamma(u+1), followed by a two-variable saddle and Stirling expansions. The dominant saddle hasu~sqrt(n/2),2k-n~u logu; an all-order expansion should involve n^{-1/2} and logn. Its leading growth inverse has n~2logY/W(logY/e). This is a route, not a proved all-order theorem.
4. A266891: product(1+kq^k)^k. The live OEIS conjecture is loga_n~n^(2/3)(2log(3n)-3)/(4*3^(1/3)), May2018. This belongs to the same selected moving-edge family as A022629; it should not be counted as an independent research direction. Generalizing the outer multiplicity to k^r gives cutoffK~((r+2)n)^(1/(r+2)) and a Sommerfeld-edge expansion.

Other screens were rejected: A000123 has classical deBruijn asymptotics; A000607 already has detailed primary asymptotic literature; simple reciprocal products have elementary nearest-pole asymptotics; A262961 has substantial Bessel-moment arithmetic literature and a leading estimate amenable to standard Laplace expansion, so it was not promoted ahead of the three independent programs above.
