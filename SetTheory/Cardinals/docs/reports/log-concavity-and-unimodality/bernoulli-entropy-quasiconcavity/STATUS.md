# Result status and claim boundaries

Date: 20 September 2026.

## Proved in the manuscript

1. For every finite real q>1, both entropy functionals fail quasiconcavity in
   the Bernoulli parameters already for n=2, on a mean-preserving interior segment.
2. A dyadic witness family: m=3+ceil(1/(q-1)), p=2^(-m), endpoints
   (3p/2,p/2) and its reversal, midpoint (p,p).
3. An exact q=2 rational Jensen violation, with Tsallis gap 181/80000.
4. The sharp balanced-point curvature boundary
   p_c(q)=1/(1+exp(acosh(2^(q-1))/(q-1))).
5. The complete fixed-mean two-coin maximizer classification for q>1, with
   boundary threshold p_b(q)=1/[2(1+2^(1/(q-1)))] and center threshold p_c(q).
6. Concavity of both functionals on every two-coin fixed-mean segment for 0<q<=1.
7. Minimum dimensions: Tsallis q>1 requires exactly two coins; Renyi 1<q<=2
   requires exactly two; Renyi q>2 already fails for one coin.
8. Interior mixed-direction curvature failures near (p,...,p) for each fixed n>=2.

## Imported known result

Shannon joint concavity for arbitrary n, proved by Hillion and Johnson. Combined
with item 1, it implies that the largest finite universally admissible order is one.
That statement does not assert that every smaller positive order is admissible.

## Computations actually run

- 12,512 standard-library exact arithmetic checks: PASS.
- Independent SymPy differentiation and polynomial identities: PASS.
- 80-decimal evaluation of the explicit phase boundaries; two plots generated.
- Original exploratory floating-point Hessian search, archived separately.
- PDF build and visual/layout checks recorded in results/pdf_quality_control.txt.

## Not established or claimed

- General joint concavity for every 0<q<1.
- An all-order interval theorem for arbitrary n.
- The same conclusions under a same-sign-slope restriction.
- Complete maximizer classification for n>=3.
- Uniform-in-n quantitative neighborhood sizes.
- Results at order zero or a nontrivial Tsallis functional at order infinity.
- Proof-assistant formalization, independent referee validation, author approval,
  or exhaustive bibliographic priority verification.

## Precise relationship to the literature

The numerical values proposed adjoining Conjecture 4.2 in arXiv:1503.01570v1
are disproved. The two existential initial-interval statements of that conjecture
are not disproved merely by replacing their conjectured thresholds: they could
still hold with threshold one. The article consistently distinguishes these claims.
The original Shannon Shepp–Olkin theorem is not being challenged.
