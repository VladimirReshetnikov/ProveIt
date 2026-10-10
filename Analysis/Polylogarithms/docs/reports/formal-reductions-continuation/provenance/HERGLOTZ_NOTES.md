# Herglotz contribution: integration and provenance notes

This contribution targets the ProveIt snapshot at commit
`a2a4cf58c49c745058c40e4a6748d472a3420f18`.
The reference chapter is
`Analysis/Polylogarithms/docs/manuscript/chapters/09-herglotz.tex`.
All five incoming research archives were inspected for overlapping results,
including the recent conductor-descent archive. The classification below
extends the existing theorem for `J(2/q)` to every positive rational argument.

## Files and order

1. `article/sections/herglotz_classification.tex`: definitions, proper-real-subfield theorem, exact
   dyadic identities, odd-conductor coefficient tests, complete classification,
   two infinite families.
2. `article/sections/herglotz_rank.tex`: all relations and the exact rank of the denominator
   obstructions; a lower bound for the dimension of formal companion values
   modulo rational dilogarithms.
3. `article/sections/herglotz_identities.tex`: a known functional equation in a useful form,
   its explicit consecutive rational specialization, `J(3/4)`, `J(4/5)`,
   `J(3/5)`, and known reciprocal cases.
4. `article/references.tex`: the complete article bibliography, including the
   pre-existing bibliography key `RadchenkoZagier` and the additional sources.
5. `code/verify_j.py` and `data/verification_j.json`: reproducible exact group-algebra
   checks and independent high-precision quadrature.

The TeX fragments assume standard theorem environments, amsmath, amssymb,
and hyperref. They contain no bibliography environment of their own.

## Main conclusions

For coprime positive `p,q`, define the formal companion element by
`eta_(p/q) = xi_(2p/q) - 2 xi_(p/q) + xi_(p/(2q))`, reducing each
fraction before evaluating its cyclotomic boundary.

- If both integers are odd, a rational-dilogarithm reduction exists exactly
  when both belong to `{1,3,5}`. A logarithmic reduction exists only at `p=q=1`.
- Otherwise write `e` for the even integer and `o` for the odd one. Rational
  dilogarithms can be eliminated if and only if
  `e^2 = ±1 (mod o)` and `o^2 = 1 (mod 2e)`. Under precisely the same
  conditions, a logarithmic reduction exists.
- The modulus in the second condition is `2e`, not `e`. The pairs `(8,3)`
  and `(10,3)` demonstrate the distinction from the existing F criterion.
- Every consecutive rational `n/(n+1)` passes the logarithmic test, as do
  `e/(e^2-1)` and `e/(e^2+1)` for every positive even `e`.
- For odd `q`, set `G=(Z/qZ)^*/{±1}`, `H=<2>`, and
  `d(U)=(|U|-|U[2]|)/2`. Both denominator obstruction families have rank
  `rho(q)=d(G)-d(G/H)`. At `q=31` this is `6`, while the full beta rank is `7`.

The word **formal** is essential. All nonreduction and linear independence
claims concern the rationalized five-term pre-Bloch calculus. They are not
claims of algebraic or linear independence of the real periods. Positive
explicit analytic identities in `article/sections/herglotz_identities.tex` have separately
fixed logarithmic correction terms and rational multiples of pi squared.

## Exact dependencies from the pinned manuscript

These inputs already have proofs in Chapter 9 and need not be proved anew.

| Manuscript label | Input used here |
| --- | --- |
| `hstruct:eq:delta-xi` | The invariant finite cyclotomic element has boundary `beta_q(p)-beta_p(q)-<p> wedge <q>`. The rational wedge is essential. |
| `hstruct:thm:kernel` | The only linear relations among `beta_M(a)`, indexed by units modulo sign, are inversion-symmetric coefficient relations. |
| `hstruct:lem:positive-Gram` | The all-root logarithmic Gram matrix is positive definite at every conductor. |
| `hstruct:eq:skew-image` | The logarithmic skew-matrix image is `A_M(P_a-P_(a^-1))`. Combined with positivity, this proves the new proper-subfield consequence. |
| `hstruct:lem:norm` | Applying normalized field norms to each exterior factor separates coprime cyclotomic conductors. |
| `hstruct:eq:bloch-facts` | Invariant rationalized Bloch descent and surjectivity of the rational boundary map give both directions of the formal reduction criterion. |

No global injectivity of the logarithmic exterior map is assumed. The new
subfield theorem concerns one beta symbol at a time; it deliberately does
not assert the same for every linear combination. The norm separating
conductors is a norm on each factor, not Galois averaging of an invariant
exterior symbol.

## Analytic evaluation and literature attribution

The primary source for F and J and the analytic inputs is:

- D. Radchenko and D. Zagier, *Arithmetic properties of the Herglotz
  function*, Journal für die reine und angewandte Mathematik 797 (2023),
  229–253, DOI `10.1515/crelle-2023-0009`, arXiv `2012.15805`.
  Author manuscript:
  <https://people.mpim-bonn.mpg.de/zagier/files/preprints/HerglotzFunction.pdf>.
  Our proof uses their equations (15), (22a), (23), and (24).
- Y. Choie and R. Kumar, *Arithmetic properties of the
  Herglotz–Zagier–Novikov function*, Advances in Mathematics 433 (2023),
  article 109315, DOI `10.1016/j.aim.2023.109315`, arXiv `2309.10634`.
  <https://arxiv.org/html/2309.10634v1>.
  Their Theorem 3.1 already proves J reciprocity. Their Theorem 3.2(1),
  equation (3.3), is equivalent to our adjacent-argument functional lemma
  after substituting `(x+1)/x`, using reciprocity, and applying the
  F three-term relation. **The lemma is therefore attributed as a known
  reformulation, not a new general functional equation.**
- A. Dixit, S. Sathyanarayana, and N. Guru Sharan, *Mordell–Tornheim zeta
  functions and functional equations for Herglotz–Zagier type functions*,
  arXiv `2405.07934` (2024).
  <https://arxiv.org/html/2405.07934v1>.
  This provides relevant wider context for higher and character-weighted
  companion functions and should inform future extensions.

The recent primary followups above were checked, including the rational
special-value and concluding sections. The displayed consecutive family
and `J(3/5)` are proposed additions to the pinned manuscript. We make no
claim that every equivalent occurrence in the historical literature has
been excluded. The classification and rank results are proved additions
to the supplied work; priority should be stated at this manuscript level.

The following full real identities are proved in the contribution:

```
S(n) = sum_(k=1)^(n-1) log^2(2 sin(pi k/n)),   S(1)=0.

J(n/(n+1)) = (1/2) log^2(2)
  - (n^2-n-1) pi^2 / (24 n(n+1))
  + (1/2) [S(n)-S(n+1)-S(2n)+S(2n+2)].

J(3/4) = -5 pi^2/288 + (1/8) log^2(2)
  + (1/2) log^2(1+sqrt(2)).

J(4/5) = -11 pi^2/480 + (7/8) log^2(2)
  + 2 log^2(phi) - (1/2) log^2(1+sqrt(2)).

J(3/5) = Li_2(1/3) - (1/2) Li_2(1/5) - 7 pi^2/180
  + (1/2) log^2(2) + (1/2) log^2(3)
  - (1/4) log^2(5) + log^2(phi),

phi = (1+sqrt(5))/2.
```

The rational core of `J(3/5)` has boundary
`partial([1/3] - (1/2)[1/5]) = <2> wedge <3/5>`, matching the formal
classification. Its initial integer-relation discovery has been replaced
by an analytic proof using the known `F(2/5)` evaluation. The reciprocal
values `J(3)`, `J(5)` are not labeled new discoveries.

## Reproducible verification

From the archive root run:

```
python3 code/verify_j.py --output data/verification_j.json
```

The checked output records:

- 32,764 exact zero tests for the D and T coefficient families at odd
  conductors through 401.
- Exact rational matrix-rank and row-span comparisons through conductor 101.
- Recovery of the existing `J(2/q)` criterion, and arithmetic checks of the
  consecutive and `e/(e^2±1)` infinite families through the programmed limit.
- Twenty independent quadrature checks at 100 decimal digits, with absolute
  tolerance `1e-85`. The largest observed residual was below `7e-100`.

For the rational value `p/q`, the quadrature uses
`q integral_0^1 s^(q-1) log(1+s^p)/(1+s^q) ds`, obtained from `t=s^q`.
This removes fractional endpoint powers and does not reuse the symbolic
formula being tested. The computations are corroboration, not substitutes
for the general proofs. An independent mathematical audit checked all three
TeX fragments and found no required correction.

## Further research directions for the article

1. Produce short explicit real logarithmic formulas for every pair satisfying
   the two even/odd congruences, with a certified five-term reduction and
   branch record. The criterion proves existence but is not yet a practical
   minimal-expression algorithm.
2. Classify the arithmetic orbits of pairs satisfying those congruences under
   natural quadratic substitutions. Quantify their distribution as the
   numerator and denominator grow, separating the two signs.
3. Determine every relation among companion elements when both numerator
   and denominator vary, refining the denominator rank theorem to an exact
   global relation theorem. Shared prime conductors are the first obstacle.
4. Extend the proper-subfield theorem from individual beta symbols to a
   computable classification of arbitrary combinations that descend to a
   specified real subfield.
5. Investigate prime-dilation companions
   `F(ell*x)-2F(x)+F(x/ell)` and character-weighted Herglotz integrals.
   The dyadic normalization in this work suggests that the odd-prime
   conductor norm and its old/new decomposition should be worked out first.
6. Distinguish formal identities from real-period statements. Proving that a
   nonzero exterior obstruction prevents any numerical identity in a
   prescribed transcendental class would require substantially stronger
   period-independence input and is not established here.

