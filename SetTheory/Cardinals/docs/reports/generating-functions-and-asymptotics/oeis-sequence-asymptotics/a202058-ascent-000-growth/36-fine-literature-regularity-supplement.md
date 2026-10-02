# A202058: targeted regularity and letter-weight search

Checked 2 October 2026 (UTC). This supplement records a scoped negative literature search plus small exact counterexamples that rule out some tempting routes. It proves no eventual ratio regularity.

## Bottom line

No retrieved primary paper proves log-concavity of `b_n=a_n/n!` for A202058, nor the equivalent inequality

`(n+1) a_n^2 >= n a_(n-1) a_(n+1)`.

No retrieved closed generating function weights the complete multiplicity profile of ordinary ascent-sequence letters in a way that specializes directly to the cap-two class. Existing refinements of total repetitions, zero multiplicity, consecutive-run lengths, or Fishburn matrix entries do not suffice without an additional correspondence or coefficient-extraction argument.

## Exact obstructions to broad positivity claims

These are elementary checks performed here, not literature claims.

### 1. The normalized sequence is not PF3

The first normalized coefficients are `b_0=b_1=b_2=1`, `b_3=2/3`. The Toeplitz matrix `T_(i,j)=b_(j-i)` (with negative subscripts zero) has the minor from rows `0,1,2` and columns `1,2,3`

`det [[1,1,2/3],[1,1,1],[0,1,1]] = -1/3`.

Thus the complete sequence is not a Pólya-frequency sequence of order three, hence not PF-infinity. Full Toeplitz total positivity cannot prove the desired statement for this sequence. PF2/log-concavity remains possible. This initial minor does not rule out positivity after an eventual shift or another auxiliary representation.

### 2. The natural repetition polynomial is not real-rooted

Let `R_n(z)=sum_w z^(n-number_of_distinct_letters(w))`, summing over cap-two ascent sequences of length n. Here the exponent counts doubled letters. Exact direct enumeration gives

`R_7(z)=1+21 z+126 z^2+129 z^3`.

Its cubic discriminant is `-84159`, so it has two nonreal conjugate roots. Consequently one cannot assume a stable multivariate refinement whose diagonal specialization is this polynomial, or use real-rootedness of this particular statistic. The polynomials fail real-rootedness at n=8,9,10 as well.

For comparison, the ordinary ascent-count polynomials `P_n(z)=sum_w z^asc(w)` are real-rooted in the exact finite check through n=10. This is not a theorem, and rowwise real-rootedness would not alone give log-concavity of the totals across lengths.

### 3. The obvious coordinatewise lattice does not exist

The words `001` and `010` both satisfy cap two; their coordinatewise minimum `000` does not. Thus the cap-two class is not closed under the standard meet. This excludes an immediate FKG/distributive-lattice argument on the raw words; an alternative ordering or encoding is not excluded.

Reproducible files: `literature-checks/check_small_polynomials.py` and `literature-checks/small_polynomials.json`. The script enumerates every cap-two ascent sequence through length 10 directly, checks the total counts against A202058, and uses exact rational/polynomial calculations for the discriminant, minor, and real-root counts. No floating-point root test is used for the conclusions.

## Nearby primary results and why they do not settle the target

### Savage–Visontai: s-Eulerian real-rootedness

Carla D. Savage and Mirkó Visontai, *The s-Eulerian polynomials have only real roots*, [arXiv:1208.3831](https://arxiv.org/abs/1208.3831), [PDF](https://arxiv.org/pdf/1208.3831), DOI 10.1090/S0002-9947-2014-06256-9.

This gives real-rootedness and an interlacing/compatibility method for ascent enumerators on s-inversion sequences. Their allowed coordinates have fixed bounds `0<=e_i<s_i`, and their ascent statistic compares scaled coordinates. A202058 instead has an adaptive ascent bound and a global multiplicity cap. No representation transferring this theorem was found. Some search hits loosely say “ascent sequences” while referring to ascents of inversion sequences; they must not be treated as the same class.

### Liang–Sagan: distributive lattices

Jinting Liang and Bruce E. Sagan, *Log-concavity and log-convexity via distributive lattices*, [arXiv:2408.02782v2](https://arxiv.org/abs/2408.02782v2), [PDF](https://arxiv.org/pdf/2408.02782v2), September 2026 revision.

Their Order Ideal Lemma uses a distributive lattice with opposing or matching order ideals to establish product inequalities. Applications include order polynomials, Stirling numbers, Narayana numbers, and other families. The paper supplies no bounded-occurrence ascent-sequence theorem. Its first-occurrence/rest encoding in Section 7 is for restricted growth functions, which satisfy a maximum-based bound. A cap-two ascent sequence need not be an RGF: `01013` is a valid example with the label 2 missing. The raw-coordinate obstruction above prevents a direct specialization.

### Jin–Schlosser: several statistics, not full letter content

Emma Yu Jin and Michael J. Schlosser, *Proof of a bi-symmetric septuple equidistribution on ascent sequences*, [arXiv:2010.01435](https://arxiv.org/abs/2010.01435), [PDF](https://arxiv.org/pdf/2010.01435).

The generating series in Definition (1.5) and Theorem 2 tracks length, ascents, total repetitions, maximal entries, and zeros. Crucially `rep=n-#distinct`; it is not the maximum multiplicity or a product of independent weights for each letter count. For example, `0001` and `0011` both have `rep=2`, while only the latter obeys cap two. Therefore specialization in the repetition variable cannot isolate A202058. The extra zero statistic distinguishes this example but still does not record every nonzero letter's multiplicity.

### Dukes et al.: bounded runs

*Enumerating (2+2)-free posets by indistinguishable elements*, [arXiv:1006.2696](https://arxiv.org/abs/1006.2696), [PDF](https://arxiv.org/pdf/1006.2696).

Theorems 8–9 give a product-series formula obtained by expanding primitive ascent sequences into consecutive constant runs. The multiplicities there are run lengths, not total occurrences of a value. Its bound on every run therefore allows `01010`, while the cap-two condition excludes that word. These formulas cannot be used as letter-multiplicity generating functions for the present problem.

## Search scope

Queries combined ascent sequences or A202058 with log-concavity/log-convexity, real-rootedness, interlacing, total positivity, multiplicities, multivariate content, and weights for each letter. The relevant primary sources were read beyond search snippets. This search does not certify that no suitable theorem exists, and none of the finite obstructions disproves the target PF2 inequality or eventual regularity.
