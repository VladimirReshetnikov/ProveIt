# Grouping the four linear-input 18-witness cores

The four complete sources from [the linear auxiliary-quotient family](complete_linear_auxiliary_quotient_family.md) yield six additional operation/degree points when combined with the earlier, explicitly pinned 18-witness results:

| Complete operations | M | A | Uniform exact degree |
| ---: | ---: | ---: | ---: |
| 90 | 48 | 42 | 98 |
| 92 | 48 | 44 | 76 |
| 93 | 48 | 45 | 60 |
| 94 | 48 | 46 | 56 |
| 95 | 48 | 47 | 50 |
| 96 | 48 | 48 | 44 |

Every source retains 18 strictly positive witnesses, its own parent's ordinary positive input x, and the entire valid fixed-program numeral recipe. The 85-operation minimum is unchanged. These are new complete sources within a specified grouping grammar, not unrestricted arithmetic lower bounds or a new universal input theorem. Historical 19-witness tradeoffs remain separate comparisons.

The [standalone helper](complete_linear_auxiliary_partition_frontier.py) generates and checks all 16,560 plans in that grammar and saves ten full frontier arrays in its [receipt](complete_linear_auxiliary_partition_frontier.json). The additional four saved arrays make the four-core frontier explicit: three are parent products, and 91/90 is dominated by the older 91/80 in the stated historical union. Unsaved tied schedules are represented by census metadata and a deterministic stream digest, not additional saved complete arrays.

## 1. Actual cores and the bounded grammar

Read only the authenticated four source arrays of `complete_linear_auxiliary_quotient_family.json`. Their full source and mathematical [independent review](review_linear_auxiliary_quotient_family.md) is also pinned. Extract exactly the ancestors of the following seven factors, in this order:

    N0, Nm, Ni, Na, Nk, Nt, Ns.

Here N0 is the first norm, Nm the main norm, Ni the linear-input norm, Na the ordinary auxiliary norm, Nk the retained index unit, Nt transport, and Ns the ordinary strong unit. The actual core ledgers and proved factor degrees are:

| Core | M | A | Total | Factor degrees |
| --- | ---: | ---: | ---: | --- |
| root / ordinate | 41 | 39 | 80 | 22,18,20,28,7,2,22 |
| root / auxiliary gap | 41 | 40 | 81 | 22,18,20,22,7,2,22 |
| first gap / ordinate | 41 | 40 | 81 | 12,18,20,28,7,2,22 |
| first gap / auxiliary gap | 41 | 41 | 82 | 12,18,20,22,7,2,22 |

All supplied ports, asymmetric scales X=wq and Y=sq³, the input modulus a+1, the new auxiliary quotient, and every original factor definition remain paid. Removing the old final product does not remove a defining comparison or positivity condition. In each core the sole definition `Ns=strong_difference+1` has no consumer inside the other six factor cones.

For each of the 877 set partitions of seven factors, emit one of:

- The sum of squares of every group product minus1.
- A distinguished group product A times `1+S`, minus1, where S is the sum of squares for all other groups.

Products within each group use increasing factor indices and are left-associated. Groups are ordered by their least index. There is no additional reassociation, common-subexpression, coordinate, or compiler search. The single-group anchor is precisely the ordinary seven-factor product-minus-one parent polynomial.

The sum of the partition block counts is 3263. Thus each core has 877+3263=4140 plans; all four have 16,560. The census traverses them without cost pruning.

## 2. Two literal strong-singleton folds and the complete charge

Write D=strong_difference, so Ns=D+1 is an all-value definition. When a group is the singleton Ns:

    (Ns−1)² = D²,
    Ns*(1+S)−1 = D*(1+S)+S.

The first fold deletes the private Ns addition and the residual subtraction, saving 2A. The second deletes the private Ns addition, saving 1A. The checker proves both as coefficient identities at independent factor ports. It verifies that this is the only removed core row; all other rows remain literal. No equation valid only on zeros is used for these folds.

For a core with counts Mc,Ac and a partition with g blocks, every nontrivial SOS/anchor output costs

    M=Mc+7,
    A=Ac+2g−1−f,

where f is2 for a squared strong singleton,1 for a singleton strong anchor, and0 otherwise. The sole single-group anchor instead costs `M=Mc+6,A=Ac+1`. Each core has 877 plans with the squared fold, 203 with the anchor fold, and 3060 without a fold.

These formulas are checked against actual emitted and output-live DAGs for every plan. The full stream contains 1,561,928 paid gates: 794,876 multiplications and 767,052 additions/subtractions. Each full finalizer is also proved at formal factor cuts, as are the four actual parent product finalizers. The stream digest authenticates that deterministic enumeration; the receipt saves only the ten representative arrays listed below. Those saved arrays contain 915 paid gates in total. All squares, products by fixed numerals, differences and binary sums are charged.

## 3. Full positive-zero equivalence

The domain is the complete supplied positive integer domain, with the same valid fixed compiler as each parent. At an SOS zero, every group product is1. At an anchored zero,

    A*(1+S)=1,

with A an integer and S a sum of integer squares. Since `1+S` is a positive integer, A=1 and S=0. Thus every group product is again1. Multiplying groups gives the parent's product of seven factors equal to1.

The parent's already proved full positive-zero theorem now applies. It establishes that all seven individual factors are+1, including the index/transport sign closure and the ordinary auxiliary quotient restoration. Conversely, any full positive parent zero has all seven factors+1, so every selected group residual vanishes and every anchored output is zero.

Therefore each emitted source has **exactly the same supplied positive integer zero tuples as its own immediate parent**. This uses the parent's all-seven=+1 theorem, not the false general inference that an arbitrary product1 forces all integer factors to be+1. The inherited theorem already handles signed computed gap expressions in the appropriate dependency order. Grouping adds no new positivity restriction on an intermediate register.

Except for the single-group anchor, this is not an identity with the parent's polynomial value. The full all-value statement is the explicitly emitted grouped SOS or anchored formula, with the two exact folds above. There is no assertion of equality of all integer, rational, or real zero sets, nor a claim about arbitrary fixed mask numerals. The anchor argument in particular uses integrality.

## 4. Uniform exact degrees from the literal cores

Assign degree 1 to every supplied witness and x, and degree 0 only to the six fixed numeral ports. The helper propagates the actual leading homogeneous polynomials through each literal core. At the two norm cones it uses the guarded all-value identity

    (z+ab)²−(a²+H)b² = z²+2abz−Hb².

At an auxiliary-gap cone it uses

    V²−(V+e)² = −e*(2V+e).

The defining rows of every such cone are checked before the identity is used. The resulting seven entire leading polynomials are compared coefficientwise with their explicit formulas and with the pinned parent's saved leaders. This proves the table's weights on the actual source; it does not merely import a weight list or impose the unit equations.

For group weights d_j, the exact full degrees are

    SOS:       2 max_j d_j,
    anchor a:  d_a+2 max_(j!=a) d_j,

with degree d_a for the sole single-group anchor. Group leaders are products of nonzero factor leaders. At the largest square degree, all tied squared leaders must be included. A sum of real polynomial squares cannot vanish identically unless every summand is zero. Multiplying by a nonzero anchor leader also preserves nonvanishing. The singleton folds preserve the entire polynomial, hence these degrees.

Uniformity under the valid fixed compiler specialization follows from the concrete parent leaders. Bm1>0; transport has the otherwise unmatched coefficient−Bm1 at `transport_quotient*Jrep`; all other displayed parent factors are nonzero products of independent supplied-coordinate polynomials. Fixed specialization therefore cannot annihilate a factor leader. No highest part is inferred from a zero-set identity.

For every saved output the receipt contains the complete leading polynomial, not only its degree. In particular the96/44 source has two maximal contributions, `Ha²+Hs²`; dropping either would give an incomplete leading polynomial. The ten leaders have respectively 240,456,408,441,27,27,54,5,9,12 terms. The matching degree upper bounds follow from the same all-value source calculation; the nonzero leaders prove equality.

## 5. Exact finite frontier and saved sources

The following table gives the canonical emitted representative for every point on the four-core frontier. Products within parentheses form a group; each listed non-product form is an SOS using the squared strong-singleton fold. Factor indices are0:first,1:main,2:input,3:auxiliary,4:index,5:transport,6:strong.

| Core | Complete operations / exact degree | Groups | Number of tied plans |
| --- | --- | --- | ---: |
| root / ordinate | 87/119 | (0,1,2,3,4,5,6), single anchor | 1 |
| first gap / ordinate | 88/109 | (0,1,2,3,4,5,6), single anchor | 1 |
| first gap / auxiliary gap | 89/103 | (0,1,2,3,4,5,6), single anchor | 1 |
| root / ordinate | 90/98 | (0,1,4,5),(2,3),(6) | 2 |
| first gap / ordinate | 91/90 | (0,3,5),(1,2,4),(6) | 1 |
| root / ordinate | 92/76 | (0,4,5),(1,2),(3),(6) | 4 |
| first gap / ordinate | 93/60 | (0,1),(2,4,5),(3),(6) | 2 |
| root / ordinate | 94/56 | (0,5),(1,4),(2),(3),(6) | 5 |
| root / auxiliary gap | 95/50 | (0,5),(1,4),(2),(3),(6) | 3 |
| first gap / auxiliary gap | 96/44 | (0,4,5),(1),(2),(3),(6) | 3 |

Tie counts are across the declared four-core grammar at that cost and degree. They do not assert that tied arrays are identical. No nontrivial anchor produces an additional frontier point in this census.

For the comparison in the opening table, take the union only with the pinned [earlier 18-witness auxiliary-unit frontier](complete_auxiliary_unit_partition_frontier.md) and the four immediate linear parents. Its resulting nondominated pairs are

    85/175,86/131,87/119,88/109,89/103,90/98,
    91/80,92/76,93/60,94/56,95/50,96/44.

The 91/90 new-family point remains a saved circuit but is dominated in this union. The 95/50 point is independently realized by the root/auxiliary-gap source: first+transport has weight 24, main+index 25, and the three remaining singleton weights are 20,22,22. Its maximum 25 gives exact degree 50 at 95 paid operations. This finite comparison is not a global Pareto claim over other representations or witness counts.

## 6. Reproduction and limits

The helper authenticates 59 predecessor source, receipt and proof files on every run. It imports no author or historical Python, executes no earlier builder/census, and uses no external package. Elementary polynomial, emitter and census utilities are adapted by source copy from the pinned earlier two-core author; that reuse is disclosed, not presented as an independent review. New actual-core guards, linear-input/gap leading calculations and all four source loads are checked afresh.

The complete finalizer coefficient proofs and live gate recounts cover all 16,560 generated plans. All ten saved outputs additionally receive 12 full signed/rational evaluations each, including 40 rational cases in total. These are algebra fixtures, not complete positive compiler zeros. No astronomical native Pell witness is materialized. The infinite-domain positive equivalence follows from Section3 and the pinned parent theorem.

Run with the standard library from any working directory:

    python3 /absolute/path/complete_linear_auxiliary_partition_frontier.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete_linear_auxiliary_partition_frontier.json

`--output` writes the deterministic receipt. All checks use explicit exceptions, so normal and optimized Python both retain them. Receipt equality is recursive and type-exact. This is a bounded CLI packet, with no general public compiler API or unrestricted optimization promise. Frozen predecessor files are unchanged.

The writer and fresh exact saved-receipt replays from `/`, in both normal and optimized Python, passed on the frozen source. Independent review is a separate artifact; its objective enumeration and saved-source checks must not be described as replaying the entire author source stream.
