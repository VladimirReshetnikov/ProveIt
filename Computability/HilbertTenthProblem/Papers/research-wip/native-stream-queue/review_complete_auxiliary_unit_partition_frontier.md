# Independent review of the seven-unit partition family

**PASS.** The frozen [author family](complete_auxiliary_unit_partition_frontier.md) has the advertised finite frontier, with full paid sources and uniform exact degrees:

| Full operations | M | A | Exact degree | Core | Positive witnesses |
| ---: | ---: | ---: | ---: | --- | ---: |
|85|48|37|175|normalized|18|
|86|47|39|131|ordinary|18|
|89|48|41|110|ordinary|18|
|91|48|43|80|ordinary|18|
|93|48|45|64|ordinary|18|

The independent [checker](review_complete_auxiliary_unit_partition_frontier.py) and [receipt](review_complete_auxiliary_unit_partition_frontier.json) verify all8,280 literal schedules in the declared grammar and all five saved complete sources. They read authenticated JSON and execute no author, ancestor or historical Python. All three author files and all25 dependency files are authenticated by exact SHA256 before use. This review requests no author change.

The three new ordinary points are complete ordinary-input universal upper-bound witnesses under their inherited fixed-program recipe. The minimum/frontier claim is restricted to the two actual cores, the specified partition finalizers and two literal folds. This is not a global circuit lower bound, and no source below85 operations is claimed.

## Independent coverage and paid reconstruction

The review starts from the frozen normalized85 and ordinary86 packets, not from author-generated core arrays. It reconstructs the full ancestor closure of the seven factor roots in this order:

    first, main, input, auxiliary, index, transport, strong.

The independently recovered cores are78=42M+36A and79=41M+38A. They have the same25 supplied ports:18 positive witnesses, ordinary x and six fixed numeral ports. Their underlying positive zero sets are not asserted to be identical to each other.

An independent subset recursion generates a partition by choosing the block containing the least remaining element, then recursing on the complement. It obtains877 distinct partitions. The counts by number of blocks1 through7 are

    1,63,301,350,140,21,1.

The sum of block counts is3263. One SOS plan per partition and one anchor plan per distinguished block therefore give4140 plans per core and8280 total. The completed partitions are sorted by restricted-growth encoding only to compare the author's deterministic stream; the coverage generator is different from the author's incremental block-placement recursion.

The review emitter independently constructs every whole source from the actual factor core. It uses the declared increasing-index, left-associated block products and literal finalizer recipes. Its temporary register names are translated for exact source comparison. All source closures, supplied leaves and paid gates are checked. The entire source/finalizer-identity stream matches the author's frozen digest. Every histogram, fold count, operation-dependent minimum, canonical representative and multiplicity also matches.

Except for the one-block anchor, a partition with g blocks costs

    M=core_M+7,
    A=core_A+2g−1,

before the allowed ordinary fold. The one-block anchor instead costs core_M+6 multiplications and core_A+1 additions. These formulas are compared with the recounted complete schedule in every case. Across the family the total is

    762,221 paid live gates =401,578M+360,643A.

This is a sum over8,280 schedules, not a count of globally distinct arithmetic subexpressions. The receipt saves five full frontier arrays; the other author entries are authenticated census metadata and a stream digest. The review reconstructs those other schedules to make the comparison and does not mislabel them as separately stored author arrays.

## The ordinary singleton folds and entire finalizers

The actual ordinary core contains the private row

    Ns=strong_difference+1.

No other factor-core instruction consumes Ns. If Ns is a squared singleton block, the residual Ns−1 becomes `strong_difference`; its private old+1 and the residual subtraction both disappear. This saves2A.

If Ns is the distinguished singleton anchor, writing D=`strong_difference` gives the all-value identity

    (D+1)(1+S)−1=D(1+S)+S.

This saves1A. The normalized core has a different strong definition and receives neither fold. The independent census confirms877 ordinary squared-singleton folds,203 ordinary anchor-singleton folds and3060 unfolded ordinary plans; all4140 normalized plans are unfolded.

For every complete plan the checker expands the entire finalizer at independent factor ports, including the actual D+1 substitution where appropriate. This proves the two folds and the whole finalizer formulas over arbitrary supplied scalar values. All retained core definitions remain literal parent definitions; only the private ordinary Ns row is absent when a fold applies. There is no division, coordinate deletion, omitted equality or unpaid finalizer.

## Positive-zero transfer and its precise domain

Let G1,...,Gg be the integer block products. An SOS zero forces every Gj=1. For an anchor zero,

    Ga*(1+sum_(j != a)(Gj−1)²)=1,

the second factor is a positive integer. Consequently both factors are1, all squared residuals vanish, and every Gj=1. In either case the product of the original seven factors is1. A positive child zero therefore restores the same supplied positive tuple as a zero of its immediate parent.

For the converse, the essential input is the already-proved native parent theorem: on every valid fixed-program slice, **all seven factors equal+1 at every positive parent zero**. Thus all block products are1 and every declared finalizer vanishes. Merely knowing that a formal product of seven integers is1 would be insufficient: for example, factors−1,−1,1,1,1,1,1 have product1 but singleton SOS value8. The review explicitly preserves this distinction. The ordinary parent's rank/integrality and index-sign proof is inherited; no parent theorem is invoked at a tuple lacking its positive-coordinate hypotheses.

The result is equality of the complete positive integer zero sets on the same18 supplied coordinates for every plan and its own parent. Ordinary x and all fixed numerals are held fixed. The full inherited compiler recipe remains required; arbitrary positive numeral choices are not promoted to valid programs. No all-integer or real zero-set equivalence to the parent is asserted. Except for the one-block anchor, a new polynomial need not equal its parent off the zero set.

## Exact degrees from complete core coefficients

The review uses its own exponent-vector sparse ring, reused from the immediately preceding independent ordinary-source audit. For both cores it expands the complete factor polynomials with all fixed numeral symbols retained, assigning those six symbols weight0 and every witness and ordinary x weight1. It computes actual core-register leaders from those complete coefficients. It does not execute the author's leading-form routine or rely on its prescribed main/input cancellation cuts.

The resulting factor degree arrays are

    normalized:22,18,32,60,7,2,34;
    ordinary:  22,18,32,28,7,2,22.

The sum of full monomial counts over the seven normalized factors is99,480; over the seven ordinary factors it is8,031. Thus107,511 full-factor coefficient terms are checked. Repeated monomials occurring in different factors are counted separately. All14 entire leading forms agree with explicit source formulas, including the main/input cancellations.

Writing Q=Bm1*Jrep, k0=eta+zeta and gamma=rho+sigma, the five common leaders and the two variant-specific leaders are products of nonzero powers and linear forms. The transport leader is

    U=w*(Q−F−Z−alpha−twice_cell_bits*x)
        −transport_quotient*Q.

Its otherwise unmatched coefficient of `transport_quotient*Jrep` is−Bm1. Hence every factor leader remains nonzero under every permitted fixed specialization, since Bm1>0. This proves uniformity, rather than only generic symbolic degree.

Each block therefore has exact degree equal to the sum of its factor weights. For SOS, its maximal-degree part is a sum of squares of nonzero real polynomial block leaders. It cannot vanish identically. For an anchor, the maximal part is the nonzero anchor leader multiplied by that nonzero sum of squares. Thus the exact degrees are

    SOS:2*max(block weights);
    nonempty anchor:anchor weight+2*max(other block weights);
    one-block anchor:sum(all factor weights).

The two folds are entire polynomial identities and preserve these degrees. This establishes the degree formulas for all8,280 plans. The five saved source outputs are also propagated using the independently expanded actual core leaders, and their complete leading coefficient arrays match the frozen certificates:168,120,441,21 and1 terms, respectively. Their naive gate bounds185,141,120,90,76 are kept separate from exact175,131,110,80,64.

For the new canonical sources the unique maximal squared blocks give the following explicit leaders:

    89/110:64 h² gamma² w^10 k0^6 s^16 Q^58 T^4 f^8 U²;
    91/80: 64 gamma² w^8 k0^6 s^14 Q^50;
    93/64: 16 delta^4 w^10 s^10 Q^40,

where T=`auxiliary_quotient`. All are uniformly nonzero. No degree calculation substitutes equations true only at zeros.

## Minima, supplementary checks and replay

The frontier multiplicities are1,1,1,3,6 in increasing operation order. In particular89/110 is uniquely

    {first,input}, {main,auxiliary,index,transport}, {strong}.

The canonical91/80 and93/64 representatives agree row for row with the author arrays, as do both parent-point representatives. No anchored plan adds a frontier point. The ordinary SOS degree floor64 follows because a block must contain the degree32 input factor; the enumeration also certifies all operation-dependent minima. These are finite grammar statements, not unrestricted optimization claims.

The five saved complete sources receive90 supplementary signed/rational whole-output evaluations, including30 rational supplied tuples, against their exact formulas in the original parent factors. These are not positive universal Pell-zero fixtures. The symbolic source identities, noncancellation proof and inherited parent theorems carry the corresponding infinite-domain conclusions.

Fresh receipt replay, using installed frozen authors, is

    python3 /absolute/path/review_complete_auxiliary_unit_partition_frontier.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/review_complete_auxiliary_unit_partition_frontier.json

If the author trio is staged elsewhere, add `--author-root /absolute/path/to/author-trio`. The helper reads both roots without modification, rejects optimized Python because assertions carry checks, and performs a type-exact receipt comparison. No maintained public API or historical suite is part of this audit.
