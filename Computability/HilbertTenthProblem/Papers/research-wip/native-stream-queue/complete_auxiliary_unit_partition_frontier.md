# Seven-unit partition family on18 witnesses

The complete [sources and finite checker](complete_auxiliary_unit_partition_frontier.py) and [receipt](complete_auxiliary_unit_partition_frontier.json) give three new cost/degree tradeoffs from the ordinary auxiliary quotient circuit: **89 operations/exact degree110,91/80, and93/64**, each on the same18 strictly positive witnesses and ordinary input. Together with the two immediate parents, the frontier **within the explicitly declared family** is

| Full operations | M | A | Exact degree | Parent | Canonical block weights |
| ---: | ---: | ---: | ---: | --- | --- |
|85|48|37|175|normalized85|175|
|86|47|39|131|ordinary86|131|
|89|48|41|110|ordinary86|54,55,22|
|91|48|43|80|ordinary86|40,39,30,22|
|93|48|45|64|ordinary86|31,18,32,28,22|

Each row has a complete saved live instruction array, including its finalizer. These are not bounds on arbitrary arithmetic circuits or a global Pareto frontier. The minimum operation count remains85 in this family. Historical19-witness constructions are separate comparisons, not alternative instances of these18-witness sources.

## 1. Parents and exact scope

The only two starting polynomials are the frozen [normalized85 auxiliary quotient](complete85_auxiliary_bezout_projection.md) and [ordinary86 auxiliary quotient](complete86_ordinary_auxiliary_projection.md). Their complete parent receipts, source files, proof notes and inherited dependencies are authenticated before use:25 exact byte pins, listed in the new source and receipt. The two earlier partition notes are pinned only as method provenance; no historical Python is imported, isolated or executed. There is no public maintained API claim beyond the bounded source CLI.

The ordinary x, all18 witnesses, all six fixed numeral ports and their domains are retained. In particular, the program numerals must obey the **entire inherited compiler recipe**. Necessary positivity or radix inequalities alone are not offered as a substitute for that recipe.

The factor order is

    0 first, 1 main, 2 input, 3 auxiliary,
    4 index, 5 transport, 6 strong.

The actual source closures of these seven factors have the following counts and exact degrees:

| Parent | Factor core | Factor degrees in this order |
| --- | --- | --- |
| Normalized |78=42M+36A|22,18,32,60,7,2,34|
| Ordinary |79=41M+38A|22,18,32,28,7,2,22|

The parent finalizer is their product minus1. Both parent theorems establish that **all seven factors equal+1 at every positive zero on a valid program slice**. The ordinary statement includes its separate rank, positive-restoration and index-sign argument. It is not inferred merely from the formal product of seven arbitrary integers being1.

## 2. Precisely enumerated grammar

Enumerate every set partition of the seven factor indices into nonempty blocks. A block's factors are multiplied in increasing index order with left association. For each partition with block products G1,...,Gg, emit:

    all-SOS: sum_j (Gj−1)²;

    one-anchor: Ga * [1+sum_(j != a) (Gj−1)²]−1,

once for every distinguished block a. The one-block anchor case is just the complete factor product minus1. There is no extra coordinate, supplied residual, omitted comparison or external finalizer.

There are Bell(7)=877 partitions and3263 distinguished-block choices, hence4140 plans per parent and8280 plans altogether. The enumeration generates each complete source, prunes only unreachable private rows, checks closure and liveness, recounts every gate, and expands the actual finalizer at the factor ports. It does not run a historical partition optimizer.

Only two additional literal simplifications are allowed. In the ordinary source,

    Ns=strong_difference+1.

If {6} is a singleton block whose residual is squared, substitute

    (Ns−1)²=strong_difference².

The final subtraction and private old+1 disappear, saving **two additions**. If {6} is instead the distinguished singleton anchor, put S for the sum of the other residual squares and use

    Ns(1+S)−1=strong_difference(1+S)+S.

This saves **one addition**. Both are exact all-value polynomial identities; the checker proves them on the actual emitted finalizers. The ordinary source has877 squared-singleton folds,203 anchor-singleton folds and3060 plans with no fold. The normalized source has no such private+1 producer, so all4140 normalized plans remain unfolded.

No other reassociation, CSE search, factor identity, algebraic coordinate change, sign-based unsquared guard, or factor subset is part of the grammar. In particular the minimum claims below apply to these literal schedules and two specified folds.

## 3. Positive-zero equivalence on the same supplied tuple

If an all-SOS polynomial is zero at a real tuple, each block product is1. If an anchor polynomial is zero at an integer tuple, its second factor is a positive integer, so both it and Ga must be1; again every block product is1. Thus either construction implies that the product of the original seven factors is1. Every positive child zero is therefore a positive zero of its immediate parent, with the same x, witnesses and fixed program numerals.

Conversely, the full positive-zero theorem of each parent forces all seven factors to be+1. Every block product is then1, so every declared finalizer vanishes. The two source folds are exact polynomial identities and preserve this equivalence.

Hence **the entire positive integer zero sets are identical on the same18 supplied witness coordinates** for all plans based on the same parent and valid program recipe. This transfers the parent's ordinary-input language representation without fresh native witnesses. It does not assert that the normalized and ordinary parents have the same zero tuples, that arbitrary fixed numerals encode valid programs, or that every grouped polynomial equals its parent off the zero set. Except for the one-block anchor, the latter is generally false. Nor is an all-integer or real zero-set equivalence to the parent claimed.

## 4. Fully paid ledger

Write cM,cA for the factor-core multiplication/addition counts. Except for the one-block anchor, both finalizer kinds use exactly

    M=cM+7,
    A=cA+2g−1,
    operations=(cM+cA)+6+2g,

before the specified ordinary singleton fold. Group products cost7−g multiplications; every residual, square and sum is charged. The nonempty anchor additionally pays the shift by1, anchor multiplication and final subtraction, while omitting one squared residual, giving the same total. The one-block anchor instead costs cM+6 multiplications and cA+1 additions.

The squared singleton fold subtracts2 from A; the anchor singleton fold subtracts1. It removes only the private `norm_strong` row from the factor core, plus the indicated finalizer row. No other core row is absent. Every full plan retains the complete free-coordinate list, all18 witnesses and six fixed numeral ports; all declared leaves and gates are live.

Across all8280 reconstructed sources the checker recounts **762,221 live gates=401,578M+360,643A**. It records a deterministic stream hash of every plan, full source, output and finalizer identity. The receipt saves only the five canonical frontier arrays in full; its other census entries are metadata and hashes, not thousands of purported saved arrays.

The canonical new all-SOS partitions are

    89/110: {first,input}, {main,auxiliary,index,transport}, {strong};

    91/80:  {first,main}, {input,index}, {auxiliary,transport}, {strong};

    93/64:  {first,index,transport}, {main}, {input}, {auxiliary}, {strong}.

All three use the squared singleton-strong fold. There are respectively1,3 and6 plans attaining these operation/degree pairs. One representative is saved for each. The two parent points each have multiplicity1. No anchored form contributes an additional frontier point.

## 5. Exact degrees from the actual source

The seven factor weights are exact full-polynomial degrees. The helper obtains them from the literal retained cores, not from equations valid only at zeros. It verifies the actual main/input norm cones and the all-value identity

    (X+ac+gamma)²−(a²+H)c²
      =(X+gamma)(X+gamma+2ac)−Hc².

All seven entire leading homogeneous forms are compared with their explicit formulas. Fixed numeral ports have degree0; ordinary x and the18 witness coordinates have degree1. The factors have nonzero leaders for every valid fixed-program specialization. The only leader requiring more than a product-of-powers observation is the transport leader

    Q0=Bm1*Jrep,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    U2=w*C1−transport_quotient*Q0.

Its coefficient of `transport_quotient*Jrep` is the otherwise unmatched−Bm1, which is nonzero. In the notation k0=eta+zeta, gamma0=rho+sigma and T=`auxiliary_quotient`, the ordinary factor leaders are

| Factor | Leading form |
| --- | --- |
| First |−w² k0² s⁴ Q0¹⁴|
| Main |8 gamma0 w² k0 s³ Q0¹¹|
| Input |−4 delta² w⁵ s⁵ Q0²⁰|
| Auxiliary |w² k0² s⁴ Q0¹⁴ T² f⁴|
| Index |−h w s Q0⁴|
| Transport |U2|
| Strong |i² k0⁴ s⁴ Q0¹²|

For the normalized parent, the auxiliary and strong leaders instead are

    w⁴ i² k0⁶ s¹⁰ Q0³⁴ T² f²,
    −w² i² k0⁴ s⁶ Q0²⁰,

and the other five are unchanged. The source checks both sets directly.

Every block product therefore has exact degree equal to the sum d_j of its factor weights and a nonzero leading form. All-SOS has exact degree `2 max_j d_j`: the top form is a sum of real squares of nonzero block leaders, so its maximal terms cannot cancel. An anchor with more than one block has exact degree

    d_a+2 max_(j != a) d_j.

Its leader is the nonzero anchor leader times that nonzero sum of squares. The one-block anchor has exact degree equal to the sum of all weights. The two singleton folds are entire polynomial identities, so none changes the degree. These arguments establish exactness for **every declared plan**, uniformly in the fixed numerals of valid program slices.

For the three canonical new sources the maximal squared block is unique. Their full leading forms are

    89/110: 64 h² gamma0² w¹⁰ k0⁶ s¹⁶ Q0⁵⁸ T⁴ f⁸ U2²;

    91/80:  64 gamma0² w⁸ k0⁶ s¹⁴ Q0⁵⁰;

    93/64:  16 delta⁴ w¹⁰ s¹⁰ Q0⁴⁰.

The saved degree certificates expand the entire leading polynomial for each of the five saved full sources. They contain168,120,441,21 and1 monomials, respectively. Their naive gate bounds are185,141,120,90 and76; the smaller exact degrees use the stated source cancellations and noncancellation proof, not just syntactic maximum estimates.

## 6. Finite minima and reproducibility

The combined best exact degree at each attained operation count in the declared grammar is

| Operations |85|86|87|88|89|90|91|92|93|94|95|96|97|98|
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Degree |175|131|153|176|110|120|80|102|64|86|64|86|64|86|

Removing dominated entries gives precisely the five-point frontier stated above. Both uniform-degree arrays, every canonical partition/anchor and each allowed fold are included. There is also an elementary ordinary degree floor. An all-SOS block contains the degree32 input factor, so its degree is at least64, attained at93 operations. For a nonempty anchor finalizer, if the input lies outside the anchor the degree is at least2+64=66. If the input lies in an anchor of weight at least66, the degree is larger than66; if that anchor weighs less than66, it cannot also contain both degree22 factors, so an outside block weighs at least22 and the objective is at least32+44=76. Thus the exact unrestricted-group anchor floor is66, attained by the degree2 transport singleton anchor with all other factors singleton. The separate one-group anchor has degree131. The exhaustive enumeration additionally certifies each operation-dependent minimum. No claim is made about finalizers outside this grammar.

Besides the all8280 full-source/finalizer checks, the checker evaluates all five saved complete polynomials on60 supplied tuples, including20 rational tuples. These confirm their exact finalizer formulas; they are not full universal Pell-zero witnesses. The infinite positive-zero theorem is the argument in Section3, inherited from the pinned parent proofs.

The helper uses elementary polynomial utilities also used in the preceding author packet; this is author implementation reuse, not an independent review claim. Every run freshly authenticates all25 pins, verifies parent receipt/source bindings, performs the literal reconstructions and checks a saved receipt with type-exact equality.

    python3 /absolute/path/complete_auxiliary_unit_partition_frontier.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete_auxiliary_unit_partition_frontier.json
