# Independent complete-source review of repeated-pack factorization

The complete repeated-pack compiler passes independent handwritten proof and literal-source review, with no correction requested. All 2,983 rows in the saved `r=1,2,4` graphs are authenticated: 2,707 retained literal records, 264 new records, three relocated squares and nine rebound native-header records. The three pack polynomials, and therefore the entire final polynomial on the same supplied tuple, agree with the frozen quotient-pair parent for every integer runtime assignment. The ordinary input, positive witness list, fixed-role recipe, 23 comparisons and native exponent are unchanged.

For `r>=1`, set `m=8+2r`, `ell=62+6r` and `pc(t)=floor(log2(t))+popcount(t)-1`. The certificate costs `(229+34r+pc(ell)+gM(m))M+(496+46r+gA(m))A`; the full polynomial costs `(252+34r+pc(ell)+gM(m))M+(541+46r+gA(m))A`, or `793+80r+pc(ell)+gM(m)+gA(m)` operations. It has `96+6r` positive witnesses and `6+18r` fixed roles. The `r=0` branch is the identical earlier 903-operation/96-witness fallback. No numerical universal presentation or degree bound is supplied by this symbolic family.

## 1. Independent packing and paid-power proof

The inherited low-to-high lane order is `m` selectors, then blocks of lengths `(6,6,6,6,7,7,7,7,2,...,2)`, then aggregate and height. The selected lengths sum to `52+4r`; adding the selectors and top two lanes gives `ell`. The right selector lanes all equal `J`, the right entries in block `i` all equal `(B-1)s_i`, and the final entries are `(D-1)J,D-1`. Thus the normalized top pair is `(D-1)(J+P)`.

For any integer high word `a`, appending `n` identical low lanes `q` gives `P^n*a+q*R_n(P)`, where `R_n=1+P+...+P^(n-1)`. Induction from the highest slot downward yields exactly the emitted right-block recurrence; the final join `P^m*a+J*R_m` appends the selector block. This proof uses no guard, positivity, selector exclusivity, division or AND property. It includes `P=0,1` and negative `P`.

The left and output packs have identical low selector lanes, so they share `Q=sum_i s_i*P^i`. Their retained high words end at the actual registers `left_join_m` and `output_join_m`, and their new final expressions are `P^m*L+Q` and `P^m*O+Q`. The output's top height lane is literal zero; its inherited Horner construction omits that initial zero step. This accounts for the retained high-word total `2ell-3-2m` of each operation, rather than one extra product/addition pair. No new zero-folding or semantic cancellation is credited.

The support rows pay four products for `P2,P3,P6,P7`, one product and four additions for `R2,R3,P3+1,R6,R7`, and three products for `(B-1)R2,(B-1)R6,(B-1)R7`: `8M4A`. `P2` is the exact existing `scale_square_0=P*P` row relocated earlier; the remaining prescribed power chain retains its other `pc(ell)-1` records and operands literally.

For the additional pair `(P^m,R_m)`, the leading binary digits `110` or `111` use the already paid seed 6 or 7; every other `m>=10` begins `10` and uses seed 2. Doubling pays `2M1A` for `P^(2n),(1+P^n),R_n(1+P^n)`. A following one pays `1M1A` for `R_(2n)+P^(2n)` and `P^(2n)P`. If `d` bits remain and `e` are ones, `gM=2d+e` and `gA=d+e`. These are all-r structural schedules, not formulas inferred from saved numerical evaluations. The prepared `P3,R3` still feed the support even when they are not selected as a binary seed.

## 2. Complete row, consumer and interface closure

I read the full 82-line initial proof, the full frozen 110-line primary and 178-line composer as text, and both complete files of Aristotle's final mathematical/ledger review. The parent complete source and all 2,983 successor rows were inspected only as inert records. A fresh original 229-line metadata-only reviewer validator was written independently from the paid schedule, executed once successfully, then frozen with its first receipt. No supplied, archived, predecessor or frozen scientific helper was executed or imported; no source/coefficient array was numerically or symbolically evaluated, and no degree was propagated.

The validator constructed an independent literal expected schedule for every support row, binary extension, descending selector prefix and block join, and matched the entire saved arrays and stage order. It compared every unaffected row with its actual parent, not merely author row counts. Every declared input, witness, selected-port label, centered form, quotient-pair action port, fixed-role recipe, comparison pair and ordinary-input domain agrees with the parent, except the expressly changed three pack exits and added computed selector interfaces. All 24/42/78 fixed roles remain charged once in the three cases.

The deleted old cones consist of `aggregate_mask`, all `m` letter-mask products, every old right Horner row, and the old left/output Horner rows below lane `m`. Their complete external executable consumer lists contain only the three old pack outputs entering `pell_scaled_A`, `pell_scaled_B`, and `pell_scaled_Z`. Exactly those three header operands are rebound to `packed_left`, `packed_right`, and `packed_output`. Native padding constants and every other native row remain literal. No stale removed name survives in an executable operand.

The relocated `scale_square_0` has one producer. Its old native successor still takes it twice, while the new support, size-two blocks and applicable geometric extension use the same computed row. The final selector power has exactly three consumers, the left/right/output high joins. The final geometric sum feeds only the right selector sum. The shared `Q` has exactly the two left/output final-join consumers. All rows, ordinary input and positive supplied coordinates are topologically closed and syntactically live.

Lane metadata replaces each deleted mask name with an explicit `semantic_product` of the exact original multiplication operands. These descriptors match every original lane; they are not executable inputs, free witness values or uncharged rows. The retained `height_mask=D-1` and `cell_mask=B-1` remain computed and live. This separates the unchanged mathematical lane meaning from the shorter executable graph.

All rows after the native header, including the 198-row paired action, full selected-center/quotient action, fused lift, recurrence right sides and 68-row finalizer, match literally. The finalizer is `23M45A`, and the same 23 comparison pairs and output name remain. Substitution of the three all-integer pack identities into this closed unchanged continuation proves exact equality of every native residual and the whole sum-of-squares polynomial. The parent's positive guard/domain, carry recovery and completion transfer on the identical supplied tuple; there is no new existential map or extra positivity premise.

## 3. Counts and saved-source coverage

The exact saving from the quotient parent is `(51+6r-gM)M+(54+6r-gA)A`. It includes deletion of the `m+1` private mask products and counts the relocated square once. The additional selector sharing saves `m-1` of each operation. Independently summing the disjoint prefix, centered forms, packs/support, remaining power, native certificate, paired/quotient action, lift and recurrence-right-side stages gives the certificate ledger above. Thus the all-r claim comes from the full grammar; the three saved arrays separately establish these literal instances.

| r | Literal retained | New rows | Relocated square | Rebound header rows | Certificate M/A | Full M/A | Total | Witnesses | Saving M/A |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 808 | 76 | 1 | 3 | 275 / 545 | 298 / 590 | 888 | 102 | 52 / 57 |
| 2 | 879 | 81 | 1 | 3 | 307 / 589 | 330 / 634 | 964 | 108 | 61 / 65 |
| 4 | 1020 | 107 | 1 | 3 | 380 / 683 | 403 / 728 | 1131 | 120 | 69 / 75 |

The deleted-row counts are 185, 207 and 251. All 3,362 parent records are accounted for as retained, removed, relocated or rebound; all 2,983 new records have exactly one coverage category. The savings total 379 rows across the three graphs. Source digests, removed-record digests, every retained-name snapshot, all stage censuses, witness domains and whole-graph liveness agree independently with the author's receipt. The receipt has precisely these three complete graphs and no additional formula-only cases.

## 4. Retained boundaries and final evidence

**Review remark 1 (geometric-series division).** The original warning remains: `(P^n-1)/(P-1)` is not an unpaid runtime operation and is undefined at `P=1`. The paid recurrences prove the polynomial identities there and everywhere else. No case is discarded by denominator cancellation.

**Review remark 2 (two different selector words).** The shared left/output `Q` cannot be replaced by `J*R_m`. The retained handwritten counterexample `m=2,s0=1,s1=0` gives `Q=1` and `J*R2=1+P`. It is a local identity boundary, not a claimed complete compiler zero or an emitted `r>=1` instance. No author correction was needed.

**Open question 3 (separate future saving and scope).** Further high-left history/form repetition, additional power sharing, a materialized universal relator presentation, a numerical universal equation bound, degree and optimality remain outside this source. Pascal's subsequent high-left schedule was separately hand-challenged; none of its savings is included in this frozen compiler or review. The primary and Aristotle's earlier pending literal-source condition are resolved by this particular complete audit, without expanding their historical review scopes or changing predecessor bytes. The numerical general84 frontier is unchanged.

The exact primary trio is bound by SHA256 `1040b7330d1a3228c4b30f986d200fc89442e6812a2ea21b95ff96c10c589ab2` (proof), `87208277efbd316332f2a9a0bb98b68ba1fe2cd3a416e63b98ff2982078d9e50` (inert composer), and `2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a` (complete source receipt). The companion JSON binds precise read spans, parent and independent proof-review pins, and the frozen one-run static auditor plus its first output. No repository/Git file or earlier frozen artifact was changed by this lane.
