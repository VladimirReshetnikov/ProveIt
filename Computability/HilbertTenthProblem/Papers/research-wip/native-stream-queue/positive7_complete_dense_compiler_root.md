# Emitted positive7 history sources with a paid six-row action

The one-AND history relation now has an explicit complete arithmetic-source family and a single sum-of-squares finalizer. For any fixed positive seven-coordinate integer alphabet of size m, the dense source costs

    (74m+53+lambda)M + (89m+54)A,

where ell=8m+2 and lambda=floor(log2 ell)+popcount(ell)-1. When every letter has the same column sum C, the six-row source costs

    (67m+54+lambda)M + (82m+61)A.

Both have 23 comparisons and 8m+36 strictly positive existential coordinates. Their single-polynomial sources add exactly 23M+45A. Thus the column-sum version saves **14m-8 arithmetic operations** in this complete family. It applies to the inherited positive7 universal alphabet, whose common column sum is already proved.

These are generic compiler formulas, not a numerical universal bound. The universal presentation, its relator count and its numerical alphabet are still unmaterialized. The four literal examples in the receipt use formal fixed-numeral roles for m=1 and m=8; neither example is claimed to instantiate the universal alphabet. The complete general84 bound is unchanged.

## 1. Exact fixed data and declared coordinates

The ordinary relation argument is x>0. Fix positive compiler numerals alpha and gamma, a strictly positive integer alphabet A_sigma of dimension seven, and a fixed dyadic K greater than m and every column sum. For the column6 variant also fix its common column sum C, and require K>C. All matrix coefficients and these compiler numerals are fixed, not existential variables. In column6 only the first six rows and C occur as arithmetic operands; the seventh row of each actual letter is determined by its common column sum and is required to be strictly positive.

Use the positive input column

    tau=alpha*x+gamma,
    z=(3,tau,tau^2,2,tau,tau^2,1),
    S0=2tau^2+2tau+6.

The inherited universal application uses exactly its previous alpha and gamma. The input loader remains 3=2M+1A. The source computes S0 with three additional additions and D=S0+height_slack with a fourth. All these rows are charged.

The outer positive witnesses are seven history words H_i, **six** terminal coordinates F1,...,F6, m selector hats, 7m selected-source hats, height_slack and global_slack. The seventh terminal port is literally F1. The native block has 21 distinct positive auxiliaries, all with a fresh native_ prefix; its four relation parameters are computed bindings. The count is therefore

    7+6+m+7m+2+21=8m+36.

Sharing the terminal port is equivalent to the predecessor's separate F7>0 with comparison F1=F7. The forward map restores F7=F1 and the reverse map drops F7. Both preserve positivity and all other witnesses. Its removal also permits the product P*F1 to be reused in recurrences 1 and 7.

## 2. Outer source and complete positive projection

The source explicitly un-hats every selector and selected-source field, computes their sums, and retains the predecessor's exact unshifted global bound. In mathematical notation its definitions are

    S_sigma=Shat_sigma-1, Z_sigma,i=Zhat_sigma,i-1,
    J=sum S_sigma, D=S0+height_slack, B=KD,
    P=(B-1)J+1, S=sum H_i, Ztot=sum Z_sigma,i,
    mu=(D-1)J,
    S+Ztot+global_slack=P.

Its ell=8m+2 lanes are exactly the frozen geometry packet's m Boolean selector lanes, 7m selected-source lanes, one aggregate-range lane and one D AND(D-1)=0 lane. Each selected-source mask (B-1)S_sigma is computed once and reused for seven lanes. The three lane packs use independent Horner schedules. The literal high zero in the output pack is omitted, so their combined cost is (24m+2)M+(24m+2)A. No nonzero lane, shift or mask is discarded.

The native scale T=P^ell is computed by the displayed emitter's ordinary binary addition chain. It performs floor(log2 ell) squarings and popcount(ell)-1 other multiplications, for lambda paid multiplications. ell is fixed by the alphabet; the unbounded history duration is not an exponent operand of this source.

All native input packs are nonnegative on every positive supplied assignment. The global bound forces P>1, J>=1 and every lane below P before any binary interpretation. The complete prescribed native theorem then gives dyadic P, its final lane gives dyadic D and B, and P-1=(B-1)J gives P=B^n for n>=1. The selector checksum is carry-free because m<B, and yields exactly one letter per cell. Selected-source extraction therefore precedes history recovery. The aggregate mask and the initial mass below D meet the previously reviewed simultaneous nonnegative-history theorem.

The seven comparisons remain

    B V_i=H_i+P F_i-z_i, i=1,...,7,

with F7 aliased to F1. For dense7 the V_i are the literal dense selected actions. The native component's 15 comparisons, the global comparison and these seven comparisons total 23. The complete proof in the frozen geometry packet applies after the explicit terminal-coordinate map, so positive zeros project exactly to nonempty words ending with equal coordinates 1 and 7. Conversely every such word has a positive extension by choosing a sufficiently large dyadic D and using global_slack=P-2S>0. The input coordinates 3 and 1 differ, so the inherited universal language has no accepting empty word to lose.

## 3. Exact native boundary binding without three extra input hats

The parent receipt is native_binary_positive_scale.json, SHA256 ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628. Its example.source has 108 rows: rows 0-63 form the 64-operation certificate, while rows 64-107 are its standalone sum-of-squares finalizer. The new whole source binds the 64-row certificate and all 15 comparisons, and emits one new finalizer for all 23 comparisons. The old local finalizer is not silently counted as part of native64.

Let A_pack,M_pack,Z_pack be the three nonnegative packs. The complete native relation is applied mathematically at (T,A_pack+1,M_pack+1,Z_pack+1). Instead of emitting three separate +1 rows, the source composes those hats into its private seven-row header:

    q=16T,
    scaled_A=16A_pack, padded_A=scaled_A+12,
    scaled_B=16M_pack, padded_B=scaled_B+10,
    scaled_Z=16Z_pack, F3=scaled_Z+8.

For example, 16(A_pack+1)-4=16A_pack+12. The other two identities are 16(M_pack+1)-6=16M_pack+10 and 16(Z_pack+1)-8=16Z_pack+8. The three scaled registers have no other consumers in the parent. Therefore all header boundary values and every later comparison are exactly the composed parent polynomials on arbitrary integer assignments. In particular F3>=8 and q>=16 on the positive supplied domain.

All remaining native rows and comparisons are preserved under a fresh prefix. Native P is bound to T, not to the outer lane radix P. Every native auxiliary and computed register is prefixed, avoiding collisions with the outer terminal F1 and history names. The native count remains 33M+31A; the avoided three additions belong to the outer composition. No native equation or positive auxiliary is removed by this header simplification.

## 4. Common column sums pay the seventh action

For a constant-column alphabet, exact one-hot selection gives sum_(sigma,k) Z_sigma,k=S. Consequently, as an identity at the certified selected-history interface,

    sum_i V_i=C*S.

The column6 source computes rows 1 through 6 densely, and defines

    V7=C*S-(V1+...+V6).

After the native equations establish exact selection, this is precisely the actual seventh selected action. There is no need to give this computed intermediate a positive domain before those equations: positivity is required for the supplied coordinates and native inputs, whose construction does not depend on any V_i. All seven recurrence comparisons remain, so the preceding history theorem applies unchanged. The dense and six-row certificates have exactly the same positive zero tuples on their declared supplied coordinates for the same constant-column alphabet. Their intermediate outputs and residual polynomials need not agree away from those zeros.

**Review remark 1 (the action rewrite is not an unconditional polynomial identity).** At the formal positive outer cut H_i=1 for all seven i, with all selected words zero, take one all-ones matrix and C=7. Then S=7. The dense selected action has every V_i=0, while the reconstructed seventh output is C*S=49. These assignments violate the selector/history constraints, but disprove an off-equation identity V7_dense=V7_column6. The complete positive-zero proof uses exact one-hot selection before the rewrite; it does not replace that proof with an unconditional source identity.

The seven dense action rows cost 49mM+(49m-7)A. Six dense rows cost 42mM+(42m-6)A. Computing C*S, their five-addition sum and its subtraction costs 1M+6A, so the complete action block costs (42m+1)M+42mA. The difference is (7m-1)M+(7m-7)A, totaling 14m-8. This is a saving between two fully accounted sources of the same family, not deletion of a supposedly free aggregate equation.

## 5. Literal ledgers and examples

The closed stage ledger is:

| Stage | Multiplications | Additions/subtractions |
|---|---:|---:|
| Input, initial mass, geometry, bounds and m masks | m+5 | 16m+14 |
| Three packs | 24m+2 | 24m+2 |
| Fixed power P^ell | lambda | 0 |
| Complete native certificate | 33 | 31 |
| Dense seven-row action | 49m | 49m-7 |
| Or: six-row action with mass reconstruction | 42m+1 | 42m |
| Seven recurrences with shared terminal product | 13 | 14 |

The alternatives give the opening formulas. With 23 comparisons, computing every residual and square and summing the squares adds 23M+45A. The two single-polynomial totals are therefore

    dense7:  163m+175+lambda,
    column6: 149m+183+lambda.

Every square, fixed-coefficient multiplication, subtraction, power-chain row and final accumulation is counted. Copies and register aliases are the only free operations. No straight-line optimality or degree claim is made.

| Formal alphabet size | Variant | Certificate operations | Single-polynomial operations | Positive witnesses |
|---:|---|---:|---:|---:|
| 1 | dense7 | 274 | 342 | 44 |
| 1 | column6 | 268 | 336 | 44 |
| 8 | dense7 | 1418 | 1486 | 100 |
| 8 | column6 | 1314 | 1382 | 100 |

The receipt contains these four complete literal graphs with fixed-numeral roles, not numerical universal instantiations. Further static row censuses for m=2,3,4,16 check the same formulas. Counts for a finite set of shapes supplement the explicit all-m stage derivation; they are not a universality argument or arithmetic execution of any graph.

## 6. Validation and remaining research

The fresh emitter only reads the pinned native JSON as inert rows, creates new rows, counts operation labels and checks graph topology, supplied-coordinate disjointness, fixed-role declarations and liveness. It was not used to evaluate any arithmetic source, propagate degrees, test Pell witnesses or replay an existing builder. Every emitted row and supplied variable is live at the single final output in the four saved examples. The helper and receipt are frozen after their original metadata-only emission and must not be rerun under the standing no-replay rule.

The independent proof checks cover the complete positive projection, header boundary identities, terminal sharing, six-row reconstruction and all-m ledgers. Separate static checks authenticate the parent prefix, its comparison endpoints and actual binding consumers. The sources inherit the accepted prescribed native and positive7 universal-group theorems; their external foundations are not re-proved here.

**Open question 1 (credited sparse-action continuation).** Pascal's four-port relator decoder and root's common identity baseline reduce the required selected-source interfaces. Integrating them can reduce both the action and packing parts of this complete family, but the sparse source, its global selected-output bound and all affected native lanes must be charged and checked together. An interface reduction alone is not a gate count.

**Open question 2 (numerical universal bound).** The inherited effective group embedding specifies a fixed universal alphabet abstractly. Its concrete relator list, coefficient numerals and size m have not been materialized. The present family yields a valid finite polynomial when that fixed data is supplied, but it gives no new numerical universal bound without that step or a further compiler whose count is independent of those unmaterialized data.

**Open question 3 (credited alternative chart).** Aristotle and Riemann identified a stronger hatted global bound that can also be complete, with an appropriate positive slack shift. The current source deliberately retains the exact unshifted predecessor comparison. Its possible sharing benefits must be assessed at an emitted source cut; no additional saving is included in these ledgers.
