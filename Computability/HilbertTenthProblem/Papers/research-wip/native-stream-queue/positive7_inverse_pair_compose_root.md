# A complete positive7 source with shared inverse-pair arithmetic

Pascal's inverse-pair factorization removes exactly 144 multiplications from the complete sparse positive7 compiler. The number of additions, comparisons and positive supplied coordinates is unchanged. With r fixed presentation relators and ell=62+10r, the certificate now costs

    (276+56r+lambda(ell))M+(550+74r)A,

where lambda(t)=floor(log2 t)+popcount(t)-1. Its 23-comparison finalizer adds 23M+45A, so the complete single-polynomial source costs

    (299+56r+lambda(ell))M+(595+74r)A
      =894+130r+lambda(62+10r) operations.                 (1)

It has the same 96+10r positive existential coordinates as its sparse parent. This change preserves the entire final polynomial, for the parent's valid fixed coefficient recipe, on arbitrary integer assignments to its supplied coordinates. Consequently it also preserves exactly the same positive zero tuples and ordinary-input projection. This is a stronger correspondence than the earlier dense-to-sparse wrapper change, whose declared witnesses and native packs differed.

The universal presentation remains abstract: r and its actual coefficient list have not been materialized. The formal r=0 graph costs 903 operations, but is not claimed to be universal. Neither (1) nor the three concrete source shapes improves the complete general84 numerical bound.

## 1. Exact local identity and its paid source

The [inverse-pair proof](positive7_inverse_pair_action_pascal.md) works at the existing 52 raw paired selected-word inputs. Their slot order and retained coordinates are unchanged. Each plus/minus slot has independent integer inputs; no one-hot or positive-history assumptions are used in the local arithmetic identity.

In the signed three-coordinate representation S of G -> PGP^T, put U=[1,1;0,1] and V_t=[1,0;t,1]. The actual paired matrices are (U,U), (U V_12 U^-1,V_12), and, for t=4,8, (U V_t U V_t^-1 U^-1,V_t U V_t^-1), together with their inverses. These are fixed signed macro-letter matrices in the inherited alphabet.

The factored schedule computes the same six aggregate differences

    sum_(eight slots sigma) (A_sigma-I6)Q^-1D0 Z_sigma

as the parent's 174 literal coefficient products and 168 additions. It does so with 30 multiplications and 168 additions. The detailed algebra and every scalar instruction are in the frozen local proof. In particular, S(U) is linear, so the b,z1,z2 first-block increments can be summed before applying that common map. The a first-block increment is added afterward; it is not silently conjugated.

| Local stage | M | A |
|---|---:|---:|
| a inverse pair | 0 | 24 |
| b inverse pair before common first-block S(U) | 6 | 26 |
| z1 inverse pair before common first-block S(U) | 12 | 50 |
| z2 inverse pair before common first-block S(U) | 12 | 50 |
| Shared first-block map and all six coordinate sums | 0 | 18 |
| Complete six-output local cut | 30 | 168 |

Every fixed-coefficient multiplication and doubling is paid. The only literal multiplication constants in this local graph are 4,8,12,24,144. The output order is (a,b,c,d,e,f); the third output is a copy of its already computed accumulator, not an extra source row. All 198 rows and all 52 raw input ports are live at the six outputs.

Root independently checked the decoder and shear algebra and the shared-map ledger. [Aristotle's independent review](review_positive7_inverse_pair_action_aristotle.md) checks the complete local proof and literal schedule. No saved coefficient or source array is evaluated to establish these identities; the relation to the previously pinned coefficient tables follows from the same actual signed matrices and the handwritten representation identities.

## 2. Exact complete-source composition

The fresh root composer reads only two pinned inert JSON artifacts: the complete sparse parent and Pascal's original local graph. It never executes or imports either frozen emitter. In each saved parent graph it identifies the contiguous six-increment block: paired products, uniform relator products and their six sums. It replaces the paired portion with the 198 local rows, preserving their raw selected-word names.

Every original relator product remains literally present with the same fixed coefficient role and the same selected-word input. For the last three coordinates, each such product is added to the corresponding local paired output. There are 24r products and 24r additions. The full replacement therefore has

    (30+24r)M+(168+24r)A,

whereas the replaced block has (174+24r)M+(168+24r)A. The exact source delta is 144M and zero A, for every r>=0. Products by zero are still retained in this uniform recipe.

The six replacement outputs are bound to the parent's six old increment consumers. Every source row before the cut is copied literally. Every row after the cut is copied literally except for those six operand-name bindings. This includes the fused postprocessor, recurrence right sides, all comparison residuals, all squares and final accumulation. The positive supplied-coordinate list, lane table, initial and terminal ports, fixed-role list and all 23 comparison endpoint names are unchanged.

The local proof gives equality of the six cut polynomials over the integers. Adding the identical relator products preserves that equality. Substitution into the identical suffix then gives equality of every later boundary value and of the final polynomial on all supplied integer assignments. This is a handwritten polynomial identity argument combined with static binding inspection; it is not a symbolic evaluation of the stored arrays.

The positive-projection proof of the parent therefore transfers by the identity map on all supplied coordinates. No new native witness extension, slack shift, lane bound or one-hot argument is needed for this particular substitution. The inherited ordinary-input projection still relies on the parent's positive7/group and prescribed-native theorems. Signed intermediate arithmetic remains permitted.

## 3. Full-source ledger and formal examples

The complete stage ledger after substitution is

| Stage | M | A |
|---|---:|---:|
| Input, initial mass, geometry, bounds and masks | 13+2r | 134+20r |
| Three sparse packs | 182+30r | 182+30r |
| Fixed power P^ell | lambda(ell) | 0 |
| Complete native certificate | 33 | 31 |
| Factored increments and fused action | 42+24r | 189+24r |
| Seven recurrence right sides | 6 | 14 |
| Certificate total | 276+56r+lambda(ell) | 550+74r |
| Combined finalizer | 23 | 45 |

The full action includes the parent's 12M+21A fused postprocessor. No extra seven B-products are added to its already scaled recurrence outputs. All initial conversions, hats, selectors, pack shifts, native operations, relator roles and residual differences remain paid exactly as before.

| Formal r | ell | lambda | Certificate operations | Polynomial operations | Positive witnesses |
|---:|---:|---:|---:|---:|---:|
| 0 | 62 | 9 | 835 | 903 | 96 |
| 1 | 72 | 7 | 963 | 1031 | 106 |
| 2 | 82 | 8 | 1094 | 1162 | 116 |
| 3 | 92 | 9 | 1225 | 1293 | 126 |
| 4 | 102 | 9 | 1355 | 1423 | 136 |
| 8 | 142 | 10 | 1876 | 1944 | 176 |

The receipt saves three complete new graphs, for r=0,1,4, totaling 3357 rows. The r=2,3,8 entries are explicitly count-only consequences of the inherited shape censuses and the constant 144-operation cut replacement. They are not additional saved graphs or scientific executions.

Relative to the preceding dense-column6 family, the new exact full-source difference is

    481+168r+lambda(66+16r)-lambda(62+10r).

At the formal r=0 shape, this is 1382-903=479 operations. Relative to the immediate sparse parent, the difference is exactly 144 for every r.

## 4. Frozen artifacts, review and retained claims

The local packet consists of `positive7_inverse_pair_action_pascal.md`, its original metadata-only emitter and its first graph receipt. The complete packet consists of this note, `positive7_inverse_pair_compose_root.py` and its first composed receipt. Both emitters are frozen after their original emission and must not be replayed. The separate [complete-source review](review_positive7_inverse_pair_compose_riemann.md) binds their exact bytes and checks the full composed graphs, suffix bindings, native preservation, liveness and counts.

**Review remark 1 (valid 136-operation predecessor).** Pascal's first candidate applied the common first-block S(U) separately, costing 30M+176A for the six-output cut. It correctly saved 136 operations. Sharing that map after aggregation saves eight more additions, yielding the present 144-operation reduction. The earlier candidate was valid, not a failed proof or an additional saving to count twice.

**Review remark 2 (signed factorization is not lifted-word expansion).** The local proof factors the arithmetic of a fixed signed macro-letter. It does not replace that letter by a word of separately lifted positive matrices. Those are different operators: D0*L(I)=8D0 whereas D0*L(I)^2=64D0. Treating an identity decomposition as two lifted letters would therefore alter the decoded action. The source here computes only the proved signed local expressions inside the same outer letter.

**Review remark 3 (support containment correction retained).** The frozen complete sparse parent says retained ports are “precisely the nonzero supports.” Its separate review corrects this overstatement: a relator acting as identity has zero difference support, while the uniform source still retains four selected ports and charges its zero products. The correct condition is that every omitted port has zero coefficient and retained ports contain every nonzero coefficient. This source preserves that uniform support containment and all its paid products.

The parent's explicit counterexample to sparse Ztot=S, and its corrected inequality Ztot<=S, remain inherited. No new dense/sparse witness bijection is asserted; the same-tuple statement here concerns only the exact arithmetic substitution between the two sparse sources.

**Open question 1 (materialized universal data).** The actual universal relator words, their count r and resulting fixed coefficients remain unmaterialized. The complete-source question in Pascal's local packet is resolved by this composition and its review, while the numerical-instantiation question remains open. Formula (1) is not a numerical universal gate bound until those data are supplied or a further construction eliminates their dependence.

**Open question 2 (further local and outer sharing).** The factored schedules are not asserted optimal. Further sharing among inverse pairs, relator actions, the positive lift and pack/unhat interfaces may reduce (1), but it must preserve the exact source boundary and receive complete paid accounting. The earlier hatted global chart is still a credited alternative requiring its own emitted implementation. No degree propagation, formal degree bound or arithmetic minimality result is claimed.
