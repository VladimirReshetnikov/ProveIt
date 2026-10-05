# A complete sparse positive7 compiler with a paid selected action

The sparse selected action is now integrated into a complete positive Diophantine history source. For a fixed presentation with r relators, the alphabet has m=8+2r letters. The source retains w=52+8r selected-coordinate words and packs ell=m+w+2=62+10r prescribed-AND lanes. Put lambda(t)=floor(log2 t)+popcount(t)-1. The certificate costs

    (420+56r+lambda(ell))M + (550+74r)A.

There are 23 comparisons and 96+10r strictly positive existential coordinates. One combined sum-of-squares finalizer adds 23M+45A, giving a single-polynomial source with

    (443+56r+lambda(ell))M + (595+74r)A
      =1038+130r+lambda(62+10r) operations.                 (1)

The complete dense-column6 predecessor costs 1375+298r+lambda(66+16r) operations on the same alphabet. Thus the exact full-source difference is

    337+168r+lambda(66+16r)-lambda(62+10r).                (2)

For the formal r=0 source shape this is 1382-1047=335 operations; for r=1 it is 1681-1175=506. The universal presentation has not been numerically materialized, so neither formal shape is claimed to be universal. Equation (1) is a compiler-family count, not an improvement of the complete general84 numerical bound.

## 1. Fixed recipe and positive coordinates

Use the inherited signed6 universal group alphabet and its weighted positive7 lift. Its eight paired slots are ordered a+,a-,b+,b-,z1+,z1-,z2+,z2-, followed by a relator/inverse pair for each fixed relator. The common matrices and vectors are

    h=(1,1,1,1,1,2)^T, k=(h,1)^T,
    D0=[I6|-h], E0=[I6;0], F0=8E0-k*1_6^T,
    G_sigma=Q*A_sigma*Q^-1,
    L_sigma=kappa*k*1_7^T+F0*G_sigma*D0.

Here D0 and F0 are mathematical fixed matrices, not the outer digit height or a native auxiliary. Choose the common power of two kappa as in the weighted lift, strictly greater than 28 times every absolute row sum of G_sigma. Every L_sigma is a strictly positive integer matrix, with common column sum C=8*kappa. Fix a power of two K>max(C,m). These choices must use the whole actual alphabet, including its relator letters.

The paired coefficient table is the literal table authenticated in the paid-action packet. For a relator slot, each row (u,v,t) of S(rho(R_j)^+/-1)-I3 is composed with the last-block decoder to give

    (u+v+2t, v, t, -u-2v-4t)

on ports 4,5,6,7. The emitted uniform family keeps all 24r such fixed-coefficient products, including any that become zero after the relator words are materialized. The named role kappa_minus_one is the fixed integer kappa-1. Its multiplication by the variable history sum is charged. These roles are fixed compiler numerals, not extra existential variables, and they cannot be assigned arbitrary independent integers outside this recipe.

For the universal program slice, alpha=12*2^(p+1) and gamma=12*2^p+1 have their inherited fixed meanings. The ordinary input is x>0. The source computes

    tau=alpha*x+gamma, tau2=tau*tau,
    z=(3,tau,tau2,2,tau,tau2,1),
    S0=2*tau2+2*tau+6.

The input loader costs 2M+1A; the initial mass costs three further additions. The alphabet, its relators and its lift constants are fixed independently of the ordinary input and program slice.

The positive supplied coordinates are seven history words H_i, six terminal words F_1,...,F_6, m selector hats, w retained selected-word hats, two slacks, and 21 native auxiliary witnesses. The terminal port for coordinate 7 is literally F_1. Thus

    7+6+m+w+2+21=96+10r.

All native names have a fresh pell_ prefix. Signed coefficients and computed signed intermediates are allowed in an integer polynomial source; the positive domain restriction applies to its supplied witnesses and x. In particular, no sign restriction is imposed on the six computed action increments.

## 2. Exact sparse lanes and prescribed native block

The retained coordinate sets, in the above slot order, are

| Slots | Retained ports |
|---|---|
| a+ and a- | 2,3,4,5,6,7 |
| b+ and b- | 1,2,3,4,5,7 |
| z1+,z1-,z2+,z2- | 1,2,3,4,5,6,7 |
| Each relator or inverse | 4,5,6,7 |

These are precisely the nonzero supports of the full signed action difference after the decoder; no omitted product is consumed elsewhere. Unhat the supplied selectors and retained words, writing S_sigma=selector_hat_sigma-1 and Z_sigma,i=selection_hat_sigma,i-1. Define

    J=sum_sigma S_sigma, D=S0+height_slack, B=K*D,
    P=(B-1)*J+1, S=sum_i H_i,
    Ztot=sum_retained Z_sigma,i, mu=(D-1)*J,
    S+Ztot+global_slack=P.                                 (3)

The one prescribed-AND call has, in order, m Boolean lanes (S_sigma,J,S_sigma), w retained-selection lanes (H_i,(B-1)S_sigma,Z_sigma,i), the aggregate lane (S,mu,S), and the height lane (D,D-1,0). Every per-letter mask is paid once and reused. The three packs use independent Horner schedules at radix P. Their highest output coefficient is the literal zero, so the output pack starts one lane lower. Their total cost is (3ell-4)M+(3ell-4)A; no other top field is suppressed.

The source computes T_native=P^ell by the binary chain with lambda(ell) multiplications. This is a fixed exponent determined by r; the unbounded history length is not a source exponent operand. The pinned native certificate has 64 rows, 15 comparisons and 21 positive auxiliaries. Compose its positive input hats into the same private header used in the complete dense source:

    q=16*T_native,
    scaled_A=16*A_pack, padded_A=scaled_A+12,
    scaled_B=16*M_pack, padded_B=scaled_B+10,
    scaled_Z=16*Z_pack, native_F3=scaled_Z+8.

These are the identities 16(A_pack+1)-4=16A_pack+12, 16(M_pack+1)-6=16M_pack+10 and 16(Z_pack+1)-8=16Z_pack+8. The three private scaled registers have no additional consumers. All remaining native rows and all comparison endpoints are preserved under the prefix, and the certificate still costs 33M+31A. Its old 44-row local finalizer is replaced by one finalizer for all 23 comparisons.

All raw packs are nonnegative on every positive supplied assignment, before the equations are imposed. On a zero, (3) forces P>1, hence J>=1 and B<=P. It gives S<P and Ztot<P, while each selector is at most J and each selection mask at most P-1. Since K>=2, D<P, and mu<P as well. These inequalities establish the native lane bounds before interpreting the selected action.

The native theorem gives dyadic T_native and hence dyadic P. The last lane forces D AND(D-1)=0, so D and then B are dyadic. Repunit divisibility P-1=(B-1)J gives P=B^n with n>=1 and J=sum_(j<n) B^j. The Boolean lanes restrict each selector to those cell positions. Their sum is J and m<B, so the checksum has no carry and gives exactly one label per cell. Each retained selected word is therefore its canonical coordinate selection.

## 3. Complete positive projection with omitted products

Write H_i=sum_(j<n) h_i(j)B^j. In the proof only, define the omitted coordinate selections by the same certified one-hot bits e_sigma(j):

    Ztilde_sigma,i=sum_(j<n) e_sigma(j)*h_i(j)*B^j.

For retained ports this is exactly the supplied unhatted Z_sigma,i. The complete virtual family satisfies sum_sigma Ztilde_sigma,i=H_i. These proof objects add no supplied witness, source row or native lane.

The structural action theorem shows that the omitted ports have zero coefficient in (A_sigma-I6)Q^-1D0. Consequently the six paid increments a,b,c,d,e,f equal the full virtual sum of these differences. Since F0*D0=8I7-k*1_7^T, the actual selected positive action is

    V=sum_sigma L_sigma*Ztilde_sigma
      =8H+(kappa-1)k*S+F0*Q*(a,b,c,d,e,f)^T.              (4)

Equation (4) uses exact selection and its partition identity. It is not a claim about arbitrary unrelated history and selection fields. The source's postprocessor realizes (4), and its consumer fusion realizes B*V_i by unconditional polynomial identities in these displayed arguments. It enforces all seven recurrences

    B*V_i=H_i+P*F_i-z_i, i=1,...,7,

where F_7 is F_1. There are no other consumers requiring the unscaled V_i.

The simultaneous nonnegative-history theorem now applies to the actual positive matrices L_sigma. Its initial mass is S0<D. If the current genuine mass is at most D-1, the next mass is at most C(D-1)<KD=B; each next coordinate is therefore below B. The recurrence equations recover those next digits simultaneously, and the aggregate lane sharpens their total to below D. This induction starts from z, recovers every history cell without a carry, and identifies the top terminal coefficient. Its proof uses the nonnegative matrices in (4), not a positivity claim about each signed intermediate used to compute (4).

Conversely, from any nonempty accepted trajectory choose a dyadic D above all its masses. Supply its histories and terminals, its one-hot selectors and retained selections. Then

    0<=Ztot<=S< P,
    S<= (D-1)J,
    global_slack=P-S-Ztot >= P-2S
      >=((K-2)D+1)J+1>0.

The inequality Ztot<=S follows by summing the selected subset of nonnegative coordinates at every cell. It does not require an equality of sparse and full masses. All history and terminal words are positive because z and the actual letters are strictly positive. Zero selections receive hat 1. The complete native converse supplies fresh positive auxiliary witnesses at the new packs and scale. Thus the sparse source has exactly the ordinary-input projection of accepted nonempty words. The initial coordinates 3 and 1 differ, so the inherited universal acceptance condition has no accepting empty word to lose.

**Review remark 1 (retained false dense identity).** The claim Ztot=S is false for sparse selections. At a single cell labelled a+ with all seven coordinates equal to 1, the six retained coordinates sum to 6, while the full mass is 7. This is an explicit local interface counterexample, not a claim that this cut is a universal input. Completeness uses Ztot<=S and the exact slack in (3).

**Review remark 2 (scope of witness correspondence).** Dense and sparse ordinary-input projections agree, but the tuple of declared witnesses changes: dense-column6 has 100+16r coordinates and this source has 96+10r. Its native packs and scale also change, requiring the converse theorem to extend native witnesses afresh. A claim that the same full supplied-coordinate tuple is preserved is therefore not the statement proved here. By contrast, within either fixed wrapper, sharing F_7=F_1 is the simple positive coordinate bijection that restores or deletes that equal coordinate. No impossibility of an abstract bijection between differently encoded witness sets is claimed.

## 4. Paid action and closed stage ledger

The six paired increment rows have 174 nonzero fixed-coefficient products and 168 accumulation additions. Every row is nonempty. Keeping all uniform relator terms adds 24r products and 24r additions. This census is tied literally to the pinned finite coefficient receipt; no saved coefficient arithmetic is evaluated by the emitter.

For clarity, the fused postprocessor uses

    T=(kappa-1)*S-(a+b+c+e+f+5d), E=8B,
    BT=B*T, Ed=E*d, BU=BT+Ed, BV=BU+Ed.

It outputs E times H_i plus the increment where present, followed by offsets (BV,BT,BT,BV,BT,2BT,BU). The increment list is (a,b,c,0,e,f,0). Forming the five-term sum costs four additions; forming and incorporating 5d costs 1M+1A; the baseline and subtraction cost 1M+1A. E,BT,Ed cost 3M, and BU,BV,2BT cost 3A. The five inner additions cost 5A; the seven products and seven final additions cost 7M+7A. Thus the fused postprocessor costs exactly 12M+21A, and the complete selected-action block is (186+24r)M+(189+24r)A.

Only six P*F_i products are needed on the right sides, since recurrence 7 reuses P*F_1. Their seven additions and subtractions cost 14A. There is no extra B-product on the already scaled action outputs.

| Stage | M | A |
|---|---:|---:|
| Input, initial mass, geometry, bounds and masks | 13+2r | 134+20r |
| Three sparse packs | 182+30r | 182+30r |
| Fixed power P^ell | lambda(ell) | 0 |
| Complete native certificate | 33 | 31 |
| Six increments and fused action | 186+24r | 189+24r |
| Seven recurrence right sides | 6 | 14 |
| Certificate total | 420+56r+lambda(ell) | 550+74r |
| Single combined finalizer | 23 | 45 |

The first stage is (m+5)M+(2m+2w+14)A: selector unhats and checksum cost 2m-1 additions, retained-word unhats and their total cost 2w-1, and every remaining bound, initial mass, mask and seven-word sum is charged. The global comparison, 15 native comparisons and seven recurrences total 23. Their residuals, squares and final accumulation cost 23M+45A. Copies and explicit aliases are the only zero-cost data movements.

## 5. Literal source artifacts and validation scope

The fresh metadata-only emitter is `positive7_complete_sparse_compiler_root.py`, 14595 bytes, 309 lines, SHA256 `923283521c4d15d717424196802564b02d3efd845b8de474370ae01660d6f9e9`. Its first receipt is `positive7_complete_sparse_compiler_root.json`, 554670 bytes, 28901 lines, SHA256 `2c7e2b2d2345150644b47701eed9434eabad7159f0067154b6666750e2b48e3a`. Both are frozen after that original emission; do not execute or import the emitter again.

It reads only two frozen data inputs: native_binary_positive_scale.json, SHA256 `ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628`, and positive7_paired_coefficients_fresh_root_check.json, SHA256 `3c101ed4aa971e5ba53fa1a386322cb810ac281f91be9b0b0ebdd8cfa3b59d63`. The latter came from an original fresh scalar coefficient check before that earlier packet was frozen. Here it is read only as literal coefficient data; neither checker nor any supplied source is replayed.

| Formal r | m | w | ell | lambda | Certificate operations | Polynomial operations | Positive witnesses |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 8 | 52 | 62 | 9 | 979 | 1047 | 96 |
| 1 | 10 | 60 | 72 | 7 | 1107 | 1175 | 106 |
| 2 | 12 | 68 | 82 | 8 | 1238 | 1306 | 116 |
| 3 | 14 | 76 | 92 | 9 | 1369 | 1437 | 126 |
| 4 | 16 | 84 | 102 | 9 | 1499 | 1567 | 136 |
| 8 | 24 | 116 | 142 | 10 | 2020 | 2088 | 176 |

Complete literal graphs for r=0,1,4 contain 3789 rows in total. All their rows and supplied coordinates are syntactically live and topologically closed; operation labels and fixed-role names are explicitly recorded. The other three rows of the table have shape censuses, not saved complete graphs. These finite metadata checks supplement the all-r stage proof; they do not establish the projection by running examples.

The independent projection and ledger companion is [Aristotle's sparse outer schedule](positive7_sparse_outer_schedule_aristotle.md). Complete literal-source authentication is recorded separately in [Riemann's review](review_positive7_complete_sparse_compiler_riemann.md). The source arithmetic, coefficient arrays and native witnesses have not been evaluated, and no source degree has been propagated. The inherited group-universality and complete native theorems remain dependencies; their external proofs are not re-audited by this packet.

## 6. Preserved questions and continuation

**Open question 1 (numerical universal instance).** The abstract effective universal presentation still needs its actual relator list, r and coefficient numerals. Formal r=0 supplies no evidence that eight paired slots alone are universal. The complete sparse source resolves the emitted-source portion of the paid-action packet's question and of the dense compiler's credited sparse continuation; their numerical-instantiation portion remains open. No numerical improvement over general84 and no degree bound is inferred.

**Open question 2 (credited paired-generator sharing).** Pascal is investigating whether the eight paired letters can share transvection calculations and inverse combinations more cheaply than the 174 separately charged coefficient products. A handwritten candidate is being developed. Its exact action identity, port support, complete paid schedule and effect on this wrapper require independent proof and emitted-source review before any further saving can be claimed here.

**Open question 3 (alternative charts and degree).** The credited hatted global chart from the dense packet may permit additional packing or unhat sharing. The current complete source keeps every explicit unhat and the exact unshifted bound (3). No such further saving, arithmetic optimality, degree propagation or automatic transfer of dense native witnesses is included in (1).
