# One aggregate range lane for nonnegative matrix histories

Root proposed replacing seven separate state-range lanes by one lane for the sum of the seven history words. The proposal is sound for nonnegative matrix updates with a fixed bound on column sums. The simultaneous recurrence proof itself excludes carries in that aggregate, so no independent duration-dependent estimate such as B>C^n H0 is required. Initial-mass typing, dyadic geometry, exact selected-source products and all transition comparisons remain explicit hypotheses.

The result is a conditional unbounded-history interface, not an emitted complete universal polynomial. A fully stated local construction replaces a23-operation seven-lane range block by an8-operation aggregate block. Shared powers and surrounding native packing can change that local comparison; no full-source operation count is inferred. The accepted positive7 alphabet is an application, with column bound Lambda=C and its unchanged three-operation input loader.

## 1. Exact interface and paid assumptions

Let M_sigma be a fixed finite family of7-by-7 matrices with nonnegative integer entries. Let Lambda be an integer bounding every column sum of every letter. Choose a fixed power of two K>=2 with K>Lambda. Let D be a positive power of two and B=KD. Suppose the surrounding geometry supplies

    n>=1, P=B^n, J=1+B+...+B^(n-1).                          (1)

The requirement that B is dyadic is necessary for the blockwise interpretation of the bitwise mask below; the choice of dyadic K makes it explicit. The initial vector z is positive integral and must satisfy the separately paid bound

    S0=sum_i z_i < D.                                        (2)

Supply positive history words H_i, i=1,...,7, with S=sum_i H_i<P. This may be supplied by a global positive bound already containing all H_i, or by the one comparison S+bound=P with bound>0. Consequently every H_i has canonical digits

    H_i=sum_(j=0)^(n-1) h_i(j)B^j, 0<=h_i(j)<B.               (3)

Assume a separately paid selector interface supplies exactly one letter sigma(j) at each cell and exact selected-source words

    Z_sigma,k=sum_j [sigma(j)=sigma] h_k(j) B^j.              (4)

This uses the canonical digits(3), before any history recurrence is established. The selectors and these digitwise products are not ordinary products of packed words and are not free gates.

Compute the selected output words

    V_i=sum_(sigma,k) M_sigma,ik Z_sigma,k,

and retain all seven recurrence comparisons

    B V_i=H_i+F_i P-z_i.                                     (5)

The F_i are terminal integer registers. For a general nonnegative alphabet they may be0; for the strictly positive alphabet and positive initial vector considered below they are positive. No prior upper bound on F_i is used in soundness.

Replace seven separate range lanes by the single AND interface

    S AND ((D-1)J)=S.                                        (6)

The native realization of(6), including its pretyping and positive truth fields, remains to be supplied by a complete compiler. This theorem takes the exact bitwise identity as its interface, not as an uncharged primitive in a universal operation ledger.

## 2. Simultaneous recovery prevents hidden aggregate carries

Because D and B are powers of two and D<=B, the mask (D-1)J has the low log2(D) bits in every base-B cell set. Since S<P, equation(6) is exactly the statement that each canonical base-B digit a(j) of S lies below D. This assertion alone need not bound sum_i h_i(j): component histories could add with carries. The recurrences remove that possibility.

Follow the selected word mathematically from y(0)=z using y(j+1)=M_sigma(j)y(j). The proof simultaneously recovers all seven coordinates and the carry state of their sum.

At cell0, the constant coefficient in(5) gives h_i(0) congruent to z_i modulo B. Both are in[0,B), since z_i<=S0<D<B, so h_i(0)=z_i for every i. Their total is S0<D; hence adding the seven words creates no carry out of the initial cell, and a(0)=S0.

Suppose cells through j-1 have been recovered, their actual totals are below D, and no carry enters cell j, where1<=j<n. All lower recurrence coefficients vanish exactly. Exact selection(4) identifies the next coefficient discrepancy with

    y_i(j)-h_i(j).

Nonnegativity and the column-sum bound give

    sum_i y_i(j)
       =sum_k (sum_i M_sigma(j-1),ik) y_k(j-1)
       <=Lambda sum_k y_k(j-1)<=Lambda(D-1)<K D=B.              (7)

Every y_i(j) is therefore in[0,B). Reduction of the corresponding residual modulo B after removing lower powers forces h_i(j)=y_i(j), simultaneously for all coordinates. Since their total is below B and no carry entered, no carry leaves this cell. Thus a(j)=sum_i y_i(j). Equation(6) now sharpens that total to a(j)<D, completing the induction.

After all n pre-state cells are recovered, the top coefficient of(5) forces F_i=y_i(n). Its total is also below B by(7), but it need not be below D: there is no terminal digit in the range mask. The top-coefficient argument needs no advance sign or range assertion about F_i.

This proves soundness without using any bound exponential in n and without assuming that aggregate addition was carry-free. At each cell, the preceding recovered total makes the next actual total smaller than B; only after individual recovery does the aggregate AND sharpen it below D. That order is essential.

**Review remark 1 (the zero-alphabet endpoint of the bound).** The preliminary display used the strict step Lambda*previous_total<Lambda*D. That step is false when Lambda=0: it reads0<0 for an all-zero alphabet. The corrected bound in(7) uses integrality, previous_total<=D-1 and Lambda>=0, then Lambda(D-1)<KD=B since K>Lambda and D>0. It covers the zero alphabet without changing the theorem. Terminal zero coordinates remain permitted in the general interface, as already stated in Section1.

## 3. Completeness and scope of equivalence

For any genuine finite selected word with the intended terminal predicate, follow its nonnegative trajectory. Choose a power-of-two D larger than S0 and every actual total through the endpoint, and set B=KD and P=B^n. Define H_i and Z_sigma,k by their actual digits. Every H_i is positive because its initial digit is positive. At every cell the sum of actual digits is below D<=B, so S<P and(6) holds. Recurrence telescoping gives(5), and the bound slack P-S is positive. The required selector and native witnesses still depend on the separate completeness theorem of those components.

Consequently the one-range-lane interface describes exactly genuine selected histories, conditional on its listed geometry and selected-source contracts. In a completed compiler it would preserve the projection to accepted words and ordinary inputs. It is not a bijection preserving D and every old witness: seven individual bounds h_i(j)<D do not imply the stronger aggregate bound sum_i h_i(j)<D. Completeness may increase D and therefore change B,P, all packed words and native witnesses.

The proof differs from the older canonical_history47 method, which pays an independent actual-word height bound before beginning digit recovery. The current nonnegative induction instead propagates a fresh below-D aggregate bound at every pre-state cell. This is why the scalar mass-profile counterexamples in positive_matrix_weighted_mass7_aristotle do not apply: they fail the new requirement that each preceding recovered mass is below D with K>Lambda.

**Review remark 2 (signed updates can hide aggregate carries).** Riemann supplied a two-coordinate example; the following direct extension uses exactly seven positive history words. Set D=16,K=4,B=64,n=3,P=262144,J=4161. The initial vector is seven ones, with mass7<D. On the first two coordinates use successive letters

    A0=[1,2;0,-1], A1=[0,0;1,0], A2=[1,1;1,1],

and let every letter act as the identity on the other five coordinates. Even the maximum absolute column sum is only3<K. Propose first-two-coordinate cells (1,1),(3,63),(0,2), with every other cell coordinate1. This gives

    H=(193,12225,J,J,J,J,J),
    S=33223=7+7B+8B^2,
    V=(8195,8383,J,J,J,J,J),
    F=(2,2,1,1,1,1,1).

All histories, output words and terminal coordinates are positive, S<P, and the base-B digits7,7,8 are below D. Thus S AND ((D-1)J)=S. The selected-output coefficients in the first two coordinates are (3,-1),(0,3),(2,2), giving exactly the displayed V, and every recurrence(5) holds. For instance BV1=524480=193+2P-1 and BV2=536512=12225+2P-1; on each extra coordinate BJ=J+P-1. Nevertheless the actual first-two-coordinate trajectory is (1,1)->(3,-1)->(0,3)->(3,3), so both the proposed history and endpoint are false. This refutes extension to signed updates even with a bound on absolute column sums. It is a counterexample to this conditional history interface, not a full native/universal false-positive claim.

## 4. An explicit local range-block comparison

Specify a closed local input cut consisting of already paid ports P,J,D,H1,...,H7. Powers P^2,P^4,P^6 and repunits are not additional free ports. In this comparison the old seven-lane block is

    R_H=H1+P H2+...+P^6 H7,
    mu=(D-1)J,
    R_M=mu(1+P+...+P^6), R_Z=R_H.                            (8)

It implements individual bounds in seven distinct lanes. Use the following explicit schedules:

* Horner construction of R_H:6M+6A.
* P2=P*P, P4=P2*P2, P6=P4*P2; then
  R7=(P+1)(1+P2+P4)+P6:4M+4A in total.
* mu=(D-1)J:1M+1A.
* R_M=mu*R7:1M. R_Z is a copy.

Thus this local old schedule costs23=12M+11A. The new block is

    R_H=S=H1+...+H7, R_M=mu, R_Z=S.                          (9)

It costs six additions for S and the same1M+1A for mu, totaling8=1M+7A. Against precisely the stated schedule, the local saving is15=11M+4A. If S is already an explicitly computed paid register of a surrounding global bound, (9) needs only the two common mu operations at that cut. If powers, old R_H, repunits or masks are already shared elsewhere, the baseline savings must likewise be recomputed from those actual consumers. These are valid schedules, not optimality claims.

The construction of the seven-word global bound S+bound=P takes seven additions and one comparison if not already present; the six additions producing S can be shared with(9). Changes to whole-word lane shifts, the outer top scale, native truth fields and their positivity proofs are not counted here. No actual saved universal source is claimed to lose15 operations merely from this local table.

## 5. Application to the positive7 input and alphabet

The frozen weighted7 packet supplies a fixed strictly positive integer alphabet L_sigma with every column sum C. Take Lambda=C, choose any fixed dyadic K>C, and use the input

    z=(3,tau,tau^2,2,tau,tau^2,1),
    S0=2tau^2+2tau+6.                                        (10)

The three-operation loader scaled=alpha*x,tau=scaled+gamma,tau2=tau*tau is unchanged. If an actual arithmetic source must establish(2), one explicit paid extension is

    a=tau2+tau; b=a+3; S0=b+b; D=S0+height_slack,

where height_slack is a positive supplied witness. This costs four additions, and B=K*D costs one further multiplication. Dyadic typing of D is still a geometric obligation; completeness can choose D dyadic by its positive slack. This local extension is stated to prevent treating the ordinary-input initial-mass bound as free. It is not a complete source accounting.

At genuine positive7 histories every coordinate and endpoint is positive, so the terminal registers can use the positive domain. The inherited endpoint remains F1=F7. Selectors over its finite but unmaterialized fixed alphabet, paid coefficient actions, chronology, native realization of(6), and exact dyadic repunit geometry are still required. The argument works for all finite durations without a separate certificate for C^n; it does not remove those other interfaces.

For this constant-column-sum specialization, there is also an exact alternative recurrence layout. Define M_end=sum_i F_i and retain the aggregate comparison

    (BC-1)S=P*M_end-S0.                                      (11)

With S<P, the mask(6), S0<D and K>C, scalar digit induction alone recovers the genuine mass digits C^j S0 and endpoint M_end=C^n S0: the next mass from a recovered below-D digit is below CD<B. Unlike a free scalar mass profile, this uses the local mask bound and K>C at each cell, so no exponential-height hypothesis is supplied.

Moreover exact exclusive selection and the column sums give sum_i V_i=C*S as an equality of packed integers. Consequently the sum of the seven vector residuals equals the aggregate residual(11). Retaining(11) and any six vector comparisons forces the seventh comparison algebraically. The soundness theorem therefore applies unchanged. One may omit arithmetic used only to construct V7 if that output has no other consumers; exact positive endpoint recovery is then inherited from the same proof.

This is a replacement of one comparison, not an automatic deletion of one. For example, with S,S0,M_end already paid, the literal arithmetic preparing the scalar comparison computes BC, BC-1, (BC-1)S, P*M_end and P*M_end-S0, costing3M+2A. A literal coordinate comparison(5), once V7 is paid, costs2M+2A. Computing M_end needs six additions unless shared or otherwise simplified. These costs prepare the two sides of each comparison; forming their difference or a polynomial finalizer remains additional arithmetic in both cases. Thus any saving depends on the actual private V7 action arithmetic, these mass-sum consumers and the whole source. No cost-free aggregate residual or numeric complete saving is claimed.

**Open question 1 (credited full-source task).** Root proposed this aggregate induction to obtain a paid-history advantage rather than only an input-loader improvement. The theorem removes six range lanes at its precise nonnegative selected-history interface. A complete ordinary-input positive-integer compiler using it has not been emitted in this packet. The next step must implement all remaining hypotheses and verify every changed packed consumer and pretyping inequality before claiming a global gate reduction.

## 6. Scope and provenance

The proof is handwritten. It uses the accepted weighted7 substrate and the earlier canonical_history47 method as precisely stated prior interfaces. The actual older signed atomic matrix histories are not covered by merely substituting their signed matrices into(7); nonnegative update entries are used to bound each next coordinate by the next total.

Exact proof hashes and read scopes are supplied in the companion metadata. No supplied, archived, committed, predecessor or frozen helper was executed or imported, no saved source array was evaluated or degree-propagated, and no scientific sample or build was run. Only fresh byte/metadata work is used; all new files remain in/tmp, with no repository or Git changes.
