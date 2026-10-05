# Independent review of one aggregate range lane

The aggregate-range history theorem passes independent review, with the zero-column-bound edge case corrected before freeze. Nonnegative updates allow one masked range lane for the sum of seven histories to support simultaneous recovery of every state coordinate. The stated local range-block schedules cost 23 and 8 operations, a saving of 15 at exactly that cut. The packet does not emit a complete universal polynomial or claim a whole-source saving.

The final author pair is pinned in the accompanying receipt. All proof checking was by hand and inert reading. No scientific source, helper or saved source array was evaluated or replayed.

## 1. Exact domain and the induction

The fixed alphabet consists of seven-dimensional matrices with nonnegative integer entries. The column-sum bound Lambda is uniform over letters. K is a fixed power of two at least 2 and greater than Lambda, D is dyadic, B=KD, and the exact duration geometry P=B^n and J=sum_(j<n) B^j is separately supplied for n>=1. The initial vector z is positive with separately paid total S0<D.

The positive history words have S=sum_i H_i<P, which gives each one canonical length-n base-B digits in [0,B). Exact selected-source words must use those canonical digits before recurrence recovery, and must select exactly one actual alphabet letter per cell. The seven selected matrix outputs and all seven recurrence comparisons remain required. The exact AND relation is an external interface; its native realization and pretyping are not claimed free.

Because B and D are powers of two, the mask (D-1)J says precisely that each canonical digit of S is below D. It does not initially prove that the sum of component digits is below D. The proof correctly establishes that fact using the vector recurrences before invoking the mask at each new cell.

At the constant coefficient, both z_i and h_i(0) lie in [0,B), so the congruence forces equality for all seven coordinates. The total is S0<D and creates no aggregate carry. Assume every earlier coordinate and carry state has been recovered. The next actual state is nonnegative, and its total is bounded by Lambda times the previous actual total. The corrected uniform estimate is

    total_next <= Lambda*(D-1) < K*D=B.

Each next coordinate is consequently in [0,B). After lower recurrence coefficients vanish, reduction modulo B forces every proposed next digit to equal the actual coordinate. Their sum is below B and has no incoming carry, so it equals the next canonical digit of S and produces no outgoing carry. Only now does the aggregate mask sharpen its total to less than D. This closes the simultaneous induction without an exponential-in-duration height estimate.

After the n pre-state cells, the top coefficients give F_i=y_i(n). The endpoint total is below B, but need not be below D because the mask has no terminal cell. Soundness does not need a prior endpoint range. General nonnegative matrices can give zero endpoints, so the abstract F registers are integral; the strictly positive alphabet application separately justifies positive terminal witnesses.

**Review remark 1 (zero column bound).** The preliminary draft used `Lambda*previous_total < Lambda*D`. For the allowed zero alphabet with Lambda=0, this reads 0<0. I requested the non-strict integer bound followed by the strict K*D bound displayed above, or an explicit zero case. The correction preserves the theorem and is retained in the final author's numbered remarks. This is a proof edge-case correction, not a counterexample to the final theorem.

## 2. Completeness and the precise replacement

For a genuine finite selected word, choose a dyadic D greater than every actual total, including the endpoint. The actual digits then give positive history words because the initial coordinates are positive, even if later coordinates vanish. Their aggregate has no carries, satisfies the mask, and is less than P. The positive bound slack is P-S. Exact selection and recurrence telescoping provide the remaining local witnesses, conditional on their own component completeness theorems.

The equivalence therefore concerns genuine selected histories and their accepted-word/input projection under the specified external interfaces. It does not preserve every original witness at fixed D. Seven separate bounds h_i(j)<D do not force sum_i h_i(j)<D. Increasing D changes B, P, packed words and native witnesses, so those surrounding interfaces must permit and justify the reconstruction. No complete compiler is supplied here.

The argument is distinct from the earlier canonical-history47 induction, which starts with an independent bound on the entire actual word. Here a newly established total below D is propagated one step at a time. The scalar carry family from the preceding weighted7 packet cannot be used while omitting this new recovered-mass hypothesis.

## 3. Exact local arithmetic schedules

The closed local cut supplies P,J,D and H1 through H7. It supplies no powers or repunits for free. The old range history is H1+P H2+...+P^6 H7, computed by a six-stage Horner schedule costing 6M+6A.

For the seven-lane mask repunit, the displayed schedule uses P2=P*P, P4=P2*P2, P6=P4*P2 and

    R7=(P+1)(1+P2+P4)+P6.

These are four multiplications and four additions in total. The formula contains each power from P^0 through P^6 exactly once. The common mu=(D-1)J costs 1M+1A, and the old mask mu*R7 costs one more multiplication. The old outputs therefore cost 23=12M+11A; copying the history output into the selected-output port costs no arithmetic.

The aggregate replacement uses six additions for S=sum_i H_i and the same 1M+1A for mu. Its outputs S,mu,S cost 8=1M+7A. The saving is exactly 15=11M+4A against the stated old schedule. If S, powers or masks are already paid and shared, the actual fanouts must determine the revised difference. Neither schedule is claimed optimal, and this local comparison does not account for changed lane shifts, top scales, native truth fields or positivity obligations.

A separately needed bound S+bound=P costs seven additions and a comparison, sharing the six additions that form S. The positive7 initial mass can be paid by `a=tau2+tau`, `b=a+3`, `S0=b+b`, `D=S0+height_slack`: four additions and one positive slack. The multiplication B=K*D costs one further operation. The original 2M+1A ordinary-input loader remains unchanged. Dyadic typing and exact repunit geometry remain separate obligations.

For the constant-column-sum specialization, the additional scalar comparison `(BC-1)S=P*M_end-S0` is sound with the same mask. Its canonical initial digit must equal S0. Once a digit is recovered and is below D, its next mass is below CD<B, so scalar digit induction recovers the entire mass profile and endpoint M_end=C^n S0. This uses the masked local bound and K>C; it does not assume a free exponential-height estimate.

Exact exclusive selection gives sum_i V_i=C*S as a packed-integer identity. Summing the seven vector residuals therefore gives exactly the scalar residual when M_end=sum_i F_i. The scalar comparison together with any six vector comparisons forces the seventh, even if its privately used output-action arithmetic is not emitted. This is a replacement and needs its own paid arithmetic and terminal-mass sum. The stated three multiplications and two additions for the scalar comparison, versus two multiplications and two additions for one coordinate comparison, correctly count the rows preparing the two sides. Computing M_end costs six more additions unless shared or simplified. A final difference or sum-of-squares circuit, if required by a later compiler, is additional to these comparison-side schedules. No complete saving follows without all private consumers and new costs.

## 4. Signed carry obstruction

I supplied the two-coordinate signed counterexample to the author and independently checked its seven-coordinate embedding by hand. Set D=16, K=4, B=64, n=3, J=4161 and P=262144. Start from seven ones. The first two coordinates use, in order,

    M0=[1,2;0,-1], M1=[0,0;1,0], M2=[1,1;1,1],

and each letter acts as identity on the other five coordinates. Even the maximum absolute column sum is only 3<K. Propose first-two-coordinate cells (1,1), (3,63), (0,2), with the remaining five coordinates always one. Then

    H=(193,12225,J,J,J,J,J),
    S=33223=7+7*64+8*64^2<P.

All canonical aggregate digits are below D, so the mask holds, and all seven history words are positive. Initial total 7 is below D. The exact selected update words have first two coordinates V=(8195,8383), with the remaining five equal to J. The positive endpoint (2,2,1,1,1,1,1) satisfies every vector recurrence. The first two equalities are

    64*(8195,8383)
      =(193,12225)+(2,2)*262144-(1,1).

However, the actual first two states are (1,1), (3,-1), (0,3), (3,3), so the proposed history and endpoint are false. The negative coordinate wraps and an aggregate carry hides it. The example violates only the nonnegative-entry hypothesis of the new history argument, even retaining an absolute-column bound. It demonstrates failed exact-history recovery for signed matrices; it is not asserted to produce a false accepted input in a complete universal compiler.

## 5. Application, provenance and remaining work

For the frozen positive7 alphabet, each matrix is strictly positive and every column sum equals C. Taking Lambda=C and a fixed dyadic K>C meets the new theorem, and every actual coordinate and endpoint stays positive. The original ordinary-input column and terminal equality F1=F7 are preserved. The alphabet is still inherited as a finite effective construction, not transcribed numerically. Its coefficient actions, selectors, chronology, native range realization and geometry are not paid by this note.

The exact prior proof and metadata dependencies, declared author read spans and this review's read scope are recorded in the receipt. The weighted7 construction and its canonical-history predecessor were independently reviewed earlier in this session. The new proof and schedules were read inertly; counts and identities were checked directly, without source-array evaluation or degree propagation. Only fresh hashing and JSON metadata processing ran. No scientific helper, test, build or Git command ran, and repository and frozen predecessor bytes were unchanged.
