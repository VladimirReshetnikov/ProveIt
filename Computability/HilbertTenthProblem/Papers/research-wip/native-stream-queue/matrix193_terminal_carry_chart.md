# Positive terminal carries remove24 matrix gates and four witnesses

The four complete matrix constructions cost **1,544 /1,541 /1,541 /1,538 operations**, with **141 /140 /140 /139 positive witnesses**. Each saves4 multiplications and20 additions from the [grouped-power parent](matrix193_grouped_power_composition.md). Their exact degrees are **35,587 /53,345 /53,347 /71,105**: the flow and both-controller charts lose two degrees.

The new positive coordinates leave middle coefficients determined modulo Q. That ambiguity changes only terminal fields. The shared terminal fields and the fixed matrix bounds still force the two actual terminal rows to agree. This preserves the ordinary-input language on every valid fixed-program slice. It does not preserve every parent witness coordinate or assert identical complete polynomials. The established universal84 bound is unchanged.

The [fresh helper](matrix193_terminal_carry_chart.py) emits all four full arrays in the [receipt](matrix193_terminal_carry_chart.json). Frozen programs are authenticated as inert bytes only; none is imported or executed.

## 1. Complete source edit

Retain the physical packing, native kernel, coefficient words, two block bounds, four low-tail bounds, four history equations and controller/input constraints. Use the same D,c0=D−1,B=KD,P=(B−1)J+1,Q=CP with C=2^93. The fixed block lengths remain l_X=144,l_Y=194 and T_i=Q^(l_i−1).

For each of four coefficient products, replace the two old positive coordinates dot_hat,high_hat by positive ports named `*_dot*_raw_positive` and `*_dot*_negative_high`. Write them p_i,h_i. The low coordinate and its positive complementary slack remain unchanged. Replace

    dot=dot_hat−Qhalf,       high=high_hat−T_half,
    A_i(Q)*U_block=low+T_i*(dot+Q*high)

by

    A_i(Q)*U_block=low+T_i*(p_i−Q*h_i).                 (1)

Delete the four equations dot_hat+dot_slack=Q and their four positive slack ports. The four dot-centering and four high-centering producers disappear. Multiplication by Q remains paid; its following addition becomes subtraction at the same cost. All half-scales remain live through the bounded low tails.

Each removed upper-bound equation saves its one-addition producer, residual subtraction, square and one SOS addition:1M+3A. Four such removals save4M+12A; deleting eight centering subtractions gives the full4M+20A saving. Counts below come from the complete emitted arrays and backward liveness.

The helper traces the actual finalizer from the output through the sum of residual squares. It authenticates every residual and square exactly once and its private consumer boundary. The three chart listings interleave these nodes with outer producers, so the edit does not assume a contiguous finalizer suffix. It retains the other producers and emits the smaller complete finalizer after their dependencies.

## 2. Typing and canonical convolution still precede extraction

At a positive integer zero the output N*(1+SOS)−1 forces N=1 and every remaining outer residual to vanish. Here N is the unchanged product of the native factors. The [balanced-output proof](matrix193_balanced_output_scout.md) obtains native positivity, the dyadic bootstrap, one-hot controller typing and joined AND using only the block/global bounds and packing functions. None uses a dot upper bound or the extraction equations. Those inputs and constraints are retained here.

Thus P=B^t for an integer t>=1, each history digit h_i(j) lies in[0,2D−1], and the selected signed words obey |U_r|<=D J<P. For each fixed coefficient word the canonical convolution is

    A_i(Q)*U_block=low_true_i+T_i*(d_i+Q*high_true_i),
    |low_true_i|<T_i/2, |d_i|<Q/2, |high_true_i|<T_i/2.  (2)

These are the same signed tail bounds as in the balanced and [bounded-high](matrix193_bounded_high_output.md) proofs. The Y fixed-table product excludes the separately retained, exact SWITCH correction; that correction is added to the Y history increment afterward.

The low positive/slack equation still puts low in the open interval(−T_i/2,T_i/2). Subtracting(1) and(2) shows their low values differ by a multiple of T_i. Their difference has absolute value less than T_i, so low=low_true_i. The remaining equality gives an integer k_i such that

    p_i=d_i+k_i Q,       −h_i=high_true_i−k_i.         (3)

Since p_i>0 and d_i<Q/2, k_i cannot be negative. The proof does not require a bound on its positive size. Nor does it identify p_i with the canonical dot.

The computed LOAD/SWITCH-hat variants retain their earlier positive polynomial definitions and their identities for eliminated controller/population equations. These depend on neither the dot/high ports nor their removed bounds. The same bootstrap and typing argument therefore applies separately to all four complete arrays.

## 3. Terminal carries do not change accepted words

Include the unchanged SWITCH correction where appropriate and denote the canonical increment by delta_true_i. The retained history equations become

    B*(H_i+delta_true_i)=H_i+F'_i P−I_i,
    F'_i=F_col(i)−BC*k_i,                              (4)

because Q=CP. X and Y coordinate0 share F_even; coordinate1 shares F_odd. F'_i is an integer and need not be positive.

The [atomic chronology proof](matrix193_atomic_context_packing.md) recovers initial and interior coefficients successively modulo B. This argument remains valid with integer F'_i of either sign: its term first appears at P=B^t and does not affect any earlier coefficient. The initial discrepancy is less than2D<B. At a first unrecovered interior cell, the discrepancy is less than or equal to(Lambda+1)D<B, where Lambda is the largest absolute matrix column sum and the valid recipe requires K>Lambda+1. Hence every typed pre-state and matrix update is recovered.

At the last cell, write its signed pre-state coordinates as z_j=h_j−c0. They lie in[−(D−1),D]. The actual shifted terminal coordinate recovered from the top coefficient is

    F'_i=c0+(z M)_i.

Consequently

    |F'_i| <= D−1+Lambda*D < B.                        (5)

This handles negative terminal coordinates; no terminal positivity has been assumed during decoding.

For each paired X/Y coordinate, equation(4) gives

    F'_X−F'_Y=BC*(k_Y−k_X).

The left side has absolute value less than2B by(5). Since C>=16, the integer difference of carries must be zero. Thus k_X=k_Y and the actual terminal coordinates agree. Subtracting the common shift c0 yields equality of the signed terminal rows.

The controller still gives LOAD* SWITCH TILE*, with the zero IDLE slot fixed. The typed SWITCH pre-state, LOAD-growth estimate and retained or identically satisfied population equation still force the LOAD count to equal the ordinary input x. The existing fixed-program membership bridge therefore proves soundness. One-cell SWITCH histories and zero selected blocks cause no exception to this argument.

## 4. Positive completeness and exact polynomial contract

Start from any positive zero of the bounded parent. Its canonical values are

    d_i=old_dot_hat_i−Qhalf,
    high_true_i=old_high_hat_i−T_half_i.

Choose the common integer k=T_Y=Q^193, an already computed packing polynomial. Since T_Y>=T_X and Q>0, set

    p_i=d_i+kQ,
    h_i=k−high_true_i,
    F_even_new=F_even_old+BC*k,
    F_odd_new=F_odd_old+BC*k.                            (6)

The inequalities in(2) give p_i>0 and h_i>k/2>0. The terminal fields increase by a positive integer. All other retained coordinates are kept; forget the four old dot slacks. Equations(1) and(4) are preserved because the terms kQ and Qk cancel and BkQ=BCkP. Every native cut and remaining residual agrees.

For any formal common k, with no zero or sign assumption, the exact source contract is

    F_new(map)=F_parent−N*sum_(four removed bounds) r_bound². (7)

The helper expands the affected dependency cones and the complete finalizers as sparse integer polynomials, binding Q to the actual CP and Qhalf to(C/2)P. Unchanged source values are shared formal cuts. The raw-dot/high/terminal substitutions in(6), with arbitrary formal k, prove all retained residual equalities and(7) exactly. This is more than a comparison of local expressions, but it is not equality of the two polynomials on identical coordinates.

Conversely a new positive zero decodes an accepted word by Section3. The bounded parent's completeness theorem constructs a parent zero at the same ordinary input, possibly choosing fresh height, histories and native witnesses. Its actual terminal F'_i might not be positive at the original height. Therefore the theorem claims ordinary-input projection equivalence, not a bijection preserving common witness coordinates.

The map(6) is a mathematical witness construction, not an extra uncharged operation in the new source. The new source contains only the paid rows explicitly emitted. No variable exponent is used:193 is a fixed table constant.

## 5. New degree proof

Removal of the bounded high offset changes the highest term of the extraction RHS. Old exact degrees cannot simply be transferred.

Let s=deg Q, e=deg E_LOAD and D_top=x+height_slack. Exact expansion of every pure-Q subcircuit is used before degree propagation; this includes cancellation in the repunit and coefficient evaluations. The length194 Y product has nonzero leading form

    −a0*D_top*S_LOAD_top*Q_top^386,

where the first reversed coefficients are a0=−490 and271. The two polynomials have exact degree386s+1+e. The new RHS has degree at most194s+1, strictly lower. All other retained residuals have degree no greater than this Y value, as checked against the complete sources. A sum of real squares doubles the maximal degree without cancellation.

The native polynomial is unchanged and contains none of the changed extraction or terminal coordinates. Its uniform degree, from the pinned native/chart proof, remains16986s+67. The leading LOAD and Q forms for the four charts are nonzero for every valid fixed recipe. Thus:

| Variant | M | A | Operations | Positive witnesses | s,e | Exact degree |
|---|---:|---:|---:|---:|---|---:|
| No controller chart |762|782|1,544|141|2,1|35,587|
| Flow |761|780|1,541|140|3,1|53,345|
| Population |761|780|1,541|140|3,2|53,347|
| Both |760|778|1,538|139|4,2|71,105|

The four arrays contain6,164 rows, each live together with every supplied port. All553 coefficient rows and all63 native rows remain literal. The new residual counts are16/15/15/14 and finalizer counts50/47/47/44. Fresh naive degree upper bounds are stored separately from this exact proof.

## 6. Evidence and replay

Fresh evidence comprises full source reconstruction, explicit interleaved-finalizer tracing, topology/liveness, all16 coefficient polynomials and2,704 entries, exact full-ring contracts(7), and the degree bounds and nonzero Y coefficients above. Thirty-two signed modular full-source substitutions over two primes additionally compare every retained residual, all63 native rows and(7). Half use illustrative fixed coefficients and half vary all supplied values. They are off-zero diagnostics, not accepting trajectories or native Pell tuples.

The helper pins the immediate grouped-power trio, entry-controller map receipt, balanced and bounded-high proofs, atomic chronology, positive-controller proof and IDLE-free proof. All nine hashes are saved in its source and receipt. The proofs are used only within their stated interfaces; arbitrary fixed-numeral assignments are not asserted to define universal programs.

```sh
carry_wip=/absolute/path/to/native-stream-queue
python3 "$carry_wip/matrix193_terminal_carry_chart.py" \
  --root "$carry_wip" --expect "$carry_wip/matrix193_terminal_carry_chart.json"
python3 -O "$carry_wip/matrix193_terminal_carry_chart.py" \
  --root "$carry_wip" --expect "$carry_wip/matrix193_terminal_carry_chart.json"
```

Generation uses mutually exclusive `--output`. Duplicate/nonfinite JSON is rejected, receipt equality is recursively type-exact, and explicit guards remain active under optimized Python. Fresh normal and optimized exact replays from `/` pass. No frozen predecessor or repository file is modified by the helper. No global minimality or new universal84 bound is claimed.
