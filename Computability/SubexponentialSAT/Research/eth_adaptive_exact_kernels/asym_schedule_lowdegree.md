> Historical intermediate analysis: the closing five-packet intake supersedes some novelty and frontier claims below. These derivations remain valid supporting work, not the final headline. See report.tex, streamed_composition_new.md, late_cache_refinement.md, late_review_cauchy.md and fused_cauchy_new.md for the closing comparison.

> Closing-cutoff status: this note proves the unchanged packing/precision schedule and its **flat-enumeration ablation**. The final polynomial-space evaluator uses the late streamed-separator identity; see `streamed_composition_new.md` for the stronger coefficients **55.33162212048** (generic) and **25.16376541523** (degree ≤ s^.51), and the closing-cutoff comparisons. Do not present the older 63.758994 or29.353412 values as the final frontier.

# Degree-sensitive adaptive schedule: coefficient below 30

## Theorem and boundary

Replace the root degree assumption `Delta<=ceil(s^(9/10))` in the normalized contraction interface by `Delta<=ceil(s^(51/100))`. Keep all other algebraic identities, immutable tensor semantics, precision/oracle conditions and bit-cost model. In particular original entry routines may still cost `poly(s+L) 2^(O(s^.9))`: this is lower order and need not be reduced together with graph degree.

There is then a polynomial-space contraction algorithm with

    T <= (s+L)^{O(1)} 2^{(C_51+o(1)) s/sqrt(log_2 s)},
    C_51 = 29.353412008627856... <30.

The source high-moment proposal's alternative SAT grouping yields initial degree `n^(1/2) polylog(n)`, with wire budget `s=O(n log log n)` and unchanged local coefficient procedures. Where that imported construction is applicable, its actual normalized degree is eventually at most `s^.51`. Thus the present theorem preserves and improves that useful degree-sensitive normalized contraction case. It does not convert the displayed wire coefficient directly into a variable coefficient: the encoding's wire multiplier still matters. It does not prove new density compression or remove the log-log factor.

## Explicit schedule

Use the same lambda, buffer b, leaf threshold H, and definitions u_d=floor(lambda*x_d), a_d=sum_(j<=d)(u_j+b) as in `asym_schedule_new.md`. For d=0,...,6 use

|d|r_d|A_d=sum_(j<=d)x_j|x_d|
|---|---|---|---|
|0|15|627/10000|627/10000|
|1|15|2269/20000|203/4000|
|2|8|357/2500|587/20000|
|3|6|81/500|12/625|
|4|5|1771/10000|151/10000|
|5|4|1911/10000|7/500|
|6|4|1999/10000|11/1250|

At d=7+j use r=3 and

    x_(7+j)=(391/40000)(3/4)^j.

The cumulative budget tends to A_infty=239/1000. The mass product at depth7 is m_7=1/6750.

## Why this is not a naive rescaling

The generic high-degree schedule is controlled mainly by row labeling. Here packet rounding, `LQ^2=o(M)`, becomes binding, so the budgets have been independently changed. For gamma=.51 the required exponent conditions are

- Root degree: `gamma+2 A_0 log_2(r_0)<1`.
- Nonroot retained side: `gamma+A_d log_2(r_d)<1`.
- Uniform padding-rounding: `(1+2 log_2(r_d))A_d<1`.
- Fresh side: `2 A_d log_2(r_d)+A_(d-1)<1`.

The fresh-side condition follows from rounding because A_(d-1)<=A_d. All new packet degrees are `s^(.239+o(1))<s^.51`, so the retained-side invariant is preserved.

The exact checker proves each logarithmic guard by integer exponentiation. Important examples are

    15^627 < 2^2450      [root degree],
    15^4538 < 2^17731    [depth1 rounding],
    8^714 < 2^2143,
    6^162 < 2^419,
    5^3542 < 2^8229,
    4^3998 < 2^8001,
    3^478 < 2^761        [tail rounding].

The full degree and rounding guard table is in `degree_51_schedule_checks.json`. The smallest fixed rounding gap among this finite set occurs at depth1 and is about .0000765238564. The root degree gap is about .0000759193107. The tail rounding exponent is .996612075345. These fixed gaps absorb every logarithmic factor, the additive buffers, floors, and s/M<=lambda.

## Remaining proof and coefficient

The same noncircular .7-shrink bootstrap, positive-power uniform growth of u_d, inherited precision argument, slope-four entropy, and depth-first polynomial-space evaluation from `asym_schedule_new.md` apply verbatim. The alphabet is always at least3 and the tail taper ratio is still3/4. Labels and precisions remain polynomial-size; deformation degree is now at most `s^(1.239+o(1))<s^4`. Packet entry cost is at most `exp(s^(.239+o(1)))`, still lower order than `exp(s/sqrt(log s))` and within the original `.9` oracle allowance.

With kappa(r)=pi sqrt(2(1-1/r))/ln2 and m_(d+1)=2m_d/r_d,

    C_51=sum_(d=0)^6 kappa(r_d)m_d/sqrt(x_d)
       + kappa(3)/[6750 sqrt(391/40000)(1-4/(3sqrt(3)))].

The finite terms are

    24.729994932969, 3.665038246735, .622181160186,
    .187678988438, .069118158132, .027801116768, .017532947321.

The tail is .034066458080. Rational one-sided square-root bounds together with checked Machin/atanh rational estimates for pi and ln2 prove

    C_51 < 309386069468981/10537797414375
         =29.359652430491405... <30.

## Comparison discipline

The high-moment report's degree-one-half normalized coefficient is 42.3727... using slope-three factorial modes. Composing only its mode enumeration with the joint slope-four basis multiplies that value by sqrt(3)/2, giving about36.695.... The new coefficient29.3534 is smaller. A more favorable explicit two-stage composition of all relevant packing and slope-four ideas has root alphabet19 and tail14. Under gamma=.51, let

    A0=.49/(2 log_2 19),
    A=1/(1+2 log_2 14), c=2/14.

Its boundary coefficient is

    kappa(19)/sqrt(A0)
       +(2/19)kappa(14)/[sqrt(A-A0)(1-c^(2/3))^(3/2)]
       =30.32044969233703....

Even allowing the stronger excluded gamma=.5 boundary gives30.103788712027054.... The present explicit interior coefficient is smaller. These are comparison candidates and numerical evaluations, not proven universal lower bounds or global optima over all schedules.

For truly much smaller-degree inputs, the earlier asymmetric packet's degree<=s^(1/12) specialization has coefficient31.0641 with slope-three modes, hence about26.902 with slope-four modes. That narrower case remains part of the portfolio; the new gamma=.51 theorem does not replace it. Resource-qualified caching/matrix variants should likewise be listed separately.

## Optional gamma=.6 specialization

For degree<=ceil(s^(3/5)), multiply the finite-prefix budgets of `asym_schedule_new.md` by4, retain the same alphabets, and use total tail budget239/1000 (not252/1000). Thus the remaining tail budget is122/3125, with ratio3/4 and m_7=1/5460. The identical degree/rounding/fresh-side checks give

    C_.6=31.885139053014726... <32,
    C_.6 <21747499139912713/681912579348000
         =31.891916645248344....

This optional weaker-degree-premise certificate is independently recorded in `lowdegree_schedule_checks.json`.

## Evidence and limits

- `asym_schedule_checks/verify_degree_51_schedule.py`
- `asym_schedule_checks/degree_51_schedule_checks.json`
- `asym_schedule_checks/verify_lowdegree_schedule.py` (optional gamma=.6)
- `asym_schedule_checks/lowdegree_schedule_checks.json`

All are original arithmetic checks; no archived code was executed or imported. They certify schedule arithmetic, not end-to-end SAT behavior. The all-size theorem follows from the analytic argument and unchanged upstream algebraic interfaces, not finite test success.
