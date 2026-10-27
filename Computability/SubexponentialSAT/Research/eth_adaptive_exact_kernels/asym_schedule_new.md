> Historical intermediate analysis: the closing five-packet intake supersedes some novelty and frontier claims below. These derivations remain valid supporting work, not the final headline. See report.tex, streamed_composition_new.md, late_cache_refinement.md, late_review_cauchy.md and fused_cauchy_new.md for the closing comparison.

> Closing-cutoff status: this note proves the unchanged packing/precision schedule and its **flat-enumeration ablation**. The final polynomial-space evaluator uses the late streamed-separator identity; see `streamed_composition_new.md` for the stronger coefficients **55.33162212048** (generic) and **25.16376541523** (degree ≤ s^.51), and the closing-cutoff comparisons. Do not present the older 63.758994 or29.353412 values as the final frontier.

# Adaptive alphabets with asymmetric packing: a coefficient below 64

## Provenance and exact scope

This is a new explicit schedule, not a claim of a new logarithmic exponent. It combines the independently supplied asymmetric pair-load balancing lemma (asymmetric packet-balancing report), exact crossing-family fraction, additive precision buffer, and joint/full-orientation slope-four Cauchy modes. The new contribution is an adaptive alphabet schedule: it uses the remaining asymmetric labeling budget at each depth instead of fixing an alphabet or changing it only once. The schedule was identified by the packing-review agent and is proved and exactly checked here.

For the normalized interface in those reports—at most `s` Boolean wires, degree at most `ceil(s^(9/10))`, polynomial description, `P0,ell <= C s`, immutable creation-precision representatives, and original entry cost `poly(s+L) 2^(O(s^.9))`—the resulting bound is

    (s+L)^{O(1)} 2^{(C_adapt+o(1)) s/sqrt(log_2 s)},
    C_adapt = 63.75899407488543... < 64,

with polynomial working space, conditional on precisely the unchanged upstream deformation/integrality/recovery/recursive-factorization identities. It does not certify the entire upstream SAT construction.

**Comparison caveat:** the joint-Cauchy proposal also supplies a genuinely faster exponential-space caching/matrix algorithm. Its composition with asymmetric packing can beat 64. Therefore this result is a polynomial-space frontier, not an unrestricted victory over all resource tradeoffs. A separate extra-space result is needed for that comparison.

## Schedule

Let lambda=ceil(log_2 s), b=ceil(6 log_2 lambda), H=ceil(s/lambda). For d=0,...,6 use these constants:

| d | r_d | A_d (cumulative leading packet budget) | x_d=A_d-A_(d-1) |
|---|---|---|---|
|0|13|27/2000|27/2000|
|1|14|21/800|51/4000|
|2|8|333/10000|141/20000|
|3|6|1933/50000|67/12500|
|4|5|861/20000|439/100000|
|5|4|1183/25000|427/100000|
|6|4|4999/100000|267/100000|

For d=7+j, j>=0, use r_d=3 and

    x_(7+j) = (1301/400000)(3/4)^j.

The total budget is sum x_d = 63/1000. Set u_d=floor(lambda*x_d) and a_d=sum_(j<=d)(u_j+b). Each call uses L_d=2^a_d, Q_d=r_d^a_d. Changing the alphabet at a child does not modify its parent descriptors or mode basis; it only relabels that child's explicit bipartite graph.

## Packing proof

The asymmetric lemma supplies P_d=(1+o(1)) M_d whenever

    Q_d R_d/M_d=o(1),
    Q_d^2 C_d (log s)^2/M_d=o(1),
    L_d Q_d^2/M_d=o(1).

At the root R_0=C_0<=ceil(s^.9), so the main condition is

    .9 + 2 A_0 log_2(r_0) < 1.

After the root, the retained side has R_d<=ceil(s^.9), while every fresh packet tensor on the other side has C_d<=2 L_(d-1). The dominant condition is now

    .9 + A_d log_2(r_d) < 1.

All these strict inequalities have exact integer certificates:

    13^27 < 2^100,
    14^21 < 2^80,
    8^333 < 2^1000,
    6^1933 < 2^5000,
    5^861 < 2^2000,
    4^1183 < 2^2500,
    4^4999 < 2^10000,
    3^63 < 2^100.

For every nonroot call the remaining exponents obey

    2 A_d log_2 r_d + A_(d-1) < .2+.063 = .263,
    (2 log_2 r_d+1) A_d < .263.

The corresponding root bounds are even smaller. New packet degrees have exponent at most .063+o(1)<.9, preserving the retained-side degree bound. Fixed slack in the displayed inequalities absorbs all factors polynomial in lambda, the ceiling in Delta, the additive O((log lambda)^2) packet budget, and s/M<=lambda.

## Noncircular depth bootstrap and uniformity

First prove these bounds for hypothetical active calls at every depth

    d <= N = ceil(log_(10/7) lambda)+10.

The finite prefix has fixed length. In the tail, u_d is at least lambda raised to

    eta+o(1), eta=1-ln(4/3)/ln(10/7)=.1934334683...>0.

Thus all u_d grow uniformly; floors cause relative o(1) error. At all these hypothetical active calls, the packing lemma gives uniform P/M=1+o(1). Since every alphabet is at least three, every child has at most `(2/3+o(1))M <= .7 M` for sufficiently large s. An active path cannot reach N: its mass would then be below s/lambda. This closes the induction without assuming the actual depth.

More precisely the balancing lemma with h=ceil(log_2 s) gives P/M=1+O(1/lambda)+s^(-epsilon+o(1)) for a fixed epsilon>0 across the finite prefix and infinite constant-alphabet tail. Over O(log lambda) levels this multiplies to 1+o(1). Therefore

    M_d <= (1+o(1)) s m_d,
    m_0=1, m_(d+1)=2m_d/r_d.

In particular m_7=1/5460 and m_(7+j)=(1/5460)(2/3)^j.

## Precision and mode entropy

No changes to the inherited exact taper or precision rule are needed. Inherited precision is O(s lambda^2 2^a_(d-1)). At retained valuation i<u_d,

    D_i=2^(a_d-i) >= 2^(a_(d-1)+b+1).

The ratio of inherited precision to M D_i/u_d is O(lambda^4 2^-b)=o(1); evaluation loss is also lower order. Exact linear taper therefore gives

    p_t <= (6+o(1)) M D_i/u_d

uniformly. The full-orientation slope-four basis has weights 1+4q-2s_2(q) and the same number of mode families. Exact unequal-symbol counting gives

    c_i <= (2(1-1/r_d)+o(1)) M/D_i.

The partition product with leading free energy pi^2/(24 theta) then yields

    log_2 N_i <= (kappa(r_d)+o(1)) M/sqrt(u_d),
    kappa(r)=pi sqrt(2(1-1/r))/ln 2.

Only the finite set r in {3,4,5,6,8,13,14} occurs, so all local o(1) errors are uniform. The entire orientation source form belongs to one source group and its targets to the opposite group. Thus varying r does not introduce a mode-factorization or child-size interface gap.

## Summing the work

The coefficient is the exact radical expression

    C_adapt = sum_(d=0)^6 kappa(r_d) m_d/sqrt(x_d)
       + kappa(3) / [5460 sqrt(1301/400000) (1-4/(3sqrt(3)))].

The seven prefix contributions are respectively

    53.0019041170, 8.4154747017, 1.5694138497,
    .4391319170, .1584745401, .0622333891, .0393506367.

The tail contributes .0730109236. The exact checker uses pi<355/113, ln2>693/1000 and rational one-sided square-root bounds and proves

    C_adapt < 9858084853553/154581966000
            =63.77254157547071... <64.

The pi and ln2 rational bounds themselves are checked from the alternating Machin arctangent formula and the positive atanh(1/3) series. No floating-point comparison is used in the certificate.

Polynomial interpolation/group/label overhead over O(log lambda) levels adds O(lambda log lambda) bits to the log runtime. Direct leaves cost exp(O(s/lambda)); original entry routines exp(O(s^.9)); packet routines exp(O(L log s)) with L<=s^(.063+o(1)). These are lower order. All arithmetic precisions, graph labels, interpolation degrees and immutable descriptions have polynomial bit length. Depth-first evaluation yields polynomial space.

## Comparison

The strongest evident fixed-r16 polynomial-space composition of asymmetric packing and joint slope-four modes, even allowing its excluded boundary as an infimum, has coefficient

    C_fixed16 = pi/ln2 (sqrt(150)+sqrt(50)/3)
              =66.19272369357722....

The new explicit interior coefficient is about 3.6767% smaller; unlike the old boundary it has fixed packing slack. This is a reduction in a leading upper-bound coefficient, not a measured runtime ratio. The original asymmetric report's certified 76.90899 value uses slope-three modes, so comparing only with that number understates the baseline.

## Evidence files

- `asym_schedule_checks/verify_schedule.py`: original arithmetic checker written for this iteration, no archived code imported.
- `asym_schedule_checks/schedule_checks.json`: recorded result.

All-size conclusions rely on the proof, not finite numerical tests. No SAT benchmarks or proof-assistant verification are claimed.

### Stronger two-stage comparison (important correction)

The round-two proposal already permits distinct root and tail alphabets. Composing that idea with asymmetric caps and joint slope-four modes produces a slightly stronger baseline candidate than fixed16. For root alphabet17 and tail13, let A0=.1/(2 log_2 17), A=.1/log_2 13 and c=2/13. Its boundary coefficient is

    kappa(17)/sqrt(A0)
      +(2/17)kappa(13)/[sqrt(A-A0)(1-c^(2/3))^(3/2)]
      =66.12047546003285....

The explicit <64 schedule beats this too (about3.57% smaller in evaluated coefficient). The numerical search found this best among its scanned integer two-stage parameters; this is not asserted as a proven global lower bound or a minimum over all possible compositions.

### Retuned cached two-stage comparison

For a stronger high-memory comparator than the directly inherited fixed-r16 schedule, use root alphabet7 and tail alphabet9. Let

    B0=pi sqrt(2)/ln2,
    a0=sqrt(12)/7, b0=sqrt(30)/7, j0=sqrt(24)/7,
    at=4/9, bt=sqrt((4+2(log_2(7)-2)^2)/9), jt=2/3,
    x0=89/5000, A=1577/50000, theta=279/1000.

For d>=1 set x_d=(A-x0)(1-theta)theta^(d-1). Then

    K0=B0/sqrt(x0),
    K1=B0*(2/7)/sqrt((A-x0)(1-theta)),
    q=(2/9)/sqrt(theta).

The full cached recurrence gives

    Tcoef=max{b0 K0, a0 K0+K1 max(bt,at/(1-q))}
         =37.89968459804997...,
    Scoef=max{j0 K0,jt K1}=33.623040921657754....

This is an explicit interior comparison with exactly the same root memory coefficient as the new adaptive cached schedule. It is not the stronger false claim that the root dominates its runtime: the recursive cache contribution dominates. Its packing guards are `7^89<2^250` and `9^1577<2^5000`; the tail satisfies `2/9<1/4<theta`, giving a noncircular depth bootstrap and uniformly growing taper. All other inherited assumptions are unchanged. The new adaptive cached time37.5917025555 is smaller at the same memory coefficient.

Allowing the excluded root and tail boundaries x0=.05/log_2(7), A=.1/log_2(9), and choosing theta=[(2/9)/(1-(4/9)/bt)]^2 gives numerical boundary time about37.89056 and space33.61326. This is a useful stronger comparison candidate, not a claim of global optimization over all possible schedules.
