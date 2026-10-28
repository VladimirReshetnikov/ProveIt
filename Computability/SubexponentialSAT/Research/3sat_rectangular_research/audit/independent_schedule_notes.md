# Independent audit of the two final recursive schedules

## Verdict and scope

Both schedules satisfy the stated imported packing, depth, precision, entry-access, and lower-order-overhead requirements. No defect was found in these parameter choices. This audit does not independently verify the new local backend coefficients beta_r or the reported final time coefficients; those are separate proof obligations. It also does not establish an optimal schedule.

The source interface was checked against `sat_pairwise_certificates/sections/interface.tex`, `sat_adaptive_bounds/report/interface.tex`, and the integer-schedule discussion in `sat_affine_contraction/report.tex`. The imported sufficient gates, with side-degree bounds R and C, are

    QR/M -> 0,
    Q^2 C (log s)^2 / M -> 0,
    L Q^2 / M -> 0.

Here L=2^a, Q=r^a, the initial modulus precision and nilpotence order are at most s, and active calls have M>H=ceil(s/lambda), with lambda=ceil(log_2 s). Tensor descriptions keep their immutable creation precision.

The finite arithmetic checks are independently reproducible using:

    python3 code/verify_schedules.py --output code/schedule_gate_results.json

That checker uses exact rational arithmetic and exact integer-power inequalities for logarithm upper bounds. Decimal numbers in its JSON are illustrations; its fractions and integer inequalities are authoritative.

## Parameters

Both schedules use

    Lambda = lambda - ceil(sqrt(lambda)),
    b = ceil(6 log_2 lambda),
    u_d = floor(eta_d Lambda),
    a_d = sum_{j<=d} u_j + (d+1)b,
    q = 63/100.

For d>=4 the alphabet is four and eta_d=(1-q) R_tail q^(d-4).

| Schedule | Initial degree exponent | Prefix alphabets | Prefix eta values | Tail budget | Total budget |
|---|---:|---|---|---:|---:|
| Generic | 9/10 | 10,13,10,7 | 301/20000,287/25000,357/100000,193/50000 | 401/25000 | 1/20 |
| Low degree | 1/12 | 15,10,7,6 | 2149/20000,2337/100000,407/20000,109/10000 | 3793/100000 | 1/5 |

The cumulative prefix budgets are respectively

    generic:    0.01505, 0.02653, 0.03010, 0.03396;
    low degree: 0.10745, 0.13082, 0.15117, 0.16207.

The first tail eta values are 14837/2500000 and 140341/10000000.

## Degree propagation and exact prefix gates

Let A_d=sum_{j<=d} eta_j and set A_-1=0. Initially R,C are both bounded by s^delta up to harmless rounding. At positive depth, the newly created side has degree at most 2 L_{d-1}. A safe bound for the retained side is the maximum of the initial degree and all earlier packet degrees. Since a_d is increasing, the latter is bounded using a_{d-1}. Consequently the leading side-degree exponents are

    root:      R exponent = C exponent = delta;
    depth d>0: R exponent = max(delta,A_{d-1}), C exponent = A_{d-1}.

This conservative bound is sufficient even when the actual retained side does not yet contain the most recent packet tensors.

We verified the following strict logarithm bounds by checking r^denominator < 2^numerator as integers:

    log_2 6  < 517/200,
    log_2 7  < 14037/5000,
    log_2 10 < 1661/500,
    log_2 13 < 7401/2000,
    log_2 15 < 3907/1000.

The resulting rational upper bounds for the powers of s in the three gates are below. The omitted polylogarithms and additive guards do not affect a fixed positive exponent gap.

| Schedule/depth | QR/M numerator exponent | Q^2 C/M numerator exponent | LQ^2/M numerator exponent |
|---|---:|---:|---:|
| Generic 0 | 0.9499961 | 0.9999922 | 0.1150422 |
| Generic 1 | 0.998174265 | 0.21139853 | 0.22287853 |
| Generic 2 | 0.9999922 | 0.2265144 | 0.2300844 |
| Generic 3 | 0.995339304 | 0.220778608 | 0.224638608 |
| Low degree 0 | 0.503140483333... | 0.922947633333... | 0.9470643 |
| Low degree 1 | 0.54203404 | 0.97661808 | 0.99998808 |
| Low degree 2 | 0.555214658 | 0.979609316 | 0.999959316 |
| Low degree 3 | 0.57012095 | 0.9890719 | 0.9999719 |

Each must be compared with denominator scale M>s/lambda, so the relevant threshold is one. All are strictly below one. The smallest certified generic gap is 39/5000000; the smallest low-degree gap is 149/12500000. These small gaps imply very large possible thresholds, but they are valid fixed asymptotic margins.

## Boundary gates in the four-group tail

For the generic schedule, total A<=1/20 and all packet degrees remain far below the original s^(9/10) degree. The limiting QR numerator exponent is

    9/10 + 2(1/20) = 1.

Because only the packet part scales with Lambda, its binary logarithm is bounded by

    lambda - (1/10) ceil(sqrt(lambda)) + O((log lambda)^2).

Division by M>s/lambda adds only O(log lambda). This tends below the threshold by an unbounded amount. The other two generic tail numerator exponents are at most 1/4+o(1), giving a much larger margin.

For the low-degree schedule, A<=1/5 and both previous-packet degrees and the initial degree are controlled. The retained-side QR numerator exponent is at most 3/5+o(1). Both Q^2 C and LQ^2 have limiting numerator exponent at most

    5(1/5) = 1.

Their binary logarithms are bounded by

    lambda - ceil(sqrt(lambda)) + O((log lambda)^2).

Again the retreat dominates all guards, the (log s)^2 factor, division by M, and any fixed polylogarithmic padding slack. Thus all gates hold uniformly throughout the tail. Near-unit padding with relative slack lambda^(-3) is permissible.

## Noncircular depth bootstrap and floors

Consider hypothetical active depths through

    D(lambda) = ceil(log_{20/11} lambda) + O(1).

On this entire range, d=O(log lambda), so accumulated guards are O((log lambda)^2), as used above. The smallest tail taper is bounded below, up to fixed constants and the floor, by

    lambda^(1 + ln(63/100)/ln(20/11)).

The exponent is approximately 0.22715479468052147 and is strictly positive because 63/100>11/20. This sign conclusion is exact and does not rely on its decimal value. Therefore every active u_d tends to infinity uniformly, every floor error is relatively o(1), and u_d<=M eventually.

The packing conditions proved on this hypothetical range justify child ratio 1/2+o(1) in the tail, hence at most 11/20 eventually. An active path cannot reach beyond D(lambda), because then M<=s(11/20)^(d-O(1))<=s/lambda. This closes the induction; the depth estimate was not assumed in order to apply an unverified packing conclusion.

Accumulating relative padding errors O(lambda^(-3)) over O(log lambda) levels gives a multiplicative 1+o(1). The leading wire mass coefficients through the first tail call are

    generic:    1, 1/5, 2/65, 2/325, 4/2275;
    low degree: 1, 2/15, 2/75, 4/525, 4/1575.

Afterward they decrease by a factor 1/2 per level, up to the already controlled relative error. Hence the normalized M/sqrt(u) costs have geometric tail ratio

    (1/2)/sqrt(q) = 5/sqrt(63) < 1.

Uniform floor and padding errors can therefore be absorbed into one o(1) in the final leading coefficient. This audit checks the masses and convergence; the separate local beta certificate and paid-branch maximum are still needed for the numerical final coefficient.

## Inherited precision

The imported source bound is p=O(s lambda^2 2^(a_{d-1})), with a_-1=0 at the root. At an active valuation i<u_d,

    D=2^(a_d-i) >= 2^(a_{d-1}+b+1).

Since M>s/lambda and u_d<=lambda,

    p / (MD/u_d) = O(lambda^4 2^(-b)) = O(lambda^(-2)) = o(1).

The exact Hermite slope rho equals (1+o(1))M/u_d uniformly: u_d tends to infinity and M/u_d tends to infinity, so both its analytic correction and integer ceiling are negligible. The recovery allowance rho u_d(a_d+1) is also lower order, because its ratio to MD/u_d is O(lambda^2/D), and D>=2^(b+1)>=2 lambda^6. Consequently the common sharp precision bound

    p_t <= (6+o(1)) MD/u_d

continues to hold uniformly over the recursion.

The mode generating-function asymptotic is uniform as well: its optimal tilt is of scale sqrt(u)/D, which tends to zero uniformly because D>=2 lambda^6. Its logarithmic remainder is negligible compared with M/sqrt(u).

## Description, entry, arithmetic, and leaf overheads

All packet exponents satisfy a_d<=A_total lambda+O((log lambda)^2). Thus L<=s^(1/20+o(1)) in the generic case and L<=s^(1/5+o(1)) in the low-degree case. In both cases:

* packet, mode, precision, and interpolation descriptions have polynomial size in s;
* all working precisions remain polynomial in s;
* the source extension field with degree 4 ceil(log_2 s) supplies enough residue-distinct interpolation points, since M(2L-1)+1<s^4 eventually;
* old tensor entries are evaluated at their creation precision and canonically lifted, so nested packet-entry work is not silently composed;
* fresh packet-entry work exp(O(L log s)) is exp(s^(A_total+o(1))), which is lower order than exp(s/sqrt(log s));
* original entry work 2^(O(s^(9/10))) remains lower order, including in the low-degree schedule, which changes the degree premise only;
* direct leaf work 2^(O(s/lambda)) is lower order;
* products of factors polynomial in s over O(log lambda) recursion levels add O(lambda log lambda) to the exponent, again lower order.

The dependence on the original description length remains one fixed polynomial factor. To state this correctly, paid recursive branching counts are bounded independently of that length, while description-dependent local work is charged once per generated call; one should not unnecessarily multiply a polynomial in the original description length at every recursion depth.

The schedules use a fixed finite set of constant alphabets, so exact weight-allocation enumeration remains polynomial in s, even though its fixed polynomial degree may be large. All finite exceptional sizes, including parameters with nonpositive Lambda or zero taper, can be handled by direct contraction. No practical threshold or measured runtime is implied by these eventual bounds.
