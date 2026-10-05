# Critical growing-power theta diagnostics

Status: independent numerical diagnostics, 2 October 2026. These are **not exact integer coefficient counts**, a proof of the asymptotic theorem, or interval-certified coefficient enclosures. The large integer indices make ordinary coefficient DP impractical. No delivered fixed-power source files were modified.

## What is computed

For `F_a(q)=product_{k>=1}(1+k^a q^k)`, let `p_k=logistic(a log k-tk)`, with the exact *discrete* saddle equation `sum k p_k=n`. The diagnostic is

`M = sqrt(2*pi*V) P(S=n)`,

so the coefficient is `exp(L+n*t)/sqrt(2*pi*V) * M`. A single Gaussian predicts `M=1`; the candidate predicts `M=Theta(mu,Q)+o(1)`.

`S=sum_{k>=1}kX_k` includes part 1. `R=sum_{k>=2}X_k` excludes part 1. All displayed theta values use the *finite, discrete* moments and the exact phase modulo one unless explicitly marked as limiting values. A cautionary column recomputes the incorrect theta after including part 1 in R.

## Exact integer selection and rounding

For each integer `a` and target `lambda` (4 or 5), first solve on the large branch

`a(log K0-1)/K0^(1/3)=lambda`.

At this reference saddle let `mu0=E R`. For target phase `phi=0` or `1/2`, choose the integer

`r = floor(mu0 - phi + 1/2)`.

Vary real K locally until `E R=r+phi`; let its real saddle mean be `n_real`. Then set

`n = floor(n_real+1/2)`

and solve the discrete saddle equation again at this **integer n**. Ties are rounded upward. The program never obtains n by rounding an already combined floating-point `K^2/2`: it keeps the deterministic integer contribution separately. JSON/TSV record n as an integer, K, actual lambda, the real-to-integer n adjustment, and the final phase error. The two phase sequences need not be ordered within a given a because each chooses the closest target to mu0 independently.

## Stable Bernoulli arithmetic

Set `m=floor K`. The frozen baselines are the exact integers

`R0=m-1`, `S0=m(m+1)/2-1`.

For `2<=k<=m`, write `X_k=1-Y_k` with rare-hole probability `q_k=1/(1+exp(|a log k-tk|))`. For `k>m`, write `X_k=Y_k` with the same stable expression for the rare-addition probability. The signs are h=-1 and +1 respectively. Means are accumulated as corrections to R0 and S0; part 1 is retained separately in S. Variances use `v=q(1-q)`, never subtraction from a rounded p near 1.

The cancellation-safe conditional variance is

`Q=(U*T2-T1^2+U*v1)/V`,

where `T_r=sum_{k>=2}(k-K)^r v_k`, `U=T0`, and `v1=p1(1-p1)`. `C=K U+T1` and `V=K^2 U+2K T1+T2+v1`.

The middle interval with `a log k-tk >=85` is omitted from rare-variable arrays and retained in the exact integer baseline. Concavity verifies its endpoint lower bound. Above the last retained k, the derivative bound `f'(x)<=-1/W` gives a geometric upper-tail bound. The total discarded-variable probability eta is recorded; coupling gives an absolute normalized-multiplier bound `sqrt(2*pi*V)*eta` (with an immaterial variance correction far below the reported precision).

## Fourier method and checks

The centered characteristic function is integrated around `theta_j=2*pi*j*C/V`. For k>=2, use `alpha=theta*k-2*pi*j`, then evaluate exactly the rare-variable factor

`log(1+q*(exp(i*h*alpha)-1))-i*h*q*alpha`.

The separate phase is `exp(-2*pi*i*j*mu)`; part 1 uses its actual phase theta. This factors nearly deterministic variables exactly, rather than taking an invalid logarithm of an uncontrolled large-phase approximation.

Main runs use 64-bit-mantissa `numpy.longdouble`/`clongdouble`, with 160-point Gauss-Legendre quadrature in `y=sqrt(V)*(theta-theta_j)` on `[-11,11]`. Local logarithms are accelerated by a degree-20 or degree-30 discrete cumulant expansion. Coefficients of Bernoulli cumulant polynomials are first generated as exact rational numbers. Several Taylor degrees are compared, and the full rare-variable characteristic product is independently evaluated at y=-8,-4,0,4,8 for every included satellite. The main Gauss nodes are binary64, so agreement is interpreted conservatively at about 12 displayed significant digits, not at every printed decimal.

Satellites `|j|<=8` are retained for lambda=4, and `|j|<=10` for lambda=5. The omitted arcs are checked using a pointwise upper envelope, **not merely the limiting theta tail**. Partition the upper edge into consecutive blocks, assigning the minimum actual Bernoulli variance on each block. If these lower weights are w_k, then

`|phi(theta)| <= exp(-2 sum w_k sin^2(k theta/2))`.

Each block sum is evaluated in closed form. For the tail away from all selected cells, remove the fast center phase and use

`|phi(theta)| <= exp(-U_lower + |sum w_k exp(i k theta)|)`.

For `theta>=10/W`, the unimodality/total-variation bound yields

`|phi(theta)| <= exp(-U_lower + max(w_k)/sin(theta/2))`.

These give small omitted-arc estimates without assuming a Gaussian at uncomputed satellites. The pointwise algebraic inequalities are rigorous; integration of their envelopes uses ordinary adaptive quadrature, **not interval arithmetic**. QUADPACK's reported error is only an integration diagnostic, not a rigorous total numerical error bound. Thus these results should be called high-precision Fourier diagnostics, not certified exact coefficients.

## Independent binary128 audits

`quad113.cpp` independently evaluates the full characteristic product at every quadrature node, without the cumulant/Taylor acceleration, in IEEE binary128 (113-bit mantissa). Its saddle and moments are independently refined in the same precision. Node and weight files were generated at 60 decimal digits.

- a=8, lambda=4, target phase 0, n=3320242: retained-arc multiplier `1.74280290387719369214029136342533`; 96 and 128 nodes agree through 33 digits. The accelerated value differs by about 6.2e-15. Its omitted-arc envelope integral is about 3.4e-14
- a=12, lambda=5, target phase 1/2, n=21224105: retained-arc multiplier `0.04227299907995258888309993863213`; 96 and 128 nodes agree through 31 digits. The accelerated value differs by about 1.6e-16. Its omitted-arc envelope integral is about 3.2e-15

The many matching digits concern the **retained arcs**, not the full coefficient; omitted arcs and the non-certified nature of their integration remain separate caveats.

## Conclusions supported by the diagnostics

- At lambda=4 the limiting multipliers are 1.7597972114580294 (phase 0) and 0.3092881363932599 (phase 1/2)
- At lambda=5 they are 2.4590979732532166 and 0.0425749720576058
- Increasing integer powers approach these very different non-unit limits; the single Gaussian fails visibly in both phases
- The finite-moment theta approximation also converges. At small powers, particularly a=8 or a=12, rare omissions of low parts have not yet become negligible in R and cause a noticeable preasymptotic mismatch. No effective onset is inferred from the theorem
- Including part 1 in R is numerically disastrous: at a=32 it predicts theta approximately 0.9948/1.0052 for lambda=4, or 0.9914/1.0086 for lambda=5, rather than the observed strong modulation

Full integer indices, actual phases and parameters, every satellite contribution, comparison errors, and omitted-arc diagnostics are in `diagnostics_complete.json`; the concise table is `diagnostics_table.tsv`.

## Reproduction

Packages in this environment: Python 3, NumPy 2.3.5, SciPy 1.17.0, mpmath 1.3.0. Run from this directory:

```
OPENBLAS_NUM_THREADS=1 python diagnostics.py --powers 12 20 32 48 --lambdas 4 5 --output results.json
OPENBLAS_NUM_THREADS=1 python diagnostics.py --powers 8 --lambdas 4 --output initial.json
# Run envelope checks only after the relevant result file has finished writing.
python error_diagnostics.py results.json
python error_diagnostics.py initial.json

python prepare_quad113.py
g++ -std=c++17 -O3 quad113.cpp -lquadmath -o quad113
./quad113 a8_l4_phase0.txt nodes96.txt
./quad113 a8_l4_phase0.txt nodes128.txt
./quad113 a12_l5_phasehalf.txt nodes96.txt
./quad113 a12_l5_phasehalf.txt nodes128.txt
```

`assemble_summary.py` merges the checked snapshots from the actual concurrent run. The baseline run used order 30; additional lambda=5 runs used order 20. Both have exact-product point checks and Taylor-order comparisons recorded. Source inspection of the existing delivered fixed-a package found an exact coefficient DP only through n=3000; it was read, not modified or reused as an exact count at these vastly larger indices.

Additional sensitivity checks changed the probability cutoff from 85 to 75/95, the local window from 11 to 12, the node count from 160 to 200, and the Taylor degree to 24. Changes were below 1.7e-14 (a=8, lambda=4) and 4.0e-16 (a=12, lambda=5). Adding two more satellites changed these recalculations by less than 5e-18. These checks are saved in `sensitivity_a8.json`, `sensitivity_a12.json`, and `satellite_sensitivity.json`.

Across the final 18 rows, the largest exact-product point discrepancy is below 4.9e-20; the largest discarded-variable normalized coupling bound is below 6.4e-22. Every recorded phase error satisfies `K*abs(mu-target)<0.470`, consistent with the half-unit n-rounding bound. All 18 cases have completed; no coefficient run is still pending.
