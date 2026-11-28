# Unconditional finite-conductor check

Run these commands from the directory containing the script and table. Python 3.9 or newer and its standard library suffice.

```sh
python3 verify_small.py > replay.csv
cmp replay.csv small-certificate.csv
```

The program enumerates every primitive quadratic character of conductor below 512. The 5,304 data rows cover 312 signed fundamental discriminants, with 16 consecutive derivative differences and one positive bound that controls every subsequent index for each discriminant. A replay took about eight seconds. Exactly 31 signed discriminants have any decreasing step, and the largest conductor among them is 97. The program checks the direction changes for all 312 cases.

## Tail dominance

Let u be the logarithmic variable of the shifted completed theta kernel. Let q be the conductor, a the parity and f(u) the product of (u²-1), exp((a+1/2)u) and the Gaussian sum with coefficients chi_D(n)n^a. The derivative difference has the same sign as the integral of u^(2m) f(u) for u from zero to infinity.

Use A=1 for q≤56, A=2 for 57≤q≤432, and A=3 for 433≤q≤511. Then exp(2A)≥q/8. For u≥A, divide the theta series by its strictly positive first term. The magnitude of its remainder is at most

```
sum_{n>=2} n exp(-(n²-1)pi/8)
<= 2 exp(-3pi/8)/(1-1.5 exp(-5pi/8)) < 0.78.
```

Thus f is nonnegative beyond A. For the row marked tail_seed, the script integrates u^32 times min(f(u),0) below A and u^32 f(u) above A. All 312 resulting lower bounds are strictly positive. At any index j≥16, the negative part below A is multiplied by u^(2j-32)≤A^(2j-32) and the positive part above A by u^(2j-32)≥A^(2j-32). It follows that the true consecutive derivative difference is positive for every j≥16. The ordinary rows m=0 through 15 determine the complete classification. Each CSV endpoint has units of 10^(-12); both reported endpoints are rounded outwards.

## Interval summation

Use u in [0,6] and truncate the theta series at n=256. On each grid cell the positive and negative Gaussian subsums are decreasing separately. Their endpoint enclosures bound the signed theta sum, including when it changes sign. Multiply by outward enclosures for the exponential prefactor and the two power factors. For the seed below A apply the negative-part function to the resulting interval before multiplying by u^32. Sum the constant lower and upper bounds over cells. Eight cells per unit are tried first. Double the resolution until both endpoints of the integral enclosure have the same strict sign.

Most operations are integer arithmetic at scale 2^576. Python's Decimal.exp gives a correctly rounded exponential to nearest; the program steps one representable number outwards in each direction. Directed decimal operations bound the arguments of each exponential. The two rational bounds on pi are checked at startup using Machin's formula and the alternating arctangent series.

To evaluate the Gaussian terms at a grid point put B=exp(-pi exp(2u)/q), x(1)=B and r(1)=B³. Enclose x(n+1)=x(n)r(n) and r(n+1)=r(n)B². Then x(n)=B^(n²). Once the upper bound for x(n) reaches 2/2^576, the sum of the remaining terms through 256 in either the positive or negative subsum is at most 2 times the sum of their indices, divided by 2^576.

## Truncation errors

On [0,6], the omitted theta sum has absolute value at most 300 exp(-3·257²/511), by comparing successive terms n exp(-3n²/511) for n≥257. Multiplying by 6·6^32·37·exp(9) bounds the error in any of the 17 integrals for a single discriminant. The negative-part function is 1-Lipschitz, so the same error bound covers the tail seed. On u≥6, put X=pi exp(2u)/q≥950(1+2(u-6)). The absolute theta series is at most 2 exp(-X). The remaining factor u^32 (u²+1)exp(1.5u) is at most exp(19u), using log u≤u/2. Even the looser bound exp(88u) gives an integration error below 10^(-180). The checker reserves a total allowance of 10^(-18) before rounding its output.

The program checks squarefreeness directly. It enumerates the signed squarefree D congruent to 1 modulo 4 and the D=4d with squarefree d congruent to 2 or 3 modulo 4. The Kronecker algorithm then gives the value of the primitive character at every positive integer up to 256.
