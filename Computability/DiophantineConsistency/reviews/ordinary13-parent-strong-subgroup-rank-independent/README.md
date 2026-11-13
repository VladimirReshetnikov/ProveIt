# Independent review of the all-index subgroup and rank conditions

The all-index subgroup argument and the correlated-sign auxiliary criterion check out under the stated ordinary Pell classification and same-data parent assumptions. No concrete error was found in either odd-index growth branch, the sign bookkeeping, or the fixed-strong sufficiency direction. These are restrictions and a conditional fixed-witness criterion, not a proof that a two-norm zero exists, that a suitable auxiliary index exists, or that either equation has the desired iPRA endpoint.

The inherited cancellation gives `c/D0 | U_h` and `c/D0 | U_(r*m)`, with `D0=gcd(c,d*t)=gcd(m,d*t)≤m`; strong divisibility therefore makes `c/D0 | U_g`, where `g=gcd(h,r*m)`. A proper divisor would have `g≤floor(r*m/2)`. The previously reviewed doubling argument gives the strict contradiction for even m.

For odd `m=2v+1≥3`, set `k=floor(r*m/2)`. If `r*m` is even then r is even and `k≥r*v+1`, so one Pell step and the bound `x_v(A)≥vA` give `2X_k≥4vA>m*t`. If `r*m` is odd, `U_(2k+1)>a*U_(2k)=2a*X_k*U_k`, where a is the first coordinate of the positive fundamental unit; `a≥2` and `X_k≥x_v(A)≥vA` again make this greater than `m*t*U_k`. Here `4v≥2v+1` and `A>t` ensure strictness. In both branches `U_(r*m)>m*t*U_k`, so `c/D0>U_k` contradicts divisibility. Hence `r*m | h`, and the strong witness is in the stated m-subgroup; standard Pell divisibility then gives `c | y_(mz)` and the norm gives `f²≡1 mod c`.

For a valid fixed strong witness, ordinary Pell classification yields an odd auxiliary index `ell=2j+1` and a signed ordinate `V=epsilon*x_ell(I)/I`. The odd-quotient polynomial gives the same sign `sigma=epsilon*(-1)^j` in both reductions: `V≡sigma*y_ell(A) mod f²` and `V≡sigma*ell mod c`. The literal ordinate gives `V≡-c mod f²` and, because `f²≡1 mod c`, `V≡-R mod c`. Thus the two displayed congruences must use one correlated sigma. Conversely they make `V+c+f²R` divisible by both coprime moduli; the explicit positivity of that numerator is needed to produce a natural `T≥1`. With that positivity and a valid strong witness, the proposed quotient and Pell y satisfy the literal parent auxiliary factor. The congruences alone do not establish positivity or existence of an index.

The independent checker pins the packet and exact graphs, checks shared expressions and auxiliary/product rows, discovers small integer-coordinate Pell units, tests both parity branches of the odd-index growth proof, and checks subgroup and both-sign divisibility controls. Its exact odd-index toy is fact-level only. The checker is separate, but the even-index predecessor was collaboratively developed during an earlier review, and the proof relies on the explicitly stated standard integer Pell classification and strong-divisibility theorem. No Lean, build, staging, provider or model validation was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-strong-subgroup-rank-independent/check.py | cmp - reviews/ordinary13-parent-strong-subgroup-rank-independent/receipt.json
```
