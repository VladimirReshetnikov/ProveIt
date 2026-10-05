# Independent proof challenge: gamma83 radical order

**PASS, no author correction requested.** The exact radical quotient table and fixed-cofactor bound in `/tmp/gamma83_next_arithmetic.md` are valid under its explicitly stated native interface. The frozen author note has SHA256 `4298f6f64d4c9e1037901df3e0d50095ee126b9e31a82106db60643365d64f93`.

This is a proof-only review. I read the entire author note, the complete current83 proof, the power-test note and residual-order obstruction; inspected the saved83 JSON's witness list and literal arithmetic/input cuts; and read the specific native-filter passages furnishing `v3(H)=v3(Delta)=1`. No author, predecessor, supplied or frozen helper was executed or imported. The author's unsaved finite arithmetic checks were not reproduced, and their counts are not independent evidence from this reviewer.

## Radical order and the exact factor of nine

The author assumes a genuine canonical history with `6|a`, `H=4a+3`, `Delta=(a+1)(a+3)` and `d=5^s`, `s>=1`. Thus H is odd and divisible by3, Delta is odd, and d is prime to3. Orders of2 modulo H and rad(H) exist. The exact identity

`16Delta=(H+1)(H+9)`

gives `gcd(H,Delta)=gcd(H,9)`, since16 is invertible modulo H. In particular no prime greater than3 dividing H divides Delta.

For each `ell^f || H`, reduction and successive binomial lifting give

`ord_ell(2) | ord_(ell^f)(2) | ord_ell(2)*ell^(f-1)`.

Hence a lift can add only factors of ell. Taking least common multiples over all prime factors shows that every valuation contributing to `g=gcd(2Delta,O)` is unchanged by radicalization except possibly its3-part. This remains true if a prime order contributes a large factor belonging to a *different* prime: that factor was already in the order modulo ell and survives in the radical order. Odd-prime lifting cannot alter the2-part either.

Put `e=v3(H)` and let tau be the maximum3-adic valuation of `ord_ell(2)` over non3 prime divisors of H, with empty maximum0. The elementary identity `ord_(3^e)(2)=2*3^(e-1)` yields

`v3(O)=max(e-1,tau)`, while `v3(O_rad)=tau`.

The other clipping valuation is `v3(Delta)=v3(H+9)`: it equals1 for e1, is at least2 for e2, and equals2 for e>=3. Taking minima gives exactly the author's four table rows: ratio1 at e1; ratio3 at e2,tau0; ratio1 at e2,tau>=1; and `3^(2-min(2,tau))` for e>=3. Thus `g/g_rad` is1,3 or9.

Because that quotient is a3-power and `3` does not divide `2d`, passing from g to `m=g/gcd(g,2d)` preserves the quotient exactly. In particular `m/m_rad=g/g_rad`. The radical calculation does not require an algorithm factoring H, and its conclusion does not bound the size of m_rad. Repeated prime factors becoming irrelevant on the e1 subclass must not be confused with a uniform bound on all prime-order contributions.

## Fixed cofactor and parity assumptions

For `H=C*ell^f`, with ell>3 prime, f>=1, odd C divisible by3 and `gcd(C,ell)=1`, let T be any positive period of2 modulo C. CRT gives

`O | lcm(T,ell^(f-1)*(ell-1))`.

The ell-power term contributes nothing to gcd with Delta. For any other odd prime p, the shared ell−1 contribution is bounded by `v_p((C+1)(C+9))`, because `16Delta` has that residue modulo ell−1. Combining it with the T contribution uses the maximum of valuations, hence the lcm in

`D_C=oddpart(lcm(T,(C+1)(C+9)))`.

The odd part of g therefore divides D_C. Since Delta is odd and the factor3 of H forces O even, `v2(g)=1`; cancellation against2d removes that2 entirely. Prime-by-prime cancellation then proves `m | D_C/gcd(D_C,d)`. No assumption that T is the least period is needed.

The listed values are correct: C3,T2 gives D_C3; C9,T6 gives D_C45 and, because5|d, remaining bound9; C15,T4 gives D_C3. Thus the extended target `H=3*ell^f` implies `m|3` for every positive f. Native evenness is essential to these odd bounds. For example, outside the declared hypotheses, a3,H15,Delta24,d5 gives m2, so merely requiring `3|H` would not suffice. The author already states `6|a`; this is an assumption check, not a requested correction.

The arithmetic example a18,H75,Delta399 has order20, g2 and m1 at d5. Its order's factor5 cannot divide either `2^k*74` or `2^k*72`, so both old power tests fail for every k despite the small period. The example is correctly labelled nonnative.

## Source binding and conditional consequence

The saved JSON agrees with the author's named cuts: row16 defines a as `R12`; rows19–20 give H; rows24–25 give `a^2+4a+3=Delta`; rows33–46 give the ordinary-input index, the delta/rho multiples and the input norm. The eighteen witness names and independent sigma/gamma port match the current83 proof. I did not reconstruct the entire83 output polynomial in this review.

The current83 proof supplies the fixed-parent-history progression `x=x0 mod m` with positive slack `alpha0+2d(x0-x)`, followed by fresh positive delta and rho. On that inherited interface, m|3 permits the stated downward4-to1 transfer, and m|9 permits10-to1; the slacks increase by6d and18d respectively. This implication is conditional on an actual history with the proposed factorization. Neither the factorization criterion nor the small arithmetic illustration supplies such a history, a false-input zero, a new universal bound or a native occurrence theorem.

The read native-filter conclusions force a divisible by9 on the relevant constructed histories, hence H and Delta both have3-adic valuation1. Applying the new radical theorem to those conclusions is immediate. This review uses their accepted existence/interface results; it does not redo their complete history, mask or Pell-completion proofs. The general independent-gamma83 language remains unresolved.

## Authenticated dependencies and exact limits

The following repository files, relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`, were hash-authenticated directly as inert bytes:

| File | SHA256 | Review scope |
|---|---|---|
| `complete83_independent_gamma_scout.json` | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` | Witness list and selected literal cuts |
| `complete83_independent_gamma_scout.md` | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` | Full note |
| `complete83_gamma_power_tests.md` | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` | Full note |
| `complete83_gamma_native_finite_prime_avoidance.md` | `93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96` | Lines1–58 and156–170 |
| `complete83_gamma_native_repunit_filter.md` | `2e6dc2b984cee9c48aab2cbf8b585d7084438b7bd83b1ebf9c0e97b0aa5c42e6` | Lines102–119 |
| `gamma83_residual_order_obstruction.md` | `7d2d15ccb608f295a344000f23d147b8f7ce2975e5732f2f6e2adc05363b2754` | Full note |
| `complete75_gamma87_compiler_order_filters.md` | `43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3` | Hash only; no added proof coverage |

Only fresh read-only hashing/JSON inspection was performed. No finite arithmetic experiment, enormous native tuple, compiler invocation, helper replay, repository edit or Git mutation was made for this review. The proof challenge accepts precisely the stated arithmetic deductions and their conditional use of the inherited source interface.
