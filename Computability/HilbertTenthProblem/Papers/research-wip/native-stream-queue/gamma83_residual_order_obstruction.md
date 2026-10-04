# What the extracted gamma83 filters cannot bound

Two bounded deductions sharpen the remaining question for [independent-gamma83](complete83_independent_gamma_scout.md). First, every fixed positive child-zero fiber has the same ordinary-input progression modulus in either Pell-index parity branch. The even branch does not create an additional progression on that fixed fiber. Second, explicit free arithmetic hosts obey the extracted discriminant relation, exact two-adic valuation, and strengthened plus/minus prime filters while having unbounded alias modulus and failing both existing power tests for every number of squarings.

The second result is an obstruction to deriving a bound from those extracted conditions alone. **Its hosts are not native half-binomial parameters, compiler histories, positive input components, or zeros of the 83-operation polynomial.** Neither result proves soundness or supplies a rejected-input zero. No source schedule or operation count changes.

## 1. The same spacing in both input branches

Use the actual source's notation

```
A=a+2, Delta=A^2-1=(a+1)(a+3), H=4a+3,
O=ord_H(2), g=gcd(2Delta,O), m=g/gcd(g,2d).
```

Fix any full positive child zero at ordinary input `x0`, not necessarily a genuine parent history. Retain its outer/main/auxiliary coordinates and independent gamma. For a new positive input `x`, change only the outer slack to

```
alpha_x=alpha_0+2d(x0-x)>0,
```

before refreshing the two positive input coordinates `delta,rho`. The literal source preserves `C`, `W`, and all six noninput factors under this change. Its exact input-fiber theorem applies with `u_x=2dx+b` and the same discrete logarithm `j` of `W` modulo `H`.

Native parity gives odd Delta, even A, `3|H`, and hence even O. Write `g=2s`; then `s` is odd, `s|Delta`, and `gcd(A,s)=1`. The parity of `j` is fixed by `W mod 3`, so varying x on this fiber cannot switch between the two branches.

For the odd branch, subtracting the original compatibility from the new one gives

```
g | 2d(x-x0).
```

For the even branch it gives `g | 2Ad(x-x0)`, which is equivalent to the same condition: divide by 2 and cancel A modulo s. The exact positive CRT completion in the inherited theorem supplies `delta,rho` in either case. Thus, for every such child-zero fiber, precisely the inputs

```
x>0, alpha_x>0, x=x0 mod m
```

have positive completions. This extends the parent-history progression statement to all full child-zero fibers covered by the actual native pretyping theorem, including either permitted residue of a signed W. It does not assert that an arbitrary freely supplied outer tuple satisfies that pretyping theorem.

The remaining fiber width is still finite. Changing the compatible input Pell index only enlarges `delta,rho`; it does not change m or the admissible input progression. A different outer fiber is a separate question.

## 2. Extracted conditions to be tested

Fix powers of five `d,E,t`, with `d>=5`; they may in particular obey the canonical relations among cell width, spatial padding, and bit length. Fix an integer `u>=1` and put

```
n=3^u E,
Mminus=2^n-1, Mplus=2^n+1,
S=Mminus*Mplus=2^(2n)-1.
```

Consider positive free integers a obeying the following conditions:

```
v2(a)=3t,
a=0 mod Mplus,
4a=1 mod Mminus.                                      (1)
```

These conditions imply `6|a`, `a>2^t`, `H=3 mod 4*2^(3t)`, and

```
v3(a)>=u+1, v3(Delta)=v3(H)=1,
gcd(Delta,S)=3,
gcd(Delta,S/3^(u+1))=1.                              (2)
```

Indeed `v3(Mplus)=u+1`, while `Mminus` is prime to 3. Modulo Mminus, the identity `16Delta=(H+1)(H+9)=(4a+4)(4a+12)` gives `16Delta=65`. Neither 5 nor 13 divides Mminus, since their orders 4 and 12 cannot divide the odd integer n. Hence Delta is coprime to Mminus. Modulo Mplus, Delta is 3. These observations prove (2), including the full prime-power quotient.

For `u=1`, (2) is the extracted conclusion of the pinned parity-normalized genuine-history filter. Condition (1) imposes an even stronger minus-factor congruence than that theorem's separate prime-field residues. The statement for arbitrary fixed u is an arithmetic assertion in this note; it does not claim a new genuine-history realization theorem for higher u.

Also, exactly

```
gcd(H,Delta)=gcd(H,9).
```

There is no factor 5 in this identity. The factor 5 in the existing `H-1` power test comes from a different Euclidean identity. On the hosts below the displayed gcd equals 3.

## 3. An unbounded residual order family

For each `k>=1`, choose any prime divisor r of the positive integer

```
T=2^(17^(k-1)),
Z_k=1+T+T^2+...+T^16.
```

Then

```
ord_r(2)=17^k.                                        (3)
```

Here is an elementary proof, requiring no prime-distribution or primitive-divisor theorem. Modulo 17, `T=2` and `Z_k=1`, so r is not 17. As `(T-1)Z_k=2^(17^k)-1`, the order divides `17^k`. If it divided `17^(k-1)`, then `T=1 mod r` and `Z_k=17 mod r`, forcing r=17, a contradiction. This proves (3). In particular r is odd.

The five moduli

```
Mplus, Mminus, 17^k, r, 2^(3t+1)
```

are pairwise coprime. The neighboring odd M factors are coprime. Since `ord_17(2)=8` and `2n` has only one factor 2, 17 does not divide S. If r divided S, (3) would give `17^k|2*3^u E`, impossible for E a power of five. The other coprimalities are immediate from (3) and oddness.

CRT therefore gives an infinite positive arithmetic progression of a satisfying

```
a=0                    mod Mplus,
a=4^(-1)               mod Mminus,
a=-1                   mod 17^k,
a=-3*4^(-1)            mod r,
a=2^(3t)               mod 2^(3t+1).                  (4)
```

Every such a satisfies (1)–(2). It also has `17^k|Delta` and `r|H`. Reduction of powers modulo r shows that its full order `ord_H(2)` is divisible by `17^k`. Consequently

```
17^k | g,
17^k | m,                                             (5)
```

because d is a power of five. Thus m is unbounded as k varies while d, E, t, and u remain fixed in this arithmetic relaxation.

These hosts also defeat both existing sufficient tests for all squaring exponents. Equation (4) gives

```
H-1=-2 mod 17^k, H-3=-4 mod 17^k.
```

Neither is divisible by 17. For every `e>=0`, the order in (3) therefore fails to divide `2^e(H-1)` or `2^e(H-3)`. Hence

```
2^[2^e(H-1)] != 1 mod H,
2^[2^e(H-3)] != 1 mod H.                              (6)
```

This is an all-e argument, not an inference from a finite sequence of failed squarings.

## 4. What is missing from these hosts

The CRT chooses a freely. It does not enforce

```
X=2^R,
2Y=sum_(j=0)^((R-1)/2) binom(R-1,(R-1)/2+j)*X^j,
a=Y(X+1),
```

or a packed R with the actual population, mask, computation, and temporal conditions. In particular the unbounded family at fixed t does not retain the native finite range for R or the consequent upper bound on the true half-binomial a. No source witnesses, program numerals, accepting input, or false input are asserted for the numerical hosts.

The conclusion is correspondingly limited but exact: (1)–(2), the rational H/Delta relation, the elementary native parity/two-adic conditions, and positivity alone cannot yield a uniform bound on m or force either power test. The genuine native formula and additional history restrictions remain necessary to any proposed implication of that kind. This does not contradict the genuine-history filter, which only supplies the extracted conditions on selected histories.

The earlier compiler-order packets already warn that their individual prime-power and finite-prime restrictions do not bound the full residual modulus. The new content here is an explicit unbounded family preserving the displayed stronger residue data, with a proof of failure of both power tests for every e. It is not a claim to have solved the native occurrence problem.

## 5. Fresh bounded evidence and authenticated scope

The companion [fresh helper](gamma83_residual_order_obstruction.py) reads the actual83 JSON and proof dependencies as inert bytes. It checks the current 83-row count and that rho and delta enter only the input factor. It does not run or import any predecessor helper.

The [receipt](gamma83_residual_order_obstruction.json) gives six exact CRT hosts with `d=E=5,t=125`, `u=1,2,3`, and `k=1,3`. The prime/order witnesses are

```
r=131071,     ord_r(2)=17,
r=127855913,  ord_r(2)=4913=17^3.
```

Primality is checked by trial division; modular powers verify the exact prime-power orders. The helper materializes a, H, Delta and all CRT moduli, then checks (1)–(2), the certified divisor of m, and the coprimalities underlying (6). Sixteen finite power-test residues per host are supplementary. It does not factor H, compute its full order or exact m, construct a Pell input tuple, or evaluate a full83 zero. The diagnostic five-power numbers are not claimed to be actual compiled program constants.

Read scope: full current83 proof, its literal saved input/outer consumers and factor dependencies; full historical exact period, compiler-order and local-filter notes; full current power-test note; the already independently reviewed small-prime and parity-padding notes. No predecessor execution, new compiler invocation, or repository edit was performed. The following inert files are authenticated by the fresh helper:

| File | SHA-256 |
| --- | --- |
| `complete83_independent_gamma_scout.json` | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` |
| `complete83_independent_gamma_scout.md` | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` |
| `complete75_independent_gamma87_period.md` | `dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784` |
| `complete75_gamma87_compiler_order_filters.md` | `43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3` |
| `complete75_independent_gamma87_local_filters.md` | `6dc2b46d7cdc4bf33566b24e5c0252d34858128096dbdb6614881b3a33fb6171` |
| `complete83_gamma_power_tests.md` | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` |
| `complete83_gamma_small_prime_digit_rules.md` | `b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e` |
| `gamma_parity_padding_scout.md` | `0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c` |

Run the bounded helper from any directory with `--root ABS_WIP --expect ABS_JSON`; `--output FILE` emits its deterministic receipt. Checks use explicit exceptions in normal and optimized Python. No maintained public API or adversarial JSON-parser guarantee is claimed.
