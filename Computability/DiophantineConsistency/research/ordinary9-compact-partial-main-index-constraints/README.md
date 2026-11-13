# Main-index restrictions for a fixed compact partial family

For the specific first-norm family in the [pinned partial construction](../ordinary9-shifted-two-norm-compact-first-compatible-partial/README.md), any solution of the remaining main norm has a unique possible main Pell index m and eta. Its index must obey `n<m<2n`, and two verified compact-specific prime divisors yield one of two explicit congruence classes below. Neither condition decides whether such an m exists. In particular, this is not a full zero, a parent-equation equivalence, or an iPRA theorem.

Retain the partial family's exact fixed tuple and definitions: `q=2^(67*8807)`, `J=F=s=1`, `alpha=2`, `w=(q−2)/2−Kprime>0`, `X=q*w`, `Y=q³`, `M=X*Y²`, and `n=(R+1)/2≥1`. Its first Pell ordinate k is positive and even, with `k=2n+4M*sigma`; its allowed eta is `0≤eta<k`. Set `a=Y*(X+1)`, `A=a+2`, `H=4a+3`, `Delta=A²−1=a²+H`, and `c=Y*k+eta`. The literal main signed root is `U*d` with

```text
d = X + a*c + H*(gamma − 4*q²*w*sigma).
```

If the main residual vanishes, `d²−Delta*c²=1`. Standard-integer Pell classification gives a unique `m≥1` and positive x-coordinate g such that `g+c*sqrt(Delta)=(A+sqrt(Delta))^m` and `d=+g` or `d=−g`. This classification is a mathematical input, not a newly elaborated Lean result.

## Index interval and uniqueness

For integer `T≥2` and the Pell ordinate y_j of `(T+sqrt(T²−1))^j`, the recurrence gives

```text
(2*T−1)^(j−1) ≤ y_j ≤ (2*T)^(j−1),  j≥1.
```

Indeed, `T*y_j−x_j=y_(j−1)≥0` and `x_j>0`. The first fundamental multiplier is `Af=2M+1`; its ordinate is `k=2*y_n(Af)`. Because X≥1 and Y≥8, straightforward inequalities give

```text
2*A < Af,    B=2*A−1 > 2*(Y+1),    B² > 2*Af.
```

If m≤n, then `c=y_m(A)≤(2A)^(n−1)<=(Af)^(n−1)<Y*k`, contrary to c≥Yk. If m≥2n, then `c≥B^(2n−1)>2*(Y+1)*(2Af)^(n−1)≥(Y+1)*k`, contrary to eta<k. Thus `n<m<2n`. The argument also covers n=1.

For any m whose ordinate is at least Yk, the next gap is `y_(m+1)−y_m=x_m+(A−1)y_m>k`. Consequently the interval `[Yk,(Y+1)k)` contains at most one positive main Pell ordinate. If it contains one, it fixes both m and `eta=c−Yk`; otherwise the partial family cannot satisfy the main norm. This is a uniqueness statement, not an existence proof or an equality between m and the graph rank.

## Actual signed-root congruences

The Pell identity modulo H yields `g−a*c≡2^m (mod H)` and `(g−a*c)*(g+a*c)≡1 (mod H)`. Therefore the actual literal root equation requires

```text
positive root d=+g:   2^m ≡ X       (mod H),
negative root d=−g:   2^m*X ≡ −1    (mod H).
```

For the positive branch, once a Pell ordinate c in the eta interval is given, its congruence is also sufficient for a natural gamma: `g−a*c>c>X`, because `Delta>(a+1)²` and the family has `c≥2q³>X`; hence

```text
gamma = 4*q²*w*sigma + (g−a*c−X)/H
```

is a natural integer. For the negative branch the displayed congruence is necessary but does not itself verify gamma≥0.

Independently reconstructing the compact Kprime recipe modulo the two primes below gives `H≡0` and the following data:

| prime p | X mod p | order of 2 mod p | log₂(X) | log₂(−X⁻¹) |
| --- | ---: | ---: | ---: | ---: |
| 16267 | 3981 | 5422 | 553 | 2158 |
| 16979 | 1876 | 16978 | 10155 | 15312 |

Thus a positive root requires `m≡31198741 (mod 46027358)`, and a negative root requires `m≡37842296 (mod 46027358)`. Both generalized CRT systems are compatible; neither excludes its branch. These are two verified prime divisors, not a claim that H has no other prime divisors. The checker verifies primality by trial division, reconstructs compact digits modulo each prime from the pinned source rows and slots, and exhausts the two small base-2 cycles. It reproduces the predecessor receipt and tests bounded Pell-growth controls. These computations do not instantiate giant Pell indices or prove a global absence of zeros.

Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary9-compact-partial-main-index-constraints/check.py | cmp - research/ordinary9-compact-partial-main-index-constraints/receipt.json
```

The nine-variable graph is a relaxation of a free-auxiliary-square child; its reverse bridge to the original parent remains open. No Lean, build, provider authentication, model transfer or proof-object check was run.
