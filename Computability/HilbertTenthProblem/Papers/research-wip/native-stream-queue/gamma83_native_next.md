# Native gamma83: a formal factorization barrier and a genuine power-residue restriction

This proof-only continuation concerns the unresolved independent-gamma83 source. It gives two restrictions on a small-cofactor factorization attack. Neither bounds the alias period unconditionally nor proves a prime-power complement occurs on a genuine history.

For every fixed half-index, the native modulus polynomial is irreducible over the rationals, even after substituting any positive power for its base variable. Separately, on the actual histories supplied by the existing finite-prime filter, `H=3u^f` forces `gcd(f,30)=1`, `ord_31(u)=30`, and the exact native congruence `u=1+4q^3 mod8q^3`. These restrictions do not exclude a prime complement.

## 1. The exact native polynomial

At a canonical history the authenticated kernel gives

```
R=2r+1, X=2^R,
G_r(T)=sum_(j=0)^r binom(2r,r+j) T^j,
2Y=G_r(X), a=Y(X+1), H=4a+3.
```

Consequently the exact modulus polynomial is

```
H_r(T)=2(T+1)G_r(T)+3,       H=H_r(2^R).             (1)
```

**Theorem.** For every integer `r>=0` and `k>=1`, `H_r(T^k)` is irreducible in `Q[T]`.

Put `c_j=binom(2r,r+j)`. The constant coefficient of `H_r` is the odd integer `2c_0+3`; its leading coefficient is exactly `2c_r=2`. Every other coefficient is even: for `1<=j<=r` it is `2(c_(j-1)+c_j)`. Substitution of `T^k` inserts only zero coefficients. Thus the reciprocal

```
F_(r,k)(T)=T^(k(r+1))*H_r(T^(-k))
```

has odd leading coefficient, every lower coefficient divisible by2, and constant coefficient exactly2. It is primitive, since the leading coefficient is odd and the constant is2.

For completeness, the reciprocal-Eisenstein argument is elementary. A rational factorization would, by Gauss's lemma, give two positive-degree integer factors. Both leading coefficients would be odd. Modulo2 their degrees are preserved and their product is a pure power of T, so each reduction is a positive power of T. Both constant coefficients would be even, making their product divisible by4, contrary to the exact constant2. Hence the reciprocal is irreducible. Reciprocal substitution preserves reducibility for polynomials with nonzero constant coefficient, proving the claim.

This applies to both the formal native base (`k=1`) and the formal binary base (`k=R=2r+1`), before specializing T to2. It also excludes an identity `H_r(T^k)=c*P(T)^j` for nonconstant `P in Q[T]`, rational `c!=0`, and `j>=2`.

**Scope.** This excludes a nonconstant rational-polynomial factorization for each fixed r,k. It does not exclude a fixed numerical cofactor or constrain numerical specialization to preserve irreducibility. In particular `H_r/3` is a valid rational polynomial: a constant scalar is a unit in `Q[T]`. Indeed `H_r(-1)=3`, so `3|H_r(2^R)` for every odd R. The small formula example `r=1,R=3` gives `H_r(8)=183=3*61`, despite irreducibility; it is not a compiler history. Index-dependent congruences, numerical factorization and other transformations remain open.

## 2. A restriction on genuine filtered histories

Fix any accepted positive input of any unchanged original compiler and choose adequate spatial padding h. The compiler has `d=5^s`, `s>=1`, and h is also a power of five. The lower bound on s follows because the inner exponent is a power of five and the inner radix is at least16. Therefore `E=dh` is a multiple of5.

The pinned finite-prime-avoidance theorem constructs genuine accepting histories, with fresh positive84 and independent-gamma83 witnesses at that same input, such that

```
E|R,       p | binom(R-1,(R-1)/2)
```

for every prime p dividing `2^E-1`. This is an actual ignored-bit construction preserving the computation, masks, packing bounds, population and temporal condition; no index is freely substituted. Since `31=2^5-1` is prime and `5|E`, it is one of these primes. At every resulting history,

```
X=2^R=1 mod31,       binom(2r,r)=0 mod31.
```

Symmetry of a full binomial row gives

```
G_r(1)=(2^(2r)+binom(2r,r))/2,
a=(X+1)G_r(X)/2=2^(R-2)+binom(2r,r)/2=1/4 mod31.
```

Hence the exact residues are

```
H=4 mod31,                  H/3=22 mod31.            (2)
```

Here `3|H` is an inherited native fact and3 is invertible modulo31. The element22 has exact order30, as witnessed by

```
22^30=1, 22^15=-1, 22^10=5, 22^6=8 mod31.
```

The last three tests remove all proper prime-index divisors of30. If this genuine H has a representation `H=3u^f`, `u>0`, `f>=1`, then u is a unit modulo31. With `s=ord_31(u)`, the power-order identity gives

```
30=ord_31(u^f)=s/gcd(s,f),       s|30.
```

Thus `s=30` and `gcd(f,30)=1`. Equivalently u must be `22^(f^(-1) mod30)` modulo31. This applies to every integer u, not only prime u: the complement cannot be a square, cube or fifth power on this subclass.

The two other small cofactors considered in the preceding radical-order note have analogous necessary conditions on these same histories:

| Representation | Required residue of `u^f` modulo31 | Exact order | Necessary exponent condition |
|---|---:|---:|---|
| `H=3u^f` | 22 | 30 | `gcd(f,30)=1` |
| `H=9u^f` | 28 | 15 | `gcd(f,15)=1` |
| `H=15u^f` | 23 | 10 | `gcd(f,10)=1` |

For the last two rows use the same order formula: because30 is square-free, a prime in the displayed order cannot divide f. These are necessary congruence conditions, not integer converses or assertions of factorization occurrence. In fact the finite-prime filter also has `v3(H)=1`, which already excludes the entire `H=9u^f` row on this subclass; it is displayed only to distinguish its residue test from that stronger inherited obstruction.

## 3. The exact native two-adic size condition

Root suggested keeping the exponent restriction tied to the native population. Write `q=2^t`. Every canonical history under discussion satisfies

```
popcount(R)=3t+2.
```

The central binomial coefficient has valuation `v2(binom(2r,r))=popcount(r)=popcount(R)-1`. Every j>=1 term in `G_r(2^R)` is divisible by `2^R`, while the central valuation is less than R. Therefore there is no cancellation at that valuation and

```
v2(Y)=popcount(R)-2=3t,
v2(a)=3t,
v2(H/3-1)=v2(4a/3)=3t+2.                          (3)
```

Now suppose `H=3u^f` on a filtered history. Section2 forces f odd, and H/3 is odd so u is odd. The factor `(u^f-1)/(u-1)=1+u+...+u^(f-1)` is odd. Since H>3, u>1, and (3) yields

```
v2(u-1)=3t+2,
u=1+4q^3 mod8q^3,       u>=4q^3+1.                (4)
```

Thus a possible prime complement ell must satisfy both the exact order30 condition modulo31 and (4); for f=1 its first residue is simply `ell=22 mod31`. These congruences are compatible and neither proves nor refutes prime occurrence.

The filter also gives `v3(H)=v3(Delta)=1`, so these actual histories lie in the exact `m=m_rad` subclass of the previous note. If `H=3*ell^f` with ell prime were eventually certified there, the old theorem would still give `m|3`. The present note narrows f and ell but does not produce them, prove a rejected-input alias, or apply the31 restriction to every canonical history without the filter.

**Retained arithmetic correction.** A preliminary message incorrectly said `H=2 mod31` and hence `H/3=11 mod31`. Root identified this before freeze. The literal equations give `a=1/4`, so `4a+3=4`, not2. Equation(2) and the order tests here are the corrected statements. The order30 exponent conclusion survives, but the earlier residues must not be reused.

## 4. Dependencies and bounded checks

Paths are relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`. All were authenticated as inert bytes.

| File | SHA256 |
|---|---|
| gamma83_next_arithmetic.md | 4298f6f64d4c9e1037901df3e0d50095ee126b9e31a82106db60643365d64f93 |
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 |
| complete83_independent_gamma_scout.md | bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41 |
| complete83_gamma_native_finite_prime_avoidance.md | 93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96 |
| complete83_gamma_power_tests.md | 4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

The radical-order, finite-prime and power-test notes were reread in full. The compiler's fixed-layout Section1 was reread to bind its radix and five-power assumptions. The inherited source audit and native/fiber theorems retain their original scope; there is no new full83 row audit. The repunit-filter, residual-order, small-prime-digit and compiler-order notes were also read as comparison context; their residual-order limitations remain intact.

Fresh, unsaved standard-library arithmetic corroborated 328 reciprocal coefficient cases (`0<=r<=40`, `1<=k<=8`) and 1,312 polynomial evaluations. It checked the three residue orders and360 finite exponent/residue classifications, eight small half-binomial specializations, and97 direct half-binomial residues with the required carry at31 among `15<=R<3000`, `R=15 mod20`. The coefficient check was corrected before its successful run to test leading and constant entries in ascending coefficient order. None of these small indices is claimed to be a compiler history. No full83 zero, complete native order, prime complement or enormous Pell tuple was computed. These are bounded corroborations, not a frozen executable evidence packet.

No supplied, archived, committed, frozen or copied predecessor program was run or imported, and no repository/Git object changed. Independent-gamma83 remains unresolved. The remaining target is a numerical order or factor certificate on a genuine native history; the formal polynomial barrier and necessary factor congruences do not provide one.
