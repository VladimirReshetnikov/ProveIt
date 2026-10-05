# A subpower upper bound for the forced selectors

For each fixed authentic original compiler, the fixed-prime quotient-carry construction admits selectors with the upper bound `z <= Q^(1+o(1))`, and the same upper bound holds for `F=Kz`. Precisely, for every real delta>0, all sufficiently large parameters on either already selected subsequence admit the inherited odd-scale construction with both `z <= Q^(1+delta)` and `F <= Q^(1+delta)`. This is only an upper bound; no matching lower bound or asymptotic equality is asserted. The binary population condition remains unproved.

## 1. Exact affine coprime interval

For an integer N>1 let omega(N) count its distinct prime divisors, let phi(N) be Euler's totient, and define

```
L(N)=floor(2^omega(N)*N/phi(N))+1.
```

Set L(1)=1. If beta is relatively prime to N, every interval of L(N) consecutive integer indices j contains an index with `gcd(alpha+beta*j,N)=1`, for every integer alpha.

For N>1, inclusion-exclusion over the squarefree divisors h of N gives the count

```
L*phi(N)/N + E,       |E|<2^omega(N).
```

Indeed beta is invertible modulo every h. Each divisibility condition therefore selects one residue class of j modulo h, whose count in a consecutive interval differs from L/h by strictly less than1. There are 2^omega(N) such divisors. By the definition of L(N), the main term is strictly greater than 2^omega(N), so the count is positive. For N=1 every integer is relatively prime to N.

## 2. The new interval is no longer than the old one

The application has N odd with5 not dividing N. For N>1,

```
phi(N)/(2^omega(N)*sqrt(N))
 = product_(p^a || N) p^((a-1)/2)*(p-1)/(2*sqrt(p)).
```

Every factor for p>=7 is at least1. The possible prime3 contributes at least1/sqrt(3), and prime5 is absent. Consequently

```
2^omega(N)*N/phi(N) <= sqrt(3N),
L(N) <= floor(sqrt(3N))+1.                         (1)
```

The latter inequality also holds at N=1. Thus the new search can replace the old search without increasing its selector upper bound or changing any prior explicit positivity threshold.

## 3. Subpower growth of the interval length

For every epsilon>0 there is a finite constant C_epsilon such that, for every positive integer N,

```
2^omega(N)*N/phi(N) <= C_epsilon*N^epsilon,        (2)
```

where the expression at N=1 is1. To prove this, use the exact product

```
2^omega(N)*N/phi(N)=product_(p|N) 2p/(p-1).
```

Choose a fixed prime cutoff P sufficiently large that `2p/(p-1)<=p^epsilon` for every prime p>P; for example, it suffices that p^epsilon>=4. Absorb the factors for the finitely many primes p<=P into C_epsilon. The remaining product is at most the epsilon power of the radical of N, and hence at most N^epsilon. This argument does not require N to be5-free; that hypothesis was used only in(1).

It follows that `L(N)<=C_epsilon*N^epsilon+1`, also at N=1.

## 4. Application to the unchanged source construction

Retain all notation and hypotheses of the committed fixed-prime theorem. In particular the compiler is fixed, `Q=B^n`, `A=odd(q)<2Q`, `N=A_out=A/A_S`, and

```
g<=D+1<=(d+1)n,
Cextra<=A_S^2<=(2B-1)^2*n^2,
M=m0*A*g*Cextra,       m0<=4d.
```

Its initial CRT representative satisfies `0<z0<=M`. Along `z=z0+M*j`, all already imposed fixed-prime carry congruences and the original m0 residue class remain unchanged. The quotient `(r+1)/(A*g)` is affine in j with slope relatively prime to N. Applying Section1 gives an index `0<=j<L(N)` retaining every exact denominator depth and hence

```
0<z<=M*L(N).                                      (3)
```

Equation(1) shows that(3) is bounded above by the old `Zmax` in the fixed-prime theorem. Its displayed `Zbound` and explicit inequality(10) therefore remain sufficient, unchanged. All inherited positive outer coordinates, odd-prime carry conclusions, input CRT budget, and exact transport follow on precisely their previous domains. The congruence search may initially use signed R; as in that theorem, the retained threshold establishes positive R before using its positive quotient carries.

For any epsilon>0, equations(2)-(3) give

```
z <= C'_epsilon*n^3*Q^(1+epsilon),               (4)
```

with C'_epsilon depending only on epsilon and the fixed compiler. Indeed A<2Q and N<=A, while all remaining displayed factors are bounded by fixed constants times n^3. Multiplication by the fixed positive K gives the same form for F=Kz.

Given delta>0, apply(4) with epsilon=delta/2. Since Q=B^n grows exponentially, the fixed constants and n^3 are at most Q^(delta/2) for all sufficiently large n. This proves the two explicit upper bounds in the opening paragraph along either inherited unbounded subsequence. Equivalently, for these selected representatives, `limsup(log(z)/log(Q))<=1` and `limsup(log(F)/log(Q))<=1`. Nothing here proves a lower bound of comparable size.

## 5. Binary boundary and provenance

The improvement controls only selector size. It does not prove `popcount(R)>=3*v2(q)+2`. In particular it does not recover z<=4d, nor does it guarantee z<Q. The old small-selector proof used three individual base-Q complement digits and untouched low repetitions of the fixed mask MC. Selectors allowed by(4) can occupy more than one Q digit, so that proof cannot be transferred merely by replacing its size bound. Literal coefficient sparsity alone supplies no established replacement estimate here. No actual complete source zero, rejected-input example, gate saving, or universal83 conclusion follows.

The following two dependencies were read as inert text and authenticated against their Git bytes at commit `006b3beab45d94d748da52f3a3b9b1c529240b2c`, under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:

| File | SHA256 |
|---|---|
| complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |

The first supplies the precise fixed-prime subsequences, CRT interface, polynomial factor bounds, and old positivity threshold. The second supplies the source-coupled affine construction and the still separate binary criterion. Their source, native/Pell, and compiler conclusions are inherited at their stated scopes. This follow-up proves only the sharper interval and selector upper bounds; it does not re-audit the full83 source.

This is a proof-only note. No supplied, archived, committed, frozen, or copied predecessor helper was executed or imported; no source array or enormous binomial/Pell instance was evaluated for it. No numerical corroboration is used in the proof.
