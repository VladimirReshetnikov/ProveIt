# P73 conditional auxiliary sphere: 91 operations, degree 30

This is a source-only same-zero transformation of the independently reviewed P73 91-operation, degree-30 circuit. It has the same 13 positive coordinates, four fixed compact44 ports, **91 live operations and exact degree 30**. It is an alternative representation, not an operation reduction; no global-minimality claim is made. Its mathematical proof uses a conditional nonzero fact, and the packet also gives an explicit positive-input counterexample to an unconditional one.

No Lean theorem, new JSON/PDF binding or independent replay of the upstream compiler, calibration or foundational proof is asserted. P73's original ordinary source and author-side endpoint retain the qualifications in [the P73 provider/source survey](../ordinary13-p73-provider-preflight/README.md).

## Equation and same-zero proof

Use the 13 strictly positive inputs `j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma`. Keep all P73 registers and put

```
a = X*Y+Y,    Delta = a²+4*a+3 = (a+2)²−1,
c = eta+(eta+zeta)*Y,    I = i*c²,
Q = Delta*(f²−1),    V = f²*(T*c−R)−c,
y = V+u,    Fa = y²−Q*(y²−V²),
As = f²−1−Delta*I².
```

The reviewed parent output and the candidate output are respectively

```
Pold = A0²+A1²+(Fa−1)²+As²,
Pnew = A0²+A1²+Fa²+As²−1.
```

All inputs and the fixed ports remain the same. Since `a>0`, `Delta≥8`; also `I>0` and `u>0`. We prove the two equations have the same zeros **at each positive input tuple**:

1. If `f≥2`, then `Q>1`. Suppose `Fa=0`. The equation is `Q*V²=(Q−1)*y²`. If either `V` or `y` is zero, both are zero, contradicting `y−V=u>0`. Otherwise, since `gcd(Q,Q−1)=1`, comparing prime valuations in this equality shows that every prime exponent in both `Q` and `Q−1` is even. Both are therefore positive squares, impossible for consecutive positive integers. Thus `Fa≠0` in this case.
2. If `f=1`, then `Q=0` and `Fa=y²`. When `Fa=0`, one has `As=−Delta*I²≤−8`. Consequently **`Fa²+As²−1≥0` for every positive input**: if `Fa≠0` its square is at least one; if `Fa=0` the strong square is at least 64.
3. `Delta` is 0 or 3 modulo 4, while `f²−1` is 0 or 3 modulo 4. Hence `Q` is 0 or 1 modulo 4, and `Fa` is congruent to `y²` or `V²` modulo 4. In particular, `Fa≠−1`.
4. If `Pnew=0`, the nonnegative terms `A0²`, `A1²` and `Fa²+As²−1` must all vanish. The `Fa=0` case is impossible by step 2, so `Fa²≥1`; equality then forces `As=0` and `Fa=±1`. Step 3 gives `Fa=1`. Thus the four parent residuals vanish and `Pold=0`. Conversely, `Pold=0` forces `A0=A1=As=0` and `Fa=1`, so `Pnew=0`.

The prime-valuation argument is an unbounded mathematical proof, not a finite search or a Lean theorem.

## Explicit positive input with `Fa=0`

Set every coordinate except `u` to 1, compute the actual-port rank `R` from the P73 graph, and set `u=R`. Here `J=4`, `q=4*beta+1`, `c=3`, and

```
R = (1+(q−1)²)*(q²−1) + 4*(MC+q*MF) > 0.
```

All ports are the authenticated positive compact44 values. With `f=T=1`, one gets `V=(c−R)−c=−R`, `y=V+u=0`, and therefore `Fa=0`. At this same positive tuple, `Delta=15`, `I=9`, and `As=−1215`. This disproves the tempting claim that `Fa` is nonzero for every positive P73 valuation. It does **not** claim the full candidate equation has a zero at this tuple.

## Circuit, exact degree and reproduction

The proposed [literal graph](polynomial.json) removes the parent's `Aa=Fa−1` gate, squares the already computed `Fa`, and adds one final subtraction by 1. The operation count is unchanged: 50 multiplications, 24 additions and 17 subtractions, with every gate, witness and port live. The local change obeys the exact polynomial identity

```
Pnew = Pold + 2*(Fa−1).
```

The reviewed parent has degree 30, and its independently checked difference-of-squares cancellation bounds `Fa−1` by degree 13. Thus the identity gives degree at most 30. The full candidate graph, evaluated with all witnesses `t` and the authenticated fixed-port bytes modulo 1,000,000,007, has degree 30 with nonzero leading coefficient 103566611. Its exact specialized integer degree is therefore 30. These are external graph and polynomial checks, not a Lean degree theorem.

Run from the repository root:

```
python3 -B Computability/DiophantineConsistency/research/ordinary13-p73-conditional-sphere91/check.py
```

The deterministic output is [result.json](result.json). The checker pins the reviewed parent graph and review receipt, verifies the entire graph delta, topology and liveness, evaluates both actual tails in an exact sparse integer-polynomial ring, authenticates all four compressed and raw little-endian port payloads, checks the full actual-port ray and constructs the positive `Fa=0` counterexample exactly. It also runs finite modulo-4 and coprime-square controls; the unbounded proof above does not depend on those controls. The source P61 payload paths are absent locally; the P72 byte copies match the P61 hashes as documented in the pinned review.
