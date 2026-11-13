# P73 auxiliary/strong unit pair: 90 operations, degree 54

This source-only packet gives a 13-positive, four-port graph with **90 live operations and exact degree 54**. It has the same positive zero set, at each same input tuple, as the independently reviewed [91/30 conditional sphere](../ordinary13-p73-conditional-sphere91/README.md), saving one operation at the cost of raising the degree. More strongly, the new graph and the original P73 sum-of-squares graph have the same zeros for **all integer inputs and integer port values**.

The reviewed 90/50 P73 equation uses the same domain and ports and strictly dominates this 90/54 point in degree at equal cost. The separately recorded 87/51 thirteen-positive alternative also has fewer operations and lower degree; its free-`J` witness encoding is distinct, so that comparison is not a same-valuation identity. No global minimality or frontier claim is made.

All fixed integer leaves remain those of P73 and are free under the same literal-circuit convention; every binary addition, subtraction, multiplication and square counts once. No Lean theorem, internal JSON/PDF binding, independently rebuilt foundational ancestry, or claim of consistency is supplied.

## Equation and global unit argument

For arbitrary integers `a,f,I,V,y`, define

```
Delta = a²+4*a+3 = (a+2)²−1,
Q = Delta*(f²−1),
Fa = y²−Q*(y²−V²),
Fs = f²−Delta*I² = 1+As.
```

The original P73 output and the new output are

```
Pold = A0²+A1²+(Fa−1)²+As²,
Pnew = A0²+A1²+(Fa*Fs−1)².
```

These have the same integer zeros, by a global modulo-4 argument:

- `Delta` is 0 or 3 modulo 4, and `f²−1` is 0 or 3; therefore `Q` is 0 or 1 modulo 4. Thus `Fa` is congruent to `y²` or `V²` modulo 4 and is never −1.
- `Fs=f²−Delta*I²` is 0, 1 or 2 modulo 4 and is never −1.
- If `Pnew=0`, each of its integer squares is zero, so `A0=A1=0` and `Fa*Fs=1`. Integer factors of 1 are either both 1 or both −1. The second case is excluded above, hence `Fa=Fs=1`; therefore `Fa−1=As=0` and `Pold=0`. The converse follows directly when the four original residuals vanish.

This argument does not need input positivity, `Fa≠0` as a global hypothesis, or a nonzero `Delta`. In particular the explicit positive input with `Fa=0` in the reviewed parent causes no problem: a product equal to 1 automatically makes each factor nonzero. It establishes global integer zero equivalence with **original P73**, not a claim that the conditional-sphere and original graphs are equivalent outside the positive domain. The latter was proved only for positive inputs in the reviewed parent.

## Literal graph and exact degree

The [graph](polynomial.json) changes the reviewed 91/30 conditional-sphere circuit as follows:

- Compute `Fs=f2−g72` in the original strong-residual slot; this costs the same as `As=f2m−g72`.
- Reassociate the existing difference of squares as `y²−V²=u*(y+V)`, using two gates as before. This preserves the exact polynomial and makes the degree bound visible.
- Replace the four-square-minus-one finalizer by `A0²+A1²+(Fa*Fs−1)²`. Accounting for the removed and added gates gives exactly 90: 50 multiplications, 24 additions, 16 subtractions. All gates, all 13 witnesses and all four ports are live.

The factored gap has syntactic degree at most 7, `Fa` at most 13 and `Fs` at most 14. The complete graph's syntactic output degree is at most 54. With all 13 witnesses set to `t`, the full graph evaluated at the authenticated actual port values modulo 1,000,000,007 has degree 54 and nonzero leading coefficient 832098066. Together these bounds prove exact specialized integer degree 54 externally; they do not constitute a Lean `totalDegree` proof.

## Reproduce

From the repository root run:

```
python3 -B Computability/DiophantineConsistency/research/ordinary13-p73-conditional-pair90-54/check.py
```

Its deterministic output is [result.json](result.json). The checker pins the conditional-sphere graph and independent review, reconstructs all source rows, validates topology/liveness and both exact elementary ring identities, and checks finite modulo-4 controls. It authenticates the compressed and raw little-endian bytes of all four actual P72 compact44 payloads and verifies their hashes against the P61 binding, then evaluates the complete graph on the modular ray. The P61 binding's own physical payload paths are absent in this checkout; the matching P72 copies are the bytes used here. The unbounded unit argument above is mathematical and is not replaced by the finite controls.
