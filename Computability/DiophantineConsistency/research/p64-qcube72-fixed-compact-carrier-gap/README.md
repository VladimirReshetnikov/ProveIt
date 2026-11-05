# The remaining carrier gap after the compact index window

The checked [fixed compact index-window theorem](../p64-qcube72-fixed-compact-index-window-draft/README.md)
produces, for an actual positive 72 zero in an IΣ₁ model, a first index `n`
with `n<R<2n`; the checked compact rank-window theorem gives `R+1<q⁴`.
The following is a **standard-integer deduction** explaining what remains to
recover the old carrier. It is not a Lean theorem about every IΣ₁ model.

Assume positive integers `q≥3`, `s`, `X`, and `h`, and nonnegative
integers `R,n,k,g,c`, with

```
Y=q³s, U=Y², a=XY+Y, H=4a+3,
U g = U(X+a c)+H h,
n<R<2n, R+1<q⁴,
k = 2n+4(X U)λ    for some λ≥0.
```

The last formula is an explicit assumption here. First Pell classification's
[`solution_residues`](../../Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean)
produces such a formula for an existentially selected index. To transfer it
to the already extracted `n`, one must identify the indices or apply the
Pell residue-quotient theorem directly to that `n`, as the beginning of
[`P64Early.early`](../../Lean/DiophantineConsistency/Compact44/P64Early.lean)
does. The actual first norm and first-coordinate classification have been
extracted for 72 zeros, but this packet does not claim the latter residue step
has been composed as a model-level theorem. The main carrier is also an
explicit assumption of the integer deduction.

Let `e=gcd(U,H)` and `mu=U/e`. Since `e` divides both `Y²` and
`3+4(XY+Y)`, [`P64Early.gcd_dvd_nine`](../../Lean/DiophantineConsistency/Compact44/P64Early.lean)
is a model-level source analogue of `e|9`; hence `e∈{1,3,9}`. From
`U | Hh`, cancel `e` and use `gcd(U/e,H/e)=1` to obtain `mu|h`.
[`P72Mu.gcd_cancel`](../../Lean/DiophantineConsistency/Compact44/P72Mu.lean)
is related represented cancellation machinery, but this packet does not
claim it has been composed into the conclusion here.

The size assumptions give

```
mu=Y²/e ≥ q⁶/9 ≥ q⁴ > R+1.
d=2n−R−1 satisfies 0≤d≤R−3<mu.
```

Consequently the precise same-witness carrier criterion is

```
∃ gamma∈ℕ, gamma>0 and U gamma = h+k−R−1
    if and only if    d=0 and U|h.
```

For the forward direction, the old carrier and `U|(k−2n)` imply
`mu|d` because `mu|h` and `mu|U`; the bounds on `d` force `d=0`.
Then `U|h`. Conversely, when `d=0` and `U|h`, the numerator is divisible
by `U`. It is positive because `h>0` and `k−2n=4XUλ≥0`, so its quotient
is a positive natural `gamma`. If `e=1`, `mu=U` and `U|h` is automatic.
When `e=3` or `9`, the current cancellation gives only `mu|h`; an additional
condition is required to establish `U|h`. The index window itself does not
supply the old carrier congruence needed to force `d=0`.

The checked symbolic [equal-rank full-zero negative control](../p64-qcube72-equal-rank-first-index-obstruction/README.md)
has `m=R=19259`, `n=11720`, so `n<R<2n` but `d=4180`, and its exact
finite check gives `U=729`, `H=759`, `e=3`, `mu=243`, and
`h≡486 (mod U)`. Here `d≡49 (mod mu)` and the old-carrier numerator is
`292 (mod U)`. This is at arbitrary ports with `MC>beta` and
`R+1≥q⁴`; it is not a counterexample at the fixed compact44 ports or to
existential equivalence.

[`check.py`](check.py) reruns that negative-control finite checker and tests
223,808 explicit integer instances of the criterion, including `e=1,3,9`.
These are finite controls, not a proof for IΣ₁ models or full graph zeros.
The general standard-integer proof is the divisibility argument above. Run
`python3 -I -S -B check.py`; retained output is [result.json](result.json).
