# Mixed-domain shifted guard: 14 inputs, 74 operations, degree 107

This **proposed mixed-domain** equation has 14 integer inputs: `F` is
**nonnegative**, while the other thirteen are **strictly positive**. Its
literal graph has 74 live operations and exact degree 107 at the
authenticated compact44 ports. It has the same zero-existence as the
all-positive [`14/75` five-unit parent](../ordinary14-negative-pell75/)
for every integer choice of ports, by the explicit coordinate bijection
below. The parent construction and this packet require independent review.
This is not a 74-operation all-positive equation, a new Lean/iPRA theorem,
PDF/JSON binding, fresh provider replay or global minimum claim; the parent's
endpoint and source qualifications remain inherited.

## Exact coordinate bijection

Let the all-positive parent's input be `F_old`. The new input is
`F=F_old−1>=0`, so `F_old=F+1` is a bijection from nonnegative F to
strictly positive `F_old`. Keep the other thirteen coordinates unchanged.
With `b=J*beta` and `q=b+1`, the parent's first scalar is

```
qF_old = q−F_old = b−F.
```

Thus retarget its `qF` gate to `b−F` without adding a gate; C, G, R and
every other dependent expression remain identical. The parent's guard and
guard factor are

```
guard_old = C*(X+K0)−F_old−b*h,
Fg_old    = 1+guard_old.
```

The new graph computes `guard=C*(X+K0)−F−b*h`, which is exactly `Fg_old`.
Use that existing guard directly as the fifth product factor and delete the
old `Fg=1+guard_old` gate. Every other factor and the final output are
unchanged. This identity holds for **all signed integer assignments** under
`F_old=F+1`; its positive/nonnegative restriction supplies the domain
bijection. In particular it does not rely on a solution, a source theorem, or
the sign of any fixed port.

## Count and exact degree

The checker verifies the exact two-row retargeting and single-gate deletion,
unique topology/liveness of all 74 gates, 14 inputs and four fixed leaves,
and 160 signed substitution controls for the complete output and named
intermediates. The parent has degree at most 107; an affine coordinate shift
does not increase total degree, so the new output also has degree at most 107.
Its full all-inputs-equal ray at the authenticated P72/P115 ports modulo
1,000,000,007 has degree 107 and leading coefficient 419359493, giving an
exact specialized integer degree of 107.

The degree/operation comparison with the 75-operation parent changes the
domain of F and must not be described as an all-positive reduction. The
finite controls do not replace the exact identity or any inherited
calibration/model proof.

```
python3 -I -S -B research/ordinary14-mixed-guard74/check.py > /tmp/mixed-guard74.json
cmp /tmp/mixed-guard74.json research/ordinary14-mixed-guard74/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-mixed-guard74-independent/`.
