# Two coordinate identifications cannot preserve a positive zero

Use the definitions in the [13-variable sum-of-squares graph](../adaptive-square-sums/candidate.json).
At a positive zero of the full sum, both the auxiliary and strong residuals
vanish. Set `I=c²i`, `Q=Δ(f²−1)` and

```text
A2 = y² − Q(y²−V²) − 1 = 0
A3 = I² − Q = 0.
```

All variables are positive integers. Since `k=η+ζ≥2`, `c=η+Yk≥3`, and
`i≥1`, we have `I≥9`. Also `a=XY+Y≥2`, so
`Δ=a²+4a+3≥15`. The strong residual gives `Q=I²>0`, so `f²−1>0`.

* If `y=f`, substituting `Q=Δ(f²−1)` into `A2` gives
  `(f²−1)(1−Δ(f²−V²))=0`. Thus `Δ(f²−V²)=1`, impossible for integer
  `V` and `Δ≥15`.
* If `y=I`, substituting `Q=I²` into `A2` gives
  `I²(1−I²+V²)=1`, impossible for integer `V` and `I≥9`.

Consequently neither literal identification `y=f` nor `y=c²i` can extend any
positive full zero: they force an inconsistent pair of residual equations.
This is a direct integer argument for arbitrary coefficient ports, not a Lean
theorem or a claim that the original fixed-port equation has a zero. It
rules out these two simple same-coordinate witness transports; it does not
rule out other encodings or a less direct 12-variable equation.
