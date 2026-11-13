# Thirteen natural inputs: 96 operations, degree 50

This proposed graph replaces the four-square finalizer of the proposed
[13/97/28 natural C-fold graph](../ordinary13-natural-cfold97-degree28/) by
a four-unit product. It has 13 nonnegative inputs, 96 live binary
operations and exact degree 50 at the authenticated compact44 ports. The
local graph transformation preserves zeros **pointwise for every integer
valuation and arbitrary integer ports**. The parent's positive-zero
calibration, fixed-port hypotheses and other endpoint qualifications remain
inherited. An [independent review](../../reviews/ordinary13-natural-cfold-product96-independent/README.md)
checks the all-integer unit argument, graph edit and degree. No Lean/iPRA theorem, PDF or
physical-byte binding, fresh provider replay, or global minimum is claimed.

## Four integer units

The parent output is

```
A0² + A1² + (Fa−1)² + g72².
```

The candidate instead outputs

```
(1+A0)*(1+A1)*Fa*(1+g72)−1.
```

Set `b=J*beta`, `q=b+1`, `M=q³*b`, `Delta=a²+4a+3`,
`Q=Delta*(f²−1)`, `I=i*c²`, and `y=V+u`. The existing graph has

```
A0=Z²−M²*(1+ell*(ell+k)),
A1=Dstar²−U²*(1+Delta*c²),
Fa=y²−Q*u*(u+2*V),  g72=I²−Q.
```

All four factors exclude −1 modulo 4 at every integer input:

* `b` and `q=b+1` have opposite parity, so `M=q³*b` is even and
  `1+A0 ≡ 1+Z² (mod 4)`, which is 1 or 2.
* `Delta` is 0 or 3 modulo 4. Hence `U²*(1+Delta*c²)` is 0 or 1,
  so `1+A1` is 0, 1 or 2 modulo 4.
* Both `Delta` and `f²−1` are 0 or 3 modulo 4, so `Q` is 0 or 1.
  Since `u*(u+2*V)=y²−V²`, the factor `Fa` is congruent to `y²` or
  `V²`, hence is 0 or 1.
* `I²` and `Q` are 0 or 1 modulo 4, so `1+g72` is 0, 1 or 2.

If the product output vanishes, all four integer factors are units ±1;
the four exclusions force all to be +1. Therefore `A0=A1=g72=0` and
`Fa=1`, and the parent's sum of squares is zero. Conversely, vanishing of
that sum forces those residual equations and hence makes the product zero.
This proof does not use any input sign, port bound, calibration, or machine
assumption.

## Operation count and exact degree

The graph replaces the parent's eight finalizer gates by three unit
increments, three product gates, and the final subtraction, giving 96 live
gates. It retains all 13 inputs and four fixed ports. The parent's
cancellation arguments bound the respective factor degrees by 14, 13, 13,
and 10, so the product degree is at most 50. At the authenticated P72/P115
ports, the all-inputs-equal ray modulo 1,000,000,007 has factor degrees
14, 13, 13, 10 and output degree 50 with leading coefficient 604845992.
Thus the specialized integer degree is exactly 50.

This is an intermediate tradeoff between the separate proposed
[13/88/99](../ordinary13-natural-unit-product88/) and
[13/97/28](../ordinary13-natural-cfold97-degree28/) natural graphs; none
dominates the others by operation count and degree. The checker pins both
graphs and port bytes, verifies the literal finalizer edit and liveness,
exhausts the small modulo-four controls, checks 300 signed graph controls,
and calculates the degree ray. These finite checks do not prove the
inherited calibration or endpoint.

```
python3 -I -S -B research/ordinary13-natural-cfold-product96/check.py > /tmp/natural13-cfold-product96.json
cmp /tmp/natural13-cfold-product96.json research/ordinary13-natural-cfold-product96/result.json
```
