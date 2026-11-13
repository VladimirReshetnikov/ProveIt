# An exact higher-degree residual syzygy

For the exact 72/46 current2011 sheared graph, let `P=N0`, `Q=N1`,
`W=Nt`, and `kY=k*Y`. The polynomial

```
S = 8*gamma*W*(P−1) + kY*(Q*W−1)
```

is a concrete example outside the earlier
[bounded correction screen](../current2011-shear-aux-leading-obstruction/README.md).
Each summand has degree 25, their degree-25 and degree-24 parts cancel,
and S has **exact degree 23**. The complete 28-term homogeneous leader,
with beta and the other fixed ports treated as degree-zero formal
coefficients, is recorded in [result.json](result.json). Thus one cannot
extend the earlier result to arbitrary higher-degree residual multipliers
merely by inspecting the leading terms of the individual products.

`S=0` whenever `P=1` and `Q*W=1`. This observation alone does not establish
that an altered sheared equation has the same zeros, nor does it supply a
72/46 model/iPRA bridge.

## A scoped cancellation test

Write `q0=beta*J`, `k=eta+zeta`, `Y0=s*q0³`, `E0=w*s*q0⁴`, and
`W2=w*(q0−F−alpha)−z*q0`. The prior packet derives

```
P22 = −E0²*k²*Y0²,
U23 = −2*E0²*f⁴*k*Y0*T*y,
```

while the leading strong and `Q*W−1` residuals vanish after the formal
specialization `i=gamma=0`. This packet checks the further exact identity

```
S23 evaluated at i=gamma=0 = −4*E0*k³*Y0³*W2.
```

It also follows directly: at gamma=0 the first summand of S vanishes, and
`Q=X²+2*X*a*c−H0*c²` has degree-16 leader `−4*E0*k²*Y0²`; multiplying
by the degree-5 `kY` and degree-2 W gives the displayed degree-23 term.

Consequently the following **bounded class still cannot cancel U23**:

```
U + A1*(P−1) + B1*(I²−A) + C3*(Q*W−1) + lambda*S,
deg A1<=1, deg B1<=1, deg C3<=3, lambda a fixed integer.
```

Take degree 23, then set `i=gamma=0`. The old residual terms are either
zero or divisible by `k²`; the S term is divisible by `k³`; U23 contains
exactly one k. Since actual beta is nonzero and `k=eta+zeta` is a prime
linear polynomial over the rational polynomial ring, the cancellation is
impossible. These are formal polynomial specializations, not positive
witness assignments.

The bounds are essential: this result does **not** exclude multipliers of
S with positive witness degree whose higher parts cancel with additional
syzygies, other syzygies or residuals, coordinate transformations,
alternate equations, or a global degree minimum. No literal improved graph,
new zero-equivalence or checked iPRA theorem is claimed.

## Verification

The source-pinned [checker](check.py) runs the previous exact homogeneous
leader engine and checks its receipt, independently forms the two
degree-25 summands, verifies their leading cancellation, checks the exact
degree-23 leader and its formal `i=gamma=0` specialization, and records all
28 leader monomials. Its predecessor tracks an upper ceiling on discarded
homogeneous layers; the new syzygy has discarded ceiling 21, so its leader
is exact. This finite computation does not itself prove the divisibility
argument or any zero map. No Lean/build/staging is performed.

```
python3 -I -S -B research/current2011-shear-degree25-syzygy/check.py > /tmp/shear-syzygy.json
cmp /tmp/shear-syzygy.json research/current2011-shear-degree25-syzygy/result.json
```
