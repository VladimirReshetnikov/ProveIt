# A bounded leading-term obstruction for the 72/46 shear

The exact 72-row current2011 [sheared candidate](../current2011-sheared72-46-candidate/polynomial.json)
has an auxiliary factor `U` of degree 23. Its square is the unique degree-46
term in the displayed sphere, so reducing this auxiliary degree would be a
natural route to a lower-degree equation. The candidate's positive-zero and
iPRA bridge remains unproved. This packet proves only the bounded polynomial
obstruction below; it gives no new equation or zero equivalence.

Put `q0=beta*J`, `k=eta+zeta`, `Y0=s*q0³`, and `E0=w*s*q0⁴`, with all
four ports treated as fixed degree-zero coefficients. The exact leading
homogeneous components are

```
P22  = −E0²*k²*Y0²,
H22  = i²*k⁴*Y0⁴,                         H = I²−A,
QW20 = 8*gamma*E0²*k*Y0*W2,              W2 = w*(q0−F−alpha)−z*q0,
U23  = −2*E0²*f⁴*k*Y0*T*y.
```

Here `P=N0`, `Q=N1`, `W=Nt`, `U=Na`, and `QW20` is the leader of
`Q*W−1`. The absence of degree 22 through 19 in Q comes from the exact
identity `Q=(X+gamma*H0)²+2*a*c*(X+gamma*H0)−H0*c²`, with
`H0=4*a+3`. In particular its degree-18 leader contains gamma.

Consider corrections

```
U' = U + A1*(P−1) + B1*H + C3*(Q*W−1)
```

where the multiplier polynomials have witness degrees `deg A1<=1`,
`deg B1<=1`, and `deg C3<=3`; their fixed integer coefficients may be
arbitrary, including precomputed combinations of the current ports. Each
individual product then has degree at most 23. **No such correction has
degree below 23** for the actual nonzero beta.

For proof, take the degree-23 homogeneous part. It is U23 plus the three
displayed residual leaders multiplied by the degree-1, degree-1 and
degree-3 homogeneous parts of their respective multipliers. Formally set
`i=gamma=0`. The H and QW terms vanish, and every remaining P contribution
is divisible by `k²`. But U23 is divisible by k exactly once: after
dividing by k, its remaining nonzero factors are independent of eta and
zeta. Since `k=eta+zeta` is a prime linear polynomial over the rational
polynomial ring, U23 is not divisible by `k²`. This contradicts cancellation.
The substitution is a formal polynomial specialization, not a proposed
positive witness. The actual beta is a nonzero integer, so specializing it
does not invalidate the argument.

The degree limits on the multipliers are essential. This result **does not**
rule out higher-degree multipliers whose leading products cancel via
syzygies, other residuals, coordinate changes, non-polynomial operations,
an alternate zero equation, or any global operation/degree minimum. It
also does not establish that the stated residuals vanish on a candidate
zero; that is part of the separate proposed zero bridge.

## Reproduction

[`check.py`](check.py) pins the literal 72-row graph and independently
propagates exact symbolic homogeneous layers in the integer polynomial ring
with all fourteen witnesses and four symbolic degree-zero ports. It keeps
eight top degree layers at each gate and tracks an upper ceiling on every
discarded term; it aborts if a leader could depend on discarded terms or
if its support guard is exceeded. It checks the four **complete** leaders
above, including the main-norm cancellation, against independent factored
expressions. The [receipt](result.json) records the graph hash, degrees,
support sizes and guard. The checker does not prove the divisibility
argument, invoke Lean, expand fixed port numerals, or verify the 72/46
zero bridge.

```
python3 -I -S -B research/current2011-shear-aux-leading-obstruction/check.py > /tmp/shear-leading.json
cmp /tmp/shear-leading.json research/current2011-shear-aux-leading-obstruction/result.json
```
