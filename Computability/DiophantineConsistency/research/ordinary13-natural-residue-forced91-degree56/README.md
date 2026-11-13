# Four forced inputs: 13 naturals, 91 operations, degree 56

This external graph is a mixed natural shift of the compact-port
[13/82/56 positive residue carrier](../ordinary13-residue-first82/). It leaves
`J`, `X`, `f`, and the direct auxiliary ordinate `y` unshifted, while shifting
the other nine inputs. Its 13-natural-input graph has 91 live binary operations
and exact degree 56 at the authenticated compact44 ports. The local zero map
below applies to the graph's actual equations, not to the separately displayed
current-2011 equation.

## Simultaneous forcing and zero maps

Work in an ordered model V of IΣ₁ with the repository's natural-ring and
signed difference-ring interfaces. Assume beta and K0 are represented by
nonnegative model naturals; MC and MF may be arbitrary signed values for this
local argument. All nine shifted inputs, including `F,alpha,i,s,eta,zeta`,
are positive. Define

```
b=J*beta, q=1+b, Y=q³*s, k=eta+zeta,
c=eta+Y*k, a=Y*(X+1), H=3+4*a,
Delta=a²+H, U=Y*q², I=i*c², Q=Delta*(f²-1),
C=q-F-alpha, Bt=C*(X+K0)-F.
```

Then `q>=1`, `Y,U,I>0`, `c>=3`, `I>=2`, and `Delta>=3`. The four residuals
are squares in a sum; at a zero each residual is zero. The four conclusions
below are independent and apply simultaneously, without assuming any of the
other unshifted inputs positive.

1. If `J=0`, then `b=0`, `q=1`, `C=1-F-alpha<=-1`, and `X+K0>=0`.
   Thus `Bt<0`. The first carrier is `Z=b*t-Bt=-Bt>0`, whereas its norm
   residual is then `Z²=0`, a contradiction.
2. If `f=0`, then `Q=-Delta<0`, while the strong residual gives
   `Q=I²>0`.
3. If `y=0`, the auxiliary residual and strong residual give `Q*V²=1` and
   `Q=I²>=4`, with signed `V`. If V is zero the product is zero; otherwise
   the magnitude of V is a positive model natural, so `V²>=1` and the
   product is at least four. Both cases contradict the equality.
4. If `X=0`, then `a=Y` and `H=4Y+3`. The main norm is
   `Dstar²=U²*(1+Delta*c²)`. Applying the existing model square-divisibility
   theorem to the magnitude gives `U | Dstar` in the signed ring. Write
   `Dstar=U*d`. Since the literal main expression is
   `Dstar=U*a*c+H*shift`, one has `H | U*(d-a*c)`. The norm also gives
   `(d-a*c)*(d+a*c)=1+H*c²`, so an explicit multiplication and subtraction
   shows `H | U`. Now `4U=(H-3)*q²`, hence `H | 3q²`. But
   `Y=q³*s>=q³`, so `H=4Y+3>3q²>0`; a positive smaller model natural cannot
   be divisible by H. Contradiction.

These arguments use discrete order, signed magnitude, and square divisibility
in the stated IΣ₁ models; the graph-specific application has not been
elaborated in Lean. They establish that any mixed-shift zero has all 13 parent
inputs positive. Conversely, given a positive parent zero, take predecessors
for the nine shifted inputs and use the four positive values directly. Thus
positive-parent and natural-child zero existence are equivalent under the
stated port representations. The child's polynomial is exactly the parent's
polynomial under this **mixed** substitution; it is not pointwise identical to
its fully shifted natural polynomial at the same tuple.

## Degree, provenance, and comparison

The pinned positive parent has an [independent review of its standard-integer
zero maps and compact-port degree](../../reviews/ordinary13-residue-first82-independent/).
That review explicitly does not establish an arbitrary-model proof or Lean
endpoint; its fact-level calibration and inherited provider limitations remain
separate from the local model argument above. **The new mixed-shift transfer
and its iPRA endpoint have not been elaborated in Lean.**

The checker verifies the 91-row graph and exact mixed substitution, the norm
wiring and the A1 cancellation used in the degree upper bound, and authenticates
the compact P72/P115 port bytes. A compact-port all-inputs-equal ray has degree
56 modulo 1,000,000,007 and nonzero leading coefficient 58796952. The checked
residual upper bounds are 22, 28, 28 and 22, so the specialized polynomial
has exact degree 56. This is a degree assertion for that port tuple.

Numerically, this improves the separate [13/93/56 natural candidate](../ordinary13-natural-qcube-quotient93-degree56/)
in operations at the same variables and degree; the two have different parent
proof paths. The 13/95/28 and 13/94/50 candidates trade operations for lower
degree, while 13/86/99 uses fewer operations at higher degree. None of these
comparisons establishes a global frontier or a new current-2011 PDF binding.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-residue-forced91-degree56/build.py
python3 -I -S -B research/ordinary13-natural-residue-forced91-degree56/check.py
```

The deterministic checker result is [receipt.json](receipt.json). It verifies
source rows, liveness, forcing-formula wiring, the exact degree identity, port
hashes and ray; it does not itself prove the unbounded model argument or invoke
Lean.
