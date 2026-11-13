# Shifted-zeta parent: free auxiliary square and exact reverse criterion

The exact 85-row [eta/zeta parent](../ordinary13-eta-zero-graph-adapter-audit/prototype.json) uses the auxiliary witness y only through its single `y2=y*y` row. `candidate.json` deletes that row, replaces the witness by a natural `n_y2`, and retains the parent's **shifted** `zeta=n_zeta+1` convention. It has 84 rows and 13 natural inputs. The checker verifies an exact ordered expression-tree identity under the pointwise substitution `n_y2=y²`; thus every parent zero maps to a child zero at the same ports. This is a genuine one-gate candidate, but **its reverse existential map remains unproved**, so it is not a proved reduction or an iPRA endpoint.

There is a precise route for a reverse map at the same remaining data. Take an ordinary-natural child zero at natural ports with beta>0. The first, main and strong unit factors cannot be −1 modulo 4; their product with the auxiliary factor is 1, so each factor is +1. The checker exhausts the three generic residue patterns. The first norm and natural K0 rule out J=0, giving q≥2. Hence `c=Yk+eta>0`, with shifted s and k≥1, and `I=c²*i>1` because i is shifted positive. The strong factor then gives `I²=Delta*(f²−1)>0`; since Delta>0, f≥2. These are standard-integer statements; model factor extraction and casts are separate.

Let R denote the literal signed rank and retain all first/main/strong data. For m≥0 define the Pell pair for multiplier I by

```text
(x0,y0)=(1,0),
(x_(m+1),y_(m+1))=(I*x_m+(I²−1)*y_m, x_m+I*y_m).
```

The original parent's auxiliary factor is one exactly when

```text
(I*V)² − (I²−1)*y² = 1,
V=f²*(T*c−R)−c,     T≥1, y≥0.
```

By ordinary Pell classification with fundamental unit `(I,1)`, its nonnegative solutions are these `(x_m,y_m)`. The first coordinate is divisible by I exactly for odd m, while I>1 excludes m=0 and y=0. Consequently **a parent completion preserving the other data exists if and only if** there are an odd m≥1 and ε∈{−1,1} such that

```text
T = (ε*x_m/I + c + f²*R)/(f²*c)
```

is an integer at least 1. In that case use `y=y_m` and the displayed T; first/main/strong factors do not use either auxiliary coordinate and remain unchanged. Conversely any parent completion produces such an m and sign. Allowing a different first/main/strong witness could give additional reverse maps, so failure of this same-data criterion would not by itself disprove existential equivalence.

The outstanding work is to derive this criterion, or another witness replacement, from **every relevant child zero** in the intended arithmetic models and bind it to the fixed compact endpoint. Existing nonsquare auxiliary partial assignments do not discharge or refute it. The checker also verifies bounded Pell-quotient sufficiency controls; they do not prove universal solvability. No Lean, build, provider/axiom validation or complete equivalence is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-shifted85-free-aux-square-criterion/check.py | cmp - research/ordinary13-shifted85-free-aux-square-criterion/receipt.json
```
