# Searching for a simpler counterexample

There is no coordinate-free total ordering called “simplicity.”  This
directory records exact Pareto comparisons using

1. maximum ordinary coordinate degree;
2. ambient dimension;
3. expanded monomial count;
4. primitive rational coefficient height; and
5. collision height.

The original three-variable map has maximum degree `7` and `16` expanded
monomials.  Exact affine and elementary-triangular searches did not improve
that representative.  These finite searches do not prove that ordinary
degree seven or sixteen monomials is globally minimal in dimension three.

The same polynomial is syntactically shorter if one names two repeated
subexpressions:

```text
u = 1+xy,       h = u^2 z + y^2(1+3u),
F = (u h, y+3x h, x(5-3u-x^2z)).
```

Its collision is itself a rational one-parameter family:

```text
F(t,-1/t,5/t^2) = F(0,2/t,-16/t^2) = (0,2/t,0),   t != 0.
```

Lean and Coq both check this identity for an arbitrary nonzero field element
(`Complex` in the Coq interpretation).

## A lower-degree stable counterexample

Write the original map as `F = (P,Q,R)` and put

```text
p = x y^2,       q = x^2 y z.
```

The degree-seven leading monomial of `P` is `pq = x^3 y^3 z`.  Introduce two
new variables `a,b` and define

```text
G(x,y,z,a,b) = (P - (a+p)(b+q), Q, R, a+p, b+q).
```

Expanded, this is

```text
G1 = z + 3xyz + 3x^2y^2z + 4y^2 + 7xy^3 + 3x^2y^4
     - a x^2 y z - b x y^2 - ab
G2 = y + 3xz + 6x^2yz + 3x^3y^2z + 12xy^2 + 9x^2y^3
G3 = 2x - 3x^2y - x^3z
G4 = a + xy^2
G5 = b + x^2yz.
```

Its coordinate degrees are `(6,6,4,3,4)`, and it has `22` expanded
monomials.  Thus it strictly lowers the conventional primary complexity
measure—maximum polynomial degree—from seven to six, at the cost of two
variables and six terms.

The construction is one elementary
[Bass–Connell–Wright](https://www.ams.org/bull/1982-07-02/S0273-0979-1982-15032-7/S0273-0979-1982-15032-7.pdf)
stable move.  Let

```text
S(x,y,z,a,b) = (x,y,z,a+p,b+q),
K(A,B,C,U,V) = (A-UV,B,C,U,V).
```

Both `S` and `K` are triangular polynomial automorphisms with Jacobian one,
and

```text
G = K ∘ (F × id_A^2) ∘ S.
```

Consequently `det(J_G) = det(J_F) = -2`.  The collision also lifts directly:

```text
G(-1,1,5,1,-5) = G(0,-2,-16,0,0) = (0,-2,0,0,0).
```

Run the independent exact discovery certificate with

```powershell
python Algebra/JacobianConjecture/Research/verify_simpler.py
```

The kernel-checked Lean and Coq developments are the trusted theorem boundary;
this script is retained to make the complexity calculation and construction
easy to reproduce.

## Stable degree frontier, down to the optimum degree

Repeating the same source-and-target shear idea gives the following exact
frontier.  “Terms” counts nonzero monomials after fully expanding every
coordinate.

| maximum degree | dimension | coordinate degrees | terms |
| ---: | ---: | --- | ---: |
| 7 | 3 | `(7,6,4)` | 16 |
| 6 | 5 | `(6,6,4,3,4)` | 22 |
| 5 | 6 | `(5,4,4,4,3,3)` | 27 |
| 4 | 7 | `(4,4,4,4,3,3,2)` | 32 |
| 3 | 10 | `(3,3,3,3,3,2,2,3,3,2)` | 49 |

Every row has primitive coefficient height `12`, Jacobian determinant `-2`,
and a lifted integral collision.  The degree-six row is independently
kernel-checked in both Lean and Coq.  The remaining rows have exact symbolic
certificates in [`verify_stable_frontier.py`](verify_stable_frontier.py): the
script constructs each map as

```text
K ∘ (F × identity) ∘ H
```

and mechanically checks that `J_H` is lower unitriangular and `J_K` is upper
unitriangular.  This proves the determinant claim without trusting a large
expanded determinant simplification.

The final row strictly improves the earlier 11-variable, 51-term reduction.
It shares the quadratic expression `xz+3y` between the second and third
coordinates, while retaining its multiple by `y` for the first.  Introduce

```text
T = xyz+3y²,                 E = e+xz+3y,
A = a+x²y²,                  C = c+T+3z,
D = d-xy,                    U = q-6xz+3e(d+xy),
S = s-az+7y²-c(d+xy),       H = h-x².
```

Then a compact compositional presentation is

```text
(P-AC+DS, Q-3AE-DU, R-HE, A-D², C, E, D, U, S, H).
```

All apparent terms above degree three cancel.  Expanding gives the following
explicit cubic map in variables `(x,y,z,a,c,e,d,q,s,h)`:

```text
-ac - adz - 3ay² - 3az - cd² + ds + 7dy² - sxy + 3xyz + 4y² + z
-3ae - 3axz - 9ay - 3d²e - dq + 6dxz + qxy + 12xy² + 3xz + y
-eh + ex² - hxz - 3hy + 2x
a - d² + 2dxy
c + xyz + 3y² + 3z
e + xz + 3y
d - xy
3de + 3exy + q - 6xz
-az - cd - cxy + s + 7y²
h - x²
```

It identifies the distinct integral points

```text
(-1,1,5,-1,-13,2,-1,-18,14,1)
( 0,-2,-16,0,36,6,0,0,-28,0)
```

with common image `(0,-2,0,0,0,0,0,0,0,0)`.  Maximum degree three is a
global optimum for any counterexample: [Wang's quadratic
theorem](https://doi.org/10.1016/0021-8693(80)90233-1) rules out degree at
most two in every dimension.  This is a degree optimum, not a claim that
dimension ten or 49 terms is globally minimal.

Run the whole stable frontier audit with

```powershell
python Algebra/JacobianConjecture/Research/verify_stable_frontier.py
```

The focused [`verify_degree_ten.py`](verify_degree_ten.py) certificate also
checks the final expanded formula directly against the compact composition.

## Exact rigidity inside the equivariant construction

The displayed three-variable map is homogeneous for the grading

```text
weight(x) = -1,   weight(y) = 1,   weight(z) = 2.
```

Every polynomial map with the same coordinate weights can be written, with
`t = xy` and `v = x^2 z`, as

```text
F = (p(t,v)/x^2, q(t,v)/x, x r(t,v)).
```

The quotients are polynomials precisely when each `t^a v^b` in `p` has
`a+2b >= 2` and each such monomial in `q` has `a+2b >= 1`.  A chain-rule
calculation in the localization at `x` gives the useful two-variable
determinant identity

```text
det J(F) = det [ -2p  p_t  p_v ]
                 [  -q  q_t  q_v ]
                 [   r  r_t  r_v ].
```

Both sides are polynomials, so the identity holds globally.  If this
determinant is a nonzero constant, diagonal scaling normalizes
`p_v(0)=q_t(0)=r(0)=1` and the determinant to `-1`.

There is also a general collision mechanism.  Write `a=[t^2]p`.  On the
plane `x=0`,

```text
F(0,y,z) = (a y^2 + z, y, 0).
```

If `r(t0,v0)=0`, then

```text
F(1,t0,v0) = F(0, q(t0,v0), p(t0,v0)-a q(t0,v0)^2).
```

The points are distinct.  Over an algebraically closed field every
nonconstant `r` has a zero, and `r(0,0)=1` makes that zero nontrivial.

[`verify_equivariant_degree_bound.py`](verify_equivariant_degree_bound.py)
enumerates every compatible monomial of ordinary degree at most six.  Exact
Groebner bases over `QQ`, across 23 exhaustive saturated branches, prove that
none can satisfy the Keller equations with nonconstant `r`.  Thus degree
seven is minimal for this automatic-collision construction.

For completeness, constant `r` reduces the determinant identity to the
two-variable Keller condition for `(p,q)`.  In degree at most six here,
`deg(p) <= 4` and `deg(q) <= 3` as polynomials in `(t,v)`, so the established
plane result through degree 100 applies; injectivity of `(p,q)` implies
injectivity of `F`, separately on `x != 0` and `x = 0`.  Consequently degree
seven is minimal for the entire equivariant class, using that external plane
theorem.  See [Moh's degree bound](https://doi.org/10.1515/crll.1983.340.140).

[`verify_equivariant_sparsity.py`](verify_equivariant_sparsity.py) then treats
the natural degree-seven subfamily in which `r` is affine and `p,q` are at
most linear in `v`.  The one-term cases `r=1+t` and `r=1+v` have empty Keller
loci.  With both terms present, scale to `r=1+t+v`; setting any one of eleven
coefficients used by the displayed map to zero makes the Keller ideal the
unit ideal.  The remaining `q40=0` branch is exactly the normalized displayed
map.  Hence its `7+6+3=16` expanded monomials are minimal among the
nonconstant-`r` Keller maps in this subfamily.  This is deliberately not
advertised as a global sixteen-monomial theorem.

Run both exact audits from the repository root:

```powershell
python Algebra/JacobianConjecture/Research/verify_equivariant_degree_bound.py
python Algebra/JacobianConjecture/Research/verify_equivariant_sparsity.py
```

They were validated with SymPy `1.14.0`.  The rational arithmetic and PASS
conditions are exact; Groebner-basis order and runtimes may vary across SymPy
versions.  On the reference machine the runs take roughly two minutes and
one minute respectively.

Outside this symmetry class, known theorems only give weaker degree floors:
[quadratic Keller maps](https://doi.org/10.1016/0021-8693(80)90233-1) are
invertible in every dimension, and the conjecture holds for three variables
through degree three
([dimension three and degree three](https://doi.org/10.1016/S0022-4049(98)00040-1)).
Thus any genuinely simpler three-variable counterexample has degree at least
four and, if its degree is below seven, must break the symmetry above.  The
two-variable Jacobian problem remains a separate open problem.

The research-report collection's
[`weighted-keller-rigidity`](../../../SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity/README.md)
(unformalized) extends the exact rigidity above to every degree for its
weighted class.  Gao's arXiv:2608.00222 describes a three-dimensional
counterexample of *geometric* degree four (four preimages of a generic
point); its ordinary coordinate degrees are `(4,11,12)`, so it does not
lower the ordinary degree below seven.
