# The Jacobian conjecture is false in dimension three

This project gives independent kernel-checked Lean 4 and Rocq/Coq proofs for
the polynomial map announced by Levent Alpöge on 19 July 2026.  Write

```text
P = (1 + xy)^3 z + y^2 (1 + xy) (4 + 3xy)
Q = y + 3x (1 + xy)^2 z + 3xy^2 (4 + 3xy)
R = 2x - 3x^2y - x^3z.
```

A shorter presentation of exactly the same three-variable map is

```text
u = 1+xy,       h = u^2 z + y^2(1+3u),
F = (u h, y+3x h, x(5-3u-x^2z)).
```

For `F = (P,Q,R)`, formal differentiation and polynomial normalization give

```text
det(J_F) = -2.
```

This is a nonzero constant over `C`.  Nevertheless, the three distinct
rational points

```text
(0, 0, -1/4), (1, -3/2, 13/2), (-1, 3/2, 13/2)
```

all map to `(-1/4, 0, 0)`.  A denominator-free collision, also checked in
the development, is

```text
F(-1, 1, 5) = F(0, -2, -16) = (0, -2, 0).
```

Both proof assistants also check the full one-parameter family, for `t ≠ 0`,

```text
F(t,-1/t,5/t^2) = F(0,2/t,-16/t^2) = (0,2/t,0).
```

The integral collision is its `t=-1` instance; that identification is itself
a checked lemma in both developments.

## Equivariance

Both developments also prove the exact symmetry

```text
F(-x, -y, z) = (P, -Q, -R)(x, y, z),
```

an equivariance between the linear involutions `(x,y,z) ↦ (-x,-y,z)` and
`(u,v,w) ↦ (u,-v,-w)`.  Whenever the image of a point is fixed by the target
involution, the point collides with its mirror.  The formalizations exploit
this: the third rational collision point `(-1, 3/2, 13/2)` is the mirror of
the second, so its image is obtained by rewriting rather than a fresh
polynomial evaluation, and mirroring the integral collision produces a
further integral collision `F(1,-1,5) = F(0,2,-16)` for free — the `t = 1`
member of the family.  The rational family is closed under the symmetry,
which acts on the parameter by `t ↦ -t`.  The two-variable stable shear
respects the same symmetry once the added variables `a, b` are also negated,
so the five-variable degree-six representative satisfies the analogous
equivariance with target involution `(v₀,…,v₄) ↦ (v₀,-v₁,-v₂,-v₃,-v₄)`.

The discrete symmetry is the `s = -1` slice of a full weighted torus action:
`F` is homogeneous for the grading `weight(x,y,z) = (-1,1,2)`, and both
developments prove

```text
F(x/s, sy, s²z) = (s²P, sQ, R/s)          (s ≠ 0),
```

and that scaling therefore carries collisions to collisions.  The family
files are organized around this action: the parameter-`t` member is
*defined up to one checked identification* as the scaling by `1/t` of the
mirrored integral collision, and every family property — the common
values, the collision, the mirror symmetry acting on the parameter by
`t ↦ -t`, and the inverted parametrization — is derived from the torus
action and the single integral collision by rewriting, with no further
polynomial evaluation.

Thus `F` is not injective and cannot have a set-theoretic left inverse, much
less a polynomial two-sided inverse.  It refutes the dimension-three
Jacobian conjecture over `C`; adjoining untouched coordinates gives the same
conclusion in every dimension at least three, and the Lean development
formalizes that stabilization outright
(`jacobianConjectureInDimension_false_of_three_le`): the padded map's
Jacobian is block triangular with the renamed three-by-three Jacobian and an
identity block, so its determinant is still `-2`, and the zero-padded
collision still identifies two distinct points.

## A kernel-checked lower-degree representative

There is no single ordering of polynomial maps called “simplicity,” but
maximum ordinary degree is the conventional first measure.  A two-variable
stable shear lowers that measure from seven to six.  With new variables
`a,b`, define

```text
G1 = z + 3xyz + 3x^2y^2z + 4y^2 + 7xy^3 + 3x^2y^4
     - a x^2 y z - b x y^2 - ab
G2 = y + 3xz + 6x^2yz + 3x^3y^2z + 12xy^2 + 9x^2y^3
G3 = 2x - 3x^2y - x^3z
G4 = a + xy^2
G5 = b + x^2yz.
```

Lean and Coq independently check the coordinatewise degree-six bound, the
formal identity `det(J_G)=-2`, and the collision below.  Exact expansion gives
the sharper degree profile `(6,6,4,3,4)`:

```text
G(-1,1,5,1,-5) = G(0,-2,-16,0,0) = (0,-2,0,0,0).
```

The construction is transparent: if `p=xy^2` and `q=x^2yz`, then

```text
G = K ∘ (F × id^2) ∘ S,
S(x,y,z,a,b) = (x,y,z,a+p,b+q),
K(A,B,C,U,V) = (A-UV,B,C,U,V).
```

Both added maps are unitriangular, so the determinant and collision are
  preserved.  Further exact stable reductions reach degrees five, four, and
finally the globally optimal maximum degree three in ten variables.  The
full formulas, integral collisions, scope caveats, and reproducible exact
certificates are in [`Research/README.md`](Research/README.md).

## Formal statement boundary

The Lean conjecture quantifies over finite tuples of multivariate polynomials;
the Coq development states the corresponding three- and five-variable
instances.  A map satisfies the Keller condition when its *formal* Jacobian
determinant is a nonzero constant polynomial.  Polynomial invertibility means
that another polynomial tuple induces a two-sided inverse on points.  The
collision therefore disproves an explicit universal proposition, rather than
merely certifying two unrelated calculations.

Over a characteristic-zero field, hence an infinite field, these pointwise
composition laws are equivalent to the corresponding formal polynomial
composition identities.

The Lean proof uses mathlib's `MvPolynomial.pderiv` and `Matrix.det`; its main
three-variable result is field-generic in characteristic zero and is
instantiated at `Complex`.  The Coq proof independently defines small
three- and five-variable polynomial syntaxes, formal partial differentiation
by the product rule, and explicit determinants, then interprets them in
Coquelicot's complex field `C`.

Neither proof relies on a computer-algebra result.  The `ring`, `norm_num`,
and `field` tactics construct proof terms that the respective kernels check.
The audit modules print the assumptions of the headline theorems.  In
particular, the Coq complex interpretation transparently inherits
Coquelicot's standard real-number and functional-extensionality assumptions;
there are no admitted results.

## Checking

From the repository root:

```powershell
lake --dir Algebra/JacobianConjecture/Lean build
lake --dir Algebra/JacobianConjecture/Lean env lean `
  Algebra/JacobianConjecture/Lean/JacobianConjecture/Audit.lean

coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/Common.v
coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/Counterexample.v
coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/Scaling.v
coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/CollisionFamily.v
coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/SimplerCounterexample.v
coqc -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  Algebra/JacobianConjecture/Coq/Audit.v
coqchk -silent -Q Algebra/JacobianConjecture/Coq JacobianConjecture `
  JacobianConjecture.Common JacobianConjecture.Counterexample `
  JacobianConjecture.Scaling JacobianConjecture.CollisionFamily `
  JacobianConjecture.SimplerCounterexample JacobianConjecture.Audit

python Algebra/JacobianConjecture/Research/verify_simpler.py
python Algebra/JacobianConjecture/Research/verify_stable_frontier.py
python Algebra/JacobianConjecture/Research/verify_degree_ten.py
```

The map's provenance is Alpöge's
[public announcement](https://x.com/__alpoge__/status/2079028340955197566).
Every identity needed for the counterexample is proved again inside each
formal development.
