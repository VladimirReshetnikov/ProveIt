# A simultaneous Pell certificate for finitely many positive powers

Research proof, 23 October 2026. This note concerns a new batching transformation of the explicit Pell power graphs. It is an ordinary mathematical proof, formalizable in ZFC. It is not a claim of a newly checked Lean theorem. The fixed-dimensional polynomial obtained by expanding and quadraticizing the equations below must be counted separately.

## 1. Notation and inherited arithmetic theorems

For an integer `a >= 2`, define nonnegative integers `X_j(a),Y_j(a)` by

```
X_0=1, Y_0=0,
X_(j+1)=a X_j+(a^2-1)Y_j,
Y_(j+1)=X_j+a Y_j.
```

Then `X_j(a)^2-(a^2-1)Y_j(a)^2=1`. We use the following two precise existing finite-certificate theorems, rather than an unnamed Diophantine representation.

**Pell index criterion.** For natural `a,k,x,y` with `a>=2` and `k<=y`, the nonzero branch of `Pell.matiyasevic` says that `x=X_k(a), y=Y_k(a)` when there are natural `u,v,s,t,b` satisfying

```
x^2-(a^2-1)y^2=1,
u^2-(a^2-1)v^2=1,
s^2-(b^2-1)t^2=1,
b>=2, v>0, y^2 divides v,
b == 1 (mod 4y), b == a (mod u),
s == x (mod u), t == k (mod 4y).
```

These conditions are also necessary for positive `k` and the indicated Pell coordinates. The `k=0` alternative is not used in this note.

**Power criterion.** For positive natural `n,k` and natural `m`, `Pell.eq_pow_of_pell` characterizes `m=n^k` by the existence of naturals `w,a,t,z` with `a>=2`,

```
X_k(a) == Y_k(a)(a-n)+m (mod t),
2an=t+n^2+1, m<t, n<=w, k<=w,
a^2-((w+1)^2-1)(wz)^2=1.
```

The subtraction `a-n` is natural subtraction in the source theorem; the inequalities established below make it ordinary subtraction here.

Primary source: the actual theorem statements and proofs in `Mathlib/NumberTheory/PellMatiyasevic.lean`,
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/PellMatiyasevic.lean>.
The GitHub blob read for this note has SHA `db9c757dd7cac29260397150fd190d72715ea3f8`.
ProveIt's supplied polynomial interfaces are `PellRepresentation.lean` and `PowerRepresentation.lean`; their finite criteria display precisely these hypotheses.

## 2. Simultaneous graph theorem, with the implemented substitutions

Fix a nonempty finite list of `q` power calls. Their specified values are positive integers

```
(n_i,k_i,m_i),  1<=i<=q.
```

Partition the calls into `r` nonempty classes with identical exponent values. For class `j`, denote its positive exponent by `e_j`; write `j(i)` for the class of call `i`, so `k_i=e_j(i)`. In an emitted circuit, classes can be restricted to *literally identical exponent wires*. No algorithm deciding equality of arbitrary arithmetic expressions is needed.

Introduce natural auxiliary variables

```
g,u,b, and x_j,y_j for 1<=j<=r,
```

and unrestricted integer auxiliary variables

```
z,v,lambda_B, lambda_i for 1<=i<=q, and s_j,r_j for 1<=j<=r.
```

The following are abbreviations for polynomial expressions, not additional unknowns:

```
W = sum_i (n_i+k_i)
A = 2 + sum_i m_i + g
U = u+2
X_j = x_j+1
Y_j = e_j+y_j
P = product_j Y_j
V = 4 P^2 v
B = 1+4P(b+1)
S_j = X_j+U s_j
R_j = e_j+4Y_j r_j
T_i = 2A n_i-n_i^2-1.
```

Impose exactly the following equalities:

```
(G1) A^2-((W+1)^2-1)(Wz)^2 = 1.
(G2) U^2-(A^2-1)V^2 = 1.
(G3) B-A = U lambda_B.

(I1_j) X_j^2-(A^2-1)Y_j^2 = 1.         [one per exponent class]
(I2_j) S_j^2-(B^2-1)R_j^2 = 1.         [one per exponent class]

(P_i) X_j(i)+Y_j(i)n_i-Y_j(i)A-m_i
        = T_i lambda_i.                 [one per power call]
```

**Theorem.** All equalities `m_i=n_i^k_i` hold if and only if the displayed finite system has auxiliary values in the stated domains.

At this unflattened graph level there are `4r+q+6` auxiliary variables and `2r+q+3` residual equations. These figures exclude the specified input/output slots and every wire subsequently introduced to keep the final degree four. They must not be advertised as the final variable count.

## 3. Soundness

All bounds needed by the original certificates are forced by the displayed system.

First `W>=2`, `A>=2`, `U>=2`, `Y_j>=e_j>=1`, `P>=1`, and `B>=5`. If `z=0`, equation G1 would give `A^2=1`, impossible. Therefore `z^2>=1` and

```
A^2 = 1+W^3(W+2)z^2
    >= 1+W(W+2)
     = (W+1)^2.
```

Consequently `A>=W+1>=n_i+1`. For every call the identity

```
T_i-A = (2n_i-1)(A-n_i-1)+(n_i+2)(n_i-1)
```

has a nonnegative right hand side. Thus

```
T_i >= A >= 2+sum_h m_h > m_i.
```

In particular `T_i` is a positive integer. This one common bound replaces every individual output-bound slack.

Next G2 and `U>=2` force `V!=0`. Replace `V` by the natural number `|V|` when applying the inherited index criterion; its square, positivity, and divisibility by `Y_j^2` are unchanged. Since `Y_j` divides `P`, the definition of `V` gives `Y_j^2 | |V|`. Similarly `z` can be replaced by `|z|` in G1.

For each class, the definitions of B,S,R and G3 give

```
B == 1 (mod 4Y_j),
B == A (mod U),
S_j == X_j (mod U),
R_j == e_j (mod 4Y_j).
```

The coordinates `X_j,Y_j,U,B` are natural, while S_j,R_j may be signed. The required three norms are I1_j,G2,I2_j. The signed strengthening proved in `SIGNED_INDEX_THEOREM.md` therefore gives

```
X_j = X_e_j(A), Y_j = Y_e_j(A).
```

Now P_i is exactly the power criterion's congruence, with terms moved to avoid subtraction in nonnegative gates. We have already proved `m_i<T_i`, `A>=n_i+1`, and the defining equality `2An_i=T_i+n_i^2+1`; also `n_i,k_i<=W` by definition of W. G1 with `|z|` supplies the last norm. The power criterion proves `m_i=n_i^k_i`, for every i.

No appeal to truth or consistency of ZFC occurs in this argument. In particular a false power tuple cannot become admissible merely because certificates share their parameters.

## 4. Completeness: choose the shared witnesses in three stages

Assume all `m_i=n_i^k_i`.

### Stage A: one cofinal bootstrap

Fix W from the inputs. The recurrence gives the elementary congruence

```
Y_l(W+1) == l (mod W),
```

because at base `W+1` its reduction modulo W is the base-one recurrence. Choose a positive multiple `l=W h` so large that

```
A = X_l(W+1) >= 2+sum_i m_i.
```

Such a multiple exists because the positive Pell X-sequence is strictly increasing and unbounded. Put

```
z=Y_l(W+1)/W,  g=A-2-sum_i m_i.
```

Then `z,g` are natural and G1 holds. For each exponent class, choose the true Pell coordinates

```
X_j=X_e_j(A),  Y_j=Y_e_j(A).
```

They satisfy `X_j>=1`, `Y_j>=e_j`, so natural x_j,y_j exist and I1_j holds. Now P is determined.

This ordering removes the apparent circularity of A depending on the power outputs. The theorem starts with a fixed true tuple of outputs; the auxiliary A is chosen only afterward. The same simultaneous graph equivalence remains valid when a surrounding equation connects one power's output to another power's base or exponent.

### Stage B: one common second Pell solution

Let `K=4P^2` and consider the integer matrix

```
M_A = [[A,A^2-1],[1,A]].
```

Its determinant is one. Modulo K it belongs to the finite group `SL_2(Z/KZ)`, so there is a positive integer d with `M_A^d` equal to the identity modulo K. Its ordinary integer power has the form

```
M_A^d = [[X_d(A),(A^2-1)Y_d(A)],[Y_d(A),X_d(A)]].
```

Set `U=X_d(A)` and `V=Y_d(A)`. Then `U>=2`, `V>0`, `U==1 (mod K)`, and `K|V`. Thus `u=U-2` and `v=V/K` are valid auxiliary values and G2 holds. Moreover `gcd(U,4P)=1`.

The finite-group argument is only a witness-existence proof. No matrix exponent, group cardinality, or variable exponent occurs in G1-G3 or the final polynomial.

### Stage C: one common comparison base

By CRT, since `gcd(U,4P)=1`, there are arbitrarily large positive integers B with

```
B == A (mod U),  B == 1 (mod 4P).
```

Choose one with `B>A` and `B>1+4P`. It has the form `B=1+4P(b+1)` for a natural b and satisfies G3 for an integer lambda_B.

For each class put

```
S_j=X_e_j(B),  R_j=Y_e_j(B).
```

The Pell recurrence is polynomial in its base, so B==A mod U gives `S_j==X_j mod U`. Furthermore X_e(B)>=X_e(A) when B>=A: the multiplication matrix M_B dominates M_A entrywise, and its nonnegative powers preserve that order. Hence `s_j=(S_j-X_j)/U` is natural.

Reduction of the Y-recurrence at B==1 mod4Y_j gives `R_j==e_j mod4Y_j`. Also `Y_e(B)>=e` for B>=1; this follows inductively from `Y_(h+1)=X_h+B Y_h>=1+Y_h`. Consequently `r_j=(R_j-e_j)/(4Y_j)` is natural. The definitions of S_j,R_j and I2_j hold.

Finally the usual power congruence follows directly in the ring `Z/T_i Z`: writing `D=A^2-1`, one has `(A-n_i)^2==D modT_i`. Evaluate

```
(A+sqrt(D))^k = X_k(A)+Y_k(A)sqrt(D)
```

at `sqrt(D)=-(A-n_i)`. The result is

```
X_k(A)-(A-n_i)Y_k(A) == n_i^k=m_i (mod T_i).
```

Therefore an integer lambda_i exists for P_i. This completes the simultaneous construction.

## 5. A useful orientation identity

The last quotient can even be chosen nonnegative, although an integer backend may prefer to leave it signed:

```
X_k(A)-(A-n)Y_k(A)-n^k
  = (2An-n^2-1) * sum_(j=0)^(k-2) n^j Y_(k-1-j)(A).
```

For k=1 the sum is empty and both sides vanish. For k>=2 this follows either by substituting the second-order Pell recurrence or by multiplying the generating functions

```
sum_h Y_h(A)t^h = t/(1-2At+t^2),
sum_h n^h t^h = 1/(1-nt).
```

Every summand on the right is nonnegative. The identity justifies positive orientation when a natural-variable circuit benefits from it. In the current unrestricted-integer quartic conversion, retaining a signed quotient can be cheaper than introducing a nonnegativity guard; orientation is consequently used to eliminate S,R coordinates, without requiring all quotient variables to be natural.

## 6. Domain and compilation cautions

1. Positivity of every base and exponent is a hypothesis of the batching theorem. A compiler must prove it at every call or keep the zero cases separately. It cannot infer positivity only after invoking the positive-power theorem.
2. The original power output is positive whenever its base is positive, so `m=m0+1` with natural m0 is a valid exact output parameterization. Factorial outputs are likewise positive. These reparameterizations can make later call invariants structurally apparent.
3. Distinct *bases* with the same exponent may share all four X,Y,S,R coordinates because the common auxiliary base A is independent of the original power base. Only T_i and the final power congruence remain call-specific.
4. A, W, U, B, P, V, S, R, T are polynomial abbreviations. Quadraticization must retain suitable product wires; substituting their high-degree expressions indiscriminately would not produce a quartic.
5. The entire power-output tuple can be fixed before constructing these new private witnesses. Sharing is unsafe only if a compiler also exposes the private A,U,B or other certificate coordinates to unrelated high-level constraints that were not included in the equivalence theorem.
6. Signed z and v are legitimate precisely because they occur through a norm and divisibility, with A,U>=2 forcing nonzero values where required. Allowing signed S,R uses the separate signed-index theorem, which resolves both signs modulo twice the main ordinate. The nonnegativity and lower-bound conditions on X,Y and the positive comparison base B are retained.

## 7. Why this differs from ordinary common-subexpression elimination

Ordinary sharing merges two calls only when both base and exponent agree. Here a finite collection of independent existential arithmetic witnesses is replaced by a jointly complete certificate. A common cofinal Pell base permits exponent-only sharing; a second common Pell solution makes all squared-coordinate divisibilities hold simultaneously; CRT supplies one comparison base for all indices. The proof of joint completeness is what permits these identifications. Equating arbitrary independently chosen witnesses without this proof would be invalid.

## 8. Corollary: derive nearby exponents instead of certifying them again

Suppose a finite acyclic dependency graph supplies some exponents from earlier exponents by literal equalities `e'=e+h`, where h is a fixed positive integer. A certified pair at e determines its pair at e' by h applications of

```
X_(e+1) = A X_e+(A^2-1)Y_e,
Y_(e+1) = X_e+A Y_e.
```

No additional integer unknown or norm certificate is needed for the derived pair. For the two small shifts used by the delivered graph, the formulas are

```
X_(e+1) = A X_e+(A^2-1)Y_e,
Y_(e+1) = X_e+A Y_e,

X_(e+2) = (2A^2-1)X_e+2A(A^2-1)Y_e,
Y_(e+2) = 2A X_e+(2A^2-1)Y_e.
```

The equivalent recurrence `X_(e+2)=2A X_(e+1)-X_e`, and similarly for Y, may use fewer shared arithmetic gates. It remains exactly the same polynomial identity; a signed arithmetic backend can retain this subtraction without imposing a separate sign restriction on its intermediate wires.

Use only the independently certified **seed** ordinates in the product P and only seed indices in I1/I2. Every derived pair is already the true positive Pell pair by induction on its dependency graph, so its separate divisibility, comparison norm, and progressions are unnecessary. The power criterion applies to its computed pair exactly as before. Completeness first chooses all seed pairs and then evaluates the recurrence formulas; there is no additional compatibility obligation.

If there are s seed indices, r total exponent classes, and q power calls, the graph-level counts become `4s+q+6` auxiliary variables and `2s+q+3` residual equalities, before the arithmetic products are quadraticized. The current instantiated arithmetic graph has q=40, r=19, s=16, so its batch contains 75 residual equalities. Its final quartic variable count must still come from the complete emitted system.

The independent graph auditor checks each exponent equality by collecting the actual emitted affine expressions, verifies both recurrence-coordinate identities by exact sparse polynomial arithmetic, and checks that the dependency graph is acyclic. Equality of a merely descriptive exponent label is not accepted as evidence of the identity.

## 9. Signed progression quotients in the released graph

The original simultaneous-completeness construction in Section4 supplies nonnegative s_j,r_j. The released graph permits them to be arbitrary integers, eliminating their nonnegativity guards. This enlarges the witness set but not the relation represented: `SIGNED_INDEX_THEOREM.md` proves that signed comparison coordinates still force the identical positive Pell index. The parameterization `X_j=x_j+1`, `Y_j=e_j+y_j` retains natural x_j,y_j. The distinction is essential; the signed-index theorem does not remove either of those two main-coordinate bounds.

