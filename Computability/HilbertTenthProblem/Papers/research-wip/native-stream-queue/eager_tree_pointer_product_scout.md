# Eliminating finite eager Tree pointers with products of code differences

This bounded successor to the
[coded-lookup scout](eager_tree_coded_lookup_scout.md) removes every strictly
forward pointer coordinate and the two formally unused last-row fields `u,v`.
At external `N=8`, the complete source costs **1,001 = 408M+593A**, with
**102 natural witnesses, 67 residuals, and exact degree 72**. The degree-10
coded parent costs 1,172 operations with 188 witnesses and 91 residuals.
The new result is an exact **existential projection over the remaining natural
coordinates**, not a same-tuple identity or a zero-fiber bijection.

The [source](eager_tree_pointer_product_scout.py) and
[receipt](eager_tree_pointer_product_scout.json) authenticate the preceding
Python/JSON/proof trio and read its sixteen full selected degree-10 packets.
They execute no historical code. The public source interface is deliberately
bounded to the saved sizes `N=1,...,8`, with either parent cleanup option.
The uniform external-`N` template and general proof are stated below. No
fixed-arity universal polynomial, ordinary-input recoder, or global arithmetic
optimality is claimed.

## Exact natural projection

Use the preceding zero-preserving injective natural code

\[
P(u,v)=(u+v)^2+u,\qquad C(x,y,z)=P(z,P(x,y)).
\]

The parent already computes row codes `Cj=C(xj,yj,zj)` for `j=1,...,N−1`.
For each row `i`, its three target codes are

\[
\begin{aligned}
D_{i,0}&=t_3 C(b,y,u)+t_4 C(y,a,u),\\
D_{i,1}&=t_3 C(a,y,v)+t_4 C(u,b,z),\\
D_{i,2}&=t_3 C(u,v,z).
\end{aligned}
\]

Define the active ports
`A[i,0]=A[i,1]=t3+t4` and `A[i,2]=t3`. The common natural one-hot equation
still requires `sum(t0,...,t4)=1`, so these active ports are zero or one.
Replace both the pointer row-sum equation and the coded lookup equation for
slot `s` by the single residual

\[
R_{i,s}=A_{i,s}\prod_{j>i}(C_j-D_{i,s}).
\]

The empty product is one. All original local constructor, tag/output, and
three root-interface equations are retained literally.

For a natural parent zero, an inactive slot has all pointers zero and its
new residual vanishes. An active slot has exactly one pointer equal to one,
and the parent's lookup says that selected row code equals the target code.
That difference is a zero factor, so the new residual vanishes. Deleting all
pointer coordinates thus sends parent zeros to child zeros.

Conversely, take a complete child natural zero. Its unchanged one-hot
conditions make each active port zero or one. If it is zero, restore all slot
pointers to zero. If it is one, the finite product of integer differences is
zero. The integers have no zero divisors, so at least one later row has
`Cj=Di,s`. Restore a pointer equal to one at the least such `j`, with all
other pointers zero. This satisfies both deleted parent equations.
All choices are independent because the authenticated triangular parent has
no remaining height/flow equation or additional pointer consumer. Every
reference remains strictly forward. The constructor/code theorem then gives
the original field matches; no unbounded search or new decoder is invoked.

For the last row, the three residuals are `t3+t4,t3+t4,t3`. Thus every natural
child zero has `t3=t4=0` there. The last target-code cones are unused, and
both last-row `u,v` fields have no remaining source consumer. They are removed
as a **second, separate existential projection**, and the parent lift sets
them to zero. The parent's inactive targets vanish regardless of their old
values. No other last-row tag or field is eliminated, and no equation known
only on the zero locus is substituted into the arithmetic source.

Writing `pi` for deletion of all pointers and these two unused fields, the
precise theorem is

\[
F_{child}(r)=0\quad\Longleftrightarrow\quad
\exists p,u_{last},v_{last}\in\mathbb N:
F_{parent}(r,p,u_{last},v_{last})=0.
\]

The provided least-index lift is a right inverse to `pi` on child zeros.
It is not an inverse on all parent zeros. Different later rows may have the
same natural triple; selecting either gives distinct parent witnesses with
identical retained fields. The receipt contains two complete five-row parent
zeros for `(program,argument,output)=(10,0,0)`, differing by the pointer to a
duplicated `(0,0,1)` leaf. They project to the same child tuple. A separate
variation changes the last unused `u,v` to `7,11` and also preserves that
projection. Neither unique witness fibers nor a bijection is asserted.

The projection preserves the represented natural input/output triples at
each external size. The original finite certificate interpretation and its
unbounded family of sizes remain unchanged.

## Complete paid source and degree tradeoff

For a row with `m=N−1−i>0` later rows, the old coded lookup uses `m`
multiplications, `m−1` sum additions, and one subtraction: `2m` gates.
The product replacement uses `m` differences, `m−1` product multiplications,
and one multiplication by the active port, also `2m` gates. The active ports
already exist and stay charged. For `m=0`, the residual is the existing active
port: multiplying by the fixed empty product one is folded and not charged.
No constant-only or dead arithmetic gates survive.

The savings come from the deleted pointer row sums and their finalizer terms,
and from pruning the last row's entire target-code arithmetic. All remaining
row codes and target codes are paid, including their exact reuse of the
existing `F(a,y)` product. The source performs no global CSE, last-tag
normalization, or deduplication of equal residuals: the two identical last-row
`t3+t4` residual occurrences remain separately squared and accumulated.

With `c=0` for selective cleanup or `c=1` for the parent's extra cleanup,
complete ledgers are

\[
\begin{aligned}
\#w&=13N-2,&\#r&=8N+3,\\
M&=\frac{3N^2+81N-24}{2},&
A&=\frac{3N^2+(131-2c)N-38}{2},\\
M+A&=3N^2+(106-c)N-31.
\end{aligned}
\]

The pointer count removed is `3N(N−1)/2`, followed by the two unused fields.
The complete operation saving from the matching coded parent is
`3N(N−1)/2+6N+39`. This includes `N=1`. The exact complete degree is

\[
\max(10,10N-8).
\]

With cleanup enabled:

| N | Complete operations | M | A | Witnesses | Residuals | Exact degree |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 77 | 30 | 47 | 11 | 11 | 10 |
| 2 | 191 | 75 | 116 | 24 | 19 | 12 |
| 3 | 311 | 123 | 188 | 37 | 27 | 22 |
| 4 | 437 | 174 | 263 | 50 | 35 | 32 |
| 8 | 1001 | 408 | 593 | 102 | 67 | 72 |

To prove the degree, each row code has degree four and a branch target has
degree five, so a slot with `m>0` has residual degree at most `5m+1`. The
unchanged local residuals have degree at most five. For `N≥2`, the root's third
slot has the nonzero leading form

\[
(-1)^{N-1}t_{0,3}^{N}(u_0+v_0)^{4(N-1)}.
\]

Its degree is `5(N−1)+1`. The complete sum of squares therefore has degree
`10(N−1)+2`; highest real homogeneous squares cannot cancel. For `N=1`,
the unchanged constructor-input residual retains its degree-five term
`−t4(a+b)^4`, so the full degree is ten even though the zero equations force
`t3=t4=0`. Formal degree is not reduced using those zero equations.
The receipt independently verifies attainment by evaluating every supplied
port at one indeterminate `t`, propagating exact integer coefficient arrays
through each complete source, and matching a positive leading coefficient
to its separately propagated degree upper bound.

## Exact off-zero relation and bounded evidence

There is no polynomial equality or polynomial graph bijection. Over arbitrary
integer or rational parent assignments, let `r=pi(parent assignment)`. Every
unchanged residual still agrees literally, so the exact identity is

\[
F_{child}(r)-F_{parent}=
\sum R_{i,s}^2-
\sum(\text{old pointer row-sum residuals})^2-
\sum(\text{old coded-lookup residuals})^2.
\]

This formula includes arbitrary deleted pointers and last-row `u,v`, and is
checked against both full finalizers. It is an algebraic correction only;
the existential zero theorem uses natural one-hot tags and finite integer
products. No signed- or real-domain semantic equivalence is inferred.

The writer audits all sixteen full saved circuits, actual ledgers, liveness,
unchanged source rows, all deleted-coordinate privacy, and exact degrees.
It includes signed/rational full correction checks, independently generated
complete eager-evaluation zeros for all five rules with extra unused rows,
both projection and chosen-lift directions, and the two explicit nonunique
parent examples. Strict source/receipt/proof pins are checked before every
public build/map; malformed packet/assignment calls and `-O` execution are
rejected. The receipt contains exact counts and complete full sources.

The public functions are `build`, `checked`, `project_zero`, and `restore_zero`.
The last two accept complete natural zeros of the appropriate packet, check
that requirement, and return copies. They do not promise a map on arbitrary
nonzero assignments. Internal raw evaluation supports the algebraic checks.

```sh
python eager_tree_pointer_product_scout.py --root /path/to/parent-trio \
  --expect eager_tree_pointer_product_scout.json
```

`--root` defaults to sibling files. `--output FILE` writes a fresh deterministic
receipt. This work changes no repository file or Git state and runs no
historical author suite. The operation/degree/count theorem is conventional
mathematics with executable source checks, not a formal Lean theorem or a
global arithmetic optimum.
