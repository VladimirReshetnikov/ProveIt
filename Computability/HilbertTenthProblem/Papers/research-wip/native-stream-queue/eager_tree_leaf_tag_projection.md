# Eliminating the leaf tag in finite eager Tree certificates

The complete cleaned eight-row source uses **955=397M+558A operations**, **91 natural existential witnesses**, and exact degree **72**. At one row it uses **45=19M+26A**, seven natural witnesses, and exact degree6. Compared with the frozen [terminal projection](eager_tree_terminal_projection.md), this deletes one tag coordinate per row and saves exactly **2N−1 additions/subtractions**, with no multiplication increase in the complete polynomial.

This is a finite-source successor at external `N=1,...,8`. It preserves the full natural zero tuples of that particular parent by an explicit bijection. It does not remove the external size parameter, recover earlier discarded pointer/circulation witnesses uniquely, or provide a new ordinary-input decoder or fixed-arity universal representation.

The [source](eager_tree_leaf_tag_projection.py) and [receipt](eager_tree_leaf_tag_projection.json) contain all sixteen literal schedules: eight sizes and both settings of the parent's optional `0+b` cleanup. All arithmetic, guard terms and final accumulation are charged. The parent trio is authenticated on every public call, with no historical Python import:

| Parent artifact | SHA-256 |
|---|---|
| Python | `edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd` |
| JSON | `25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95` |
| Markdown | `ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b` |

## The literal coordinate change

All supplied fields remain natural integers, including zero. In a nonterminal row define

```
s_i=t[i,1]+t[i,2]+t[i,3]+t[i,4].
```

The terminal parent has already removed its final `t3,t4`, so at its last row
`s_i=t[i,1]+t[i,2]`. Eliminate the supplied `t[i,0]` and restore it in the proof by

```
t[i,0]=1-s_i.
```

The actual parent's only two consumers of each t0 are its tag-sum chain and its leaf-output residual `t0*(z-S(y))`, with `S(y)=2y+1`. The emitter checks that exact consumer closure before changing anything. It drops the old tag-sum residual, whose restored value is identically zero. It replaces the leaf residual by

```
(s_i-1)*(z-S(y)).
```

This is the negative of the restored parent leaf residual, so its square is exactly unchanged. Every other residual keeps its source expression. The new term for the row is the **unsquared integer guard**

```
G_i=s_i*(s_i-1).
```

The output is the sum of the retained `7N` residual squares and the `N` guards. Its metadata distinguishes `square` and `integer_nonnegative_guard` terms. There are **8N nonnegative terms on integer assignments**, not8N residual squares. In particular `s_i-1` is not required to vanish: `s_i=0`, representing the leaf rule, is permitted.

## Exact correction and natural zero bijection

Let r denote all retained supplied coordinates and let `R(r)` restore every t0 as `1-s_i`. Over arbitrary integer or rational assignments the complete polynomial identity is

```
F_child(r) = F_terminal(R(r)) + sum_i s_i*(s_i-1).
```

It is a correction identity, not equality of the two full polynomials. The original tag-sum squares vanish under R, and the old/new leaf squares agree by their opposite signs. All other squares agree literally. The checker expands the actual local tag, leaf and guard cones in independent tag coordinates before applying those proved cuts to all remaining source DAGs.

For any natural child assignment, every s_i is an integer and `s_i(s_i-1)>=0`. The restored parent expression is a sum of real squares even if an off-zero restored t0 is negative. Thus if the child output is zero, each guard is zero and the restored parent output is zero. Each s_i must be0 or1. Consequently every restored t0 is a natural integer, and R(r) is a complete natural parent zero.

Conversely, a natural parent zero satisfies its one-hot equation `t0+s_i=1`. Hence `s_i` is0 or1, the guard is zero, and the parent coordinate t0 is exactly `1-s_i`. Projecting away t0 therefore gives a child zero. Projection and restoration are inverse on the full natural zero sets of the two specified sources. This argument does not assume one-hot tags before using the guard, nor invoke a decoded evaluation before restoring the parent zero.

The inverse is not an unconditional natural map: assigning all retained tags the value1 gives `s_i=4` in a nonterminal row or2 in the last row, so the restored t0 is negative. These supplied natural tuples have nonzero child output. The public `integer_pullback` exposes only the signed integer algebra; the natural `restore_zero` and `project_parent_zero` APIs require a complete zero before performing their maps.

The bijection is with the terminal parent. Its own existential projection to earlier pointer sources and normalized terminal-c slice is inherited with the same restrictions; no unique restoration of the older removed witnesses is claimed.

## Complete arithmetic accounting

For a nonterminal row the paid `active=t3+t4` register already exists and remains live in pointer-product membership. Forming

```
pair=t1+t2,
s=pair+active,
minus=s-1,
G=s*minus
```

costs3A+1M. It replaces the original five-addition tag chain. The leaf multiplication uses the new `minus` port instead of t0 without changing its gate count. In the last row `s=pair`, so its three-addition parent chain is replaced by2A+1M.

The certificate arithmetic consequently gains N guard multiplications and saves `2N−1` additions. In the complete finalizer the N original tag-sum squares disappear, cancelling those N multiplications. The number of accumulated terms remains8N, so its binary addition count is unchanged. No previously duplicated parent arithmetic is globally merged, and the existing cleanup flag retains its original separate meaning.

With `epsilon=1` for cleanup enabled and0 otherwise, the full formulas are

```
M = (3N^2+81N-46)/2,
A = (3N^2+(127-2epsilon)N-76)/2,
operations = 3N^2+(104-epsilon)N-61,
natural witnesses = 12N-5,
squared residuals = 7N,
unsquared integer guards = N.
```

All remaining supplied witness fields, the three ordinary input ports, and every gate are live. Representative cleaned complete sources are:

| N | Operations | M | A | Natural witnesses | Squared residuals + guards | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
|1|45|19|26|7|7+1|6|
|2|157|64|93|19|14+2|12|
|4|399|163|236|43|28+4|32|
|8|955|397|558|91|56+8|72|

The source guards the complete pinned terminal packets and supplies all sixteen forms, rather than accepting an arbitrary packet that happens to have the same counts.

## Exact degree and a real-domain boundary

The new guard has degree2. The leaf square after substitution has degree at most4. Neither changes the parent's leading terms. At N=1 the complete leading form remains

```
t2^2*b^4 + t1^2*(a+y)^4,
```

of exact degree6. At N>=2 the first row's third membership product has the nonzero leading form

```
(-1)^(N-1) * t[0,3]^N * (u0+v0)^(4(N-1)).
```

Its square has degree `10N−8`. The complete syntactic upper bound is the same, and the leading squares cannot cancel. The lower-degree added guards do not affect that argument. Thus the exact degree is6 at N=1 and `10N−8` for N>=2.

The checker additionally expands each entire emitted polynomial after setting all retained supplied ports to one indeterminate t. The highest coefficient is17 for N=1, and

```
8*2^(10(N-1)) + 2^(8(N-1))
```

for N>=2, confirming exact attainment on every saved full source.

The reverse direction also requires natural parent tags. For example, the signed N1 parent tuple `t0=-1,t1=0,t2=2,a=0,b=1,y=0,z=1,x=program=12,argument=0,output=1` is a complete integer zero: its tag sum is1, `F(0,1)=6`, and every output residual vanishes. Its projection has guard2 and child output2. Thus even though each new guard is nonnegative on all integers, there is no bijection with the parent's full signed zero set.

The zero equivalence is not a nonnegative-real statement. In the actual cleaned N1 child, set

```
t1=0, t2=1/2, a=b=y=z=0,
x=program=1, argument=output=0.
```

All coordinates are nonnegative rationals. The guard is `-1/4`, the leaf square is `1/4`, and all other terms vanish. The child output is zero, but its restored parent, with `t0=1/2`, has output `1/4`. These values are a direct algebraic counterexample and are rejected by the public natural-integer interface.

## Reproduction and scope of the checks

The receipt verifies all sixteen full source corrections,504 retained residual identities,72 zero tag rows,72 exact leaf sign identities and16 exact degrees. It contains128 independent signed numeric corrections, including32 rational cases, and66 genuine natural zero round trips covering all five evaluation rules and padded examples. It also checks sixteen off-zero negative pullbacks, the full rational boundary above,78 malformed or unauthorized-domain calls,14 defensive-copy cases, nine warmed source/receipt/proof pin failures, and optimized-interpreter rejection.

Every returned mutable field, including nested parent provenance, is isolated from subsequent builds. Public packets and integer assignments are checked with exact recursive types; bools, floats, fractions, surplus coordinates and altered full sources are rejected. `integer_pullback` permits signed integer coordinates but does not certify positivity or zeros. `restore_zero` and `project_parent_zero` validate the full natural source zero. The CLI reads authenticated parent JSON bytes without executing historical modules or suites.

```sh
python eager_tree_leaf_tag_projection.py --root ROOT \
  --expect eager_tree_leaf_tag_projection.json
```

ROOT contains the pinned terminal trio. Omitting it uses the helper's directory. `--output FILE` writes a deterministic receipt. The formulas and proofs explain the general schedule, while the guarded public source family is exactly the sixteen saved `N=1,...,8` forms. No unbounded array or fixed-arity universal claim follows from this finite arithmetic improvement.
