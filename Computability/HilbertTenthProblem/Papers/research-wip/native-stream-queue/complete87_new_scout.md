# Auxiliary-ordinate translations: a bounded complete87 scout

No operation saving was found. This family changes the auxiliary Pell ordinate to its sum or difference with the other auxiliary argument. Both changes have a complete positive-integer zero-set bijection to the source-pinned asymmetric universal87 polynomial, but the least expensive resulting source costs **88=48M+40A**, with exact degree165. It is dominated by the established88/125 source. The universal87/169 bound is unchanged.

This is a new coordinate family, separate from the previously published main/input joint-norm compositions, discriminant shears and strong-norm compositions. Those reports were read first. Their source rewrites retain the old supplied ordinate; this scout replaces that coordinate while retaining all ordinary-input, packed-mask, ratio, strong-norm and finalizer obligations.

## Exact coordinate maps and full positive-zero bijections

Use the actual complete parent quantities

```
a=XY+Y, Delta=(a+2)^2−1,
c=(eta+zeta)Y+eta, t=i*c^2,
V=o*f−c, K=Delta^2*t^2,
Ns=f^2−Delta*t^2,
Na=K*V^2−(K−1)*y^2.
```

The source registers for `V,K` are `aux_u_rhs,R16`. Only `Na` depends on the supplied coordinate `y=y_aux`. The other seven factors and the final product-minus-one are unchanged.

For either fixed sign `epsilon∈{−1,1}`, replace the supplied positive `y` by a supplied positive `e` and set

```
y_old=e+epsilon*V,
e_new=y_old−epsilon*V.
```

These are inverse polynomial coordinate maps over the integers, since `V` is independent of `y`. The exact transformed auxiliary factor is

```
Na_epsilon=V^2−(K−1)*e*(e+2epsilon*V).
```

Consequently the entire emitted polynomial satisfies

```
F_epsilon(all other coordinates,e)
  = F_parent(all other coordinates,e+epsilon*V)
```

on every integer tuple. This is a coordinate identity, not equality of the two polynomials on the same supplied tuple. No premise that another factor has already vanished is used to prove this identity.

The restriction to positive integer zeros also gives a bijection, but needs a proof rather than an assertion that the maps preserve the entire positive orthant:

1. On either complete product-minus-one zero, every factor is an integer unit. Because `Delta=(a+2)^2−1` is0 or3 modulo4, `Ns` cannot be−1. Thus `Ns=1`.
2. All unchanged supplied coordinates are positive, so `a≥1`, `Delta≥8`, `c≥1`, `i≥1`. Therefore `f²=1+Delta*i²*c⁴>4c²`, whence `f>2c` and `V=o*f−c>c≥1`.
3. `K=(Delta*t)²` is0 or1 modulo4. For any integer restored `y`, `Na=K V²−(K−1)y²` is a square modulo4 and cannot be−1. Hence the auxiliary factor is+1. Since `K>1`,

   `(K−1)(y²−V²)=V²−1>0`,

   so `|y|>V`.
4. Starting with an old positive zero, `y>V` and both `e=y−V` and `e=y+V` are positive. Starting with a new positive zero, the plus restoration `y=e+V` is positive directly. The minus restoration `y=e−V` exceeds `−V`; together with `|y|>V` this forces `y>V>0`.

These maps are inverse on the **full supplied positive zero sets**, preserving the other eighteen witness coordinates and the ordinary positive input `x`. No canonical Pell-subfamily restriction or refreshed auxiliary witness is required. The inherited universal compiler contract therefore transfers exactly. There is no claim that these maps carry arbitrary positive off-zero assignments into the positive orthant, nor that the unit argument holds over the reals.

## Fully paid finite family

For each of the two signs, the helper emits six literal evaluations of the transformed factor. Here `y=e+epsilon V` is a computed register when it occurs; it is never a free source input.

| Template | Auxiliary expression | Complete operations | M | A |
|---|---|---:|---:|---:|
|Restore|`K*(V²−y²)+y²`|88|48|40|
|Shifted square|`y²−K*e*(e+2epsilon V)`|89|48|41|
|Factored gap|`V²−(K−1)*e*(e+2epsilon V)`|89|48|41|
|Folded coefficient|`V²+(e−K*e)*(e+2epsilon V)`|89|48|41|
|Expanded cross|`V²+(1−K)*(e²+epsilon*2eV)`|90|49|41|
|Difference product|`y²−K*(y−V)*(y+V)`|89|48|41|

The counts are identical for both signs. This is an exhaustive census of these twelve declared schedules only. It is not a lower bound over arbitrary circuits, arbitrary coordinate substitutions or arbitrary norm rewrites.

Every schedule is applied to the actual complete87 source, followed by exact commutative common-subexpression reuse, literal constant folding, zero/one identities and pruning to the final polynomial. That same pass leaves the parent at87=48M+39A. Every surviving addition, subtraction, multiplication, square and nontrivial fixed-coefficient multiplication counts one, including all seven final factor multiplications and the final subtraction of1. Every emitted gate is live; every candidate has exactly the parent's free-coordinate interface, including its19 supplied witness slots, ordinary input and fixed compiler numeral ports. The `y_aux` slot denotes the new `e` coordinate in these twelve sources.

The cheapest mode adds one computation of `e±V` to the old five-gate auxiliary evaluator. Algebraically exposing the canceled `V²` term does not help the arithmetic count: it needs the coefficient `K−1` and the doubling/offset of `V`. The fully paid gap/Horner alternatives cost one more operation than restoration. None deletes the strong relation or treats `K−1`, a doubled register or a restored ordinate as free.

## Exact degree, distinct from the operation result

The coordinate change lowers the degree from169 to165, but requires one extra operation. The result is still worse than the already maintained88/125 tradeoff.

Let `Q0=(B−1)J`, `k0=eta+zeta`, `gamma0=rho+sigma`, and

```
a0=w*s*Q0^4, c0=k0*s*Q0^3,
Ctop=Q0−F−Z−alpha−2d*x.
```

The parent's exact leading-form proof gives `deg(a)=6`, `deg(c)=5`. Since `V=o*f−c`, its leading form is **`−c0`**, not `o*f`. Further,

```
K0=i²*a0^4*c0^4,
deg(K)=46.
```

In the transformed factor the leading term is

```
−2epsilon*K0*e*Vtop = 2epsilon*K0*e*c0,
```

of degree52. It is nonzero. The parent's auxiliary factor instead had degree56. All other factors remain independent of `y` and retain their proved degrees. In inherited order, the eight degrees are therefore

```
12,18,32,52,7,3,34,7,
```

with sum165. The complete leading homogeneous form is

```
64epsilon*Q0^98*h²*gamma0*delta²*i^4*k0^11
  *w^17*s^27*e*Ctop*(2g−k0).
```

It is nonzero for every admissible fixed compiler slice (`B>1`); the fixed mask and bridge constants do not enter the leading coefficient. Thus165 is an exact degree, not a propagated syntactic bound or a finite-fixture conjecture. The six templates at each sign are exact polynomials, so the proof covers all twelve complete schedules. Two modular affine-line expansions for each sign independently evaluate every coefficient of the complete emitted polynomial, attaining degree165 and every listed factor degree.

## Reproducible evidence and limits

`complete87_new_scout.py` reads the literal normalized source from the authenticated `complete75_asymmetric_scale_tradeoffs.json`. It also pins the asymmetric compiler, normalized-strong parent, coupled parent and positive-elimination source before reading the packet. No parent module is imported and no archive or repository file is written. The JSON contains all twelve complete sources and their M/A ledgers.

The deterministic audit performs12 exact symbolic checks of the actual emitted local factor expressions;96 expression-DAG identities for the seven unchanged factors plus each complete finalizer after the proved auxiliary cut;1,152 full polynomial/factor coordinate identities and inverse roundtrips, including576 signed cases;320 modulo-four checks of the two protected norm signs; and24 small auxiliary Pell-component fixtures with both positive coordinate maps. These component fixtures are not complete compiled-program zeros. The four full modular polynomial expansions supplement the uniform leading-form proof. No astronomical complete universal Pell witness is materialized.

Replay using Python with SymPy, for example the research environment:

```sh
/tmp/diophantine-research-venv/bin/python /path/to/complete87_new_scout.py \
  --root /path/to/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect /path/to/complete87_new_scout.json
```

`--output` writes a fresh receipt; `--expect` compares recursively with exact Python/JSON types. The literal source can be inspected without importing historical compiler modules. Writer and fresh replay pass. This is a scoped negative operation result and a dominated degree tradeoff, not a proposed new universal arithmetic frontier.
