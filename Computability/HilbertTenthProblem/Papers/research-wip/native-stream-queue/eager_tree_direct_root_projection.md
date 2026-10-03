# Direct root inputs for finite eager Tree certificates

The complete cleaned eight-row source uses **946=394M+552A operations**, **88 natural existential witnesses**, and exact degree **72**. The one-row source uses **36=16M+20A**, four natural witnesses, and exact degree6. Every saved source improves the [leaf-tag parent](eager_tree_leaf_tag_projection.md) by exactly **9 operations=3M+6A** and three witnesses.

The ordinary inputs `program`, `argument` and `output` now serve directly as the first row's fields. They retain their original meanings and natural domains, including zero. This is a separate finite-source projection, with external `N=1,...,8`; it does not eliminate the size parameter or give a new input decoder or fixed-arity universal representation.

The [helper](eager_tree_direct_root_projection.py) and [receipt](eager_tree_direct_root_projection.json) emit all sixteen complete circuits, one for each size and each setting of the existing optional `0+b` cleanup. Every public call authenticates this parent trio before reading its JSON:

| Parent artifact | SHA-256 |
|---|---|
| Python | `e491a2dd852fca307d1c5f7138b078a0b815a0cea271ef05000cf001be1f6015` |
| JSON | `1f786cd77987db5892ac40b4329f7bce1b6ad3ff26aa7cf15e0a25dde21114eb` |
| Markdown | `9f6e8d07accec6eb33ee402427e7fd795ff91487174fc47248653e855447ea8f` |

No parent Python module or historical author suite executes.

## Actual graph substitution

The parent supplies root fields `r0_x,r0_y,r0_z` and includes three residuals

```
r0_x-program,
r0_y-argument,
r0_z-output.
```

The emitter identifies these exact subtraction rows, checks that each is a unique ordinary residual squared once in the mixed finalizer, and verifies that none has a certificate consumer. It replaces every use of the root fields by the corresponding ordinary input, removes those three supplied coordinates and binding rows, and drops their three finalizer squares. No other certificate gate is removed, folded, merged or reordered. The retained finalizer terms preserve their parent order.

For a child assignment r, let R(r) restore

```
r0_x=program,
r0_y=argument,
r0_z=output,
```

and copy all other supplied coordinates. Then the entire polynomial satisfies

```
F_child(r)=F_leaf_tag_parent(R(r)).
```

This is an all-value polynomial graph identity over integers or rationals. The three restored binding residuals are identically zero; every remaining residual and guard agrees. The checker verifies both full polynomial DAGs directly with constant, zero, unit and identical-subtraction simplifications. It supplies no residual cut or assumed zero to that comparison.

Unlike the preceding tag restoration, R preserves natural values unconditionally: it only copies three already natural ordinary inputs. It also takes every natural child zero to a natural parent zero.

Conversely, at a natural parent zero, all finalizer terms are nonnegative. Its ordinary residuals are squared, and each retained tag guard is `s(s-1)` at an integer s. Consequently the three binding squares vanish individually, forcing the three root fields to equal their ordinary inputs. Projecting them away gives a child zero by the graph identity. Restoring it recovers that exact parent tuple. Thus the maps are inverse on the **full natural zero sets of the immediate leaf-tag parent and this child**.

The conclusion does not assume the Tree evaluation theorem before restoring the parent. Earlier restrictions on maps back to pointer or circulation sources remain unchanged. In particular this step does not make the earlier existential projections bijective or extend their integer semantics to real witnesses.

## Every removed gate is charged

The certificate loses precisely three binary subtractions. The finalizer loses three squares and three binary accumulator additions. Thus the saving is exactly3M+6A, including the finalizer. The optional cleanup remains a separate inherited choice; this projection performs no additional common-subexpression elimination.

The finalizer remains mixed: it has **N unsquared integer guards and7N−3 squared residuals**, or8N−3 nonnegative terms on integer assignments. It is not advertised as an SOS of8N−3 residuals. There is no new equation on the ordinary inputs.

For cleanup flag `epsilon` equal to1 when enabled and0 otherwise, the complete formulas are

```
M = (3N^2+81N-52)/2,
A = (3N^2+(127-2epsilon)N-88)/2,
operations = 3N^2+(104-epsilon)N-70,
natural existential witnesses = 12N-8,
squared residuals = 7N-3,
unsquared integer guards = N.
```

With cleanup enabled, the operation formula is `3N^2+103N-70`. All remaining supplied coordinates, all three ordinary inputs and every emitted gate are live ancestors of the complete output.

| N | Clean operations | M | A | Natural witnesses | Squares + guards | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
|1|36|16|20|4|4+1|6|
|2|148|61|87|16|11+2|12|
|4|390|160|230|40|25+4|32|
|8|946|394|552|88|53+8|72|

The three ordinary inputs are not counted as existential witnesses. The packet explicitly distinguishes the certificate ledger from the complete polynomial ledger.

## Exact degree and domain limits

The alias substitution replaces degree-one coordinates by degree-one ordinary inputs, so the parent's full degree upper bound is unchanged. To certify attainment, specialize every retained supplied port, including the ordinary inputs, to the same indeterminate t. Restoring the three root fields then gives exactly the parent's all-port diagonal specialization. Its binding residuals are already zero on that diagonal.

The checker expands the entire parent and child univariate polynomials and verifies equality of all coefficients in every saved form. The leading coefficient is17 at N=1 and

```
8*2^(10(N-1))+2^(8(N-1))
```

at N>=2. It is positive. Therefore the exact total degree remains6 at N=1 and `10N−8` at N>=2, not merely a propagated upper bound. At N=1 the leading form can also be written directly as

```
t2^2*b^4+t1^2*(a+argument)^4.
```

The parent's real-witness limitation survives unchanged. In the actual N1 child, set `program=1,argument=output=0,t1=0,t2=1/2,a=b=0`. The guard is `-1/4`, the leaf square is `1/4`, and all other terms vanish. The child and restored immediate parent both have output zero, although program1 applied to0 actually produces2. This is a nonnegative rational fixture, not a natural-integer witness; the public integer APIs reject it. The new graph identity does not claim that fractional tags are a valid Tree evaluation.

## Public maps and verification

`build`, `rewrite`, `checked`, `canonical_parent` and `polynomial_source` guard the full canonical source packets and exact saved size/cleanup types. `evaluate` and `restore_assignment` accept exact integer assignments with precisely the required keys. Their default domain is natural, and `signed=True` is available for integer algebra. `restore_assignment` requires no zero assumption. `project_parent_zero` requires a complete natural parent zero, then checks the root equalities and the full inverse. No unrestricted projection of off-zero parent assignments is presented as an inverse.

Returned sources, assignments and nested provenance are copied. Every call reauthenticates the source, receipt and proof-note bytes, including after a successful earlier call. A mismatch is rejected rather than resolved by a historical import or fallback.

The receipt records16 complete graph identities,6,588 retained certificate-gate identities,456 retained ordinary-residual identities,72 unchanged guards,48 zero binding rows and16 exact degree checks. It additionally checks128 complete numeric identities, including32 rational cases;48 unconditional natural restorations; and66 genuine natural zero round trips covering all five evaluation rules and padded examples. The inherited rational boundary is recorded separately. Interface checks cover80 rejected malformed or unauthorized-domain calls,15 defensive-copy cases, nine warmed pin failures and optimized-interpreter rejection.

Replay from any directory with the pinned leaf-tag trio under ROOT:

```sh
python eager_tree_direct_root_projection.py --root ROOT \
  --expect eager_tree_direct_root_projection.json
```

Omitting ROOT uses the helper's directory. `--output FILE` writes a deterministic receipt; saved comparisons use exact recursive types. The formulas describe the uniform finite schedule, while the public emitter deliberately supports only the sixteen authenticated `N=1,...,8` forms. All frozen predecessors remain untouched.
