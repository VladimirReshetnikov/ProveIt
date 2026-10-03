# Existential congruence atoms in fifteen or fourteen operations

When only existential truth is needed, the [canonical five-witness atom](presburger_congruence_five.md) can omit its two uniqueness constraints. The complete sum of squares uses **five natural witnesses, three quadratic residuals and 15 = 6M + 9A operations**. Keeping the Boolean product unsquared gives the same integer zero set in **14 = 5M + 9A operations**. Both have infinitely many witnesses for every input. They are unsuitable as replacements in a theorem requiring canonical, finite or unique witness fibers.

For a fixed integer modulus `d≥1` and an already evaluated signed integer affine input `L`, take natural witnesses `(q+,q−,b,s,h)` and residuals

```
L − d(q+−q−) − b(s+1),
b(s+1) + h − (d−1),
b(b−1).
```

The exported truth expression is `1−b`. Only this expression may be read by the surrounding Boolean compiler; the other coordinates must be private to this atom. The [source](presburger_congruence_existence15.py) emits all fifteen binary arithmetic gates, and the [receipt](presburger_congruence_existence15.json) includes that full schedule.

## Soundness, completeness and the exact fibers

At a natural zero the Boolean row gives `b∈{0,1}`. Put `r=b(s+1)`. Naturalness and the second row give `0≤r≤d−1`, while the first row gives `L=d(q+−q−)+r`. The uniqueness of Euclidean division over the integers fixes `q=q+−q−` and `r=L mod d`. If r is zero then b is zero; if r is positive then b is one and `s=r−1`. Thus every zero has exactly the correct truth output, including negative L and modulus one.

Conversely write `(q,r)=divmod(L,d)`. All natural zeros, without omission, have

```
q+ = max(q,0)+k,   q− = max(−q,0)+k,   k∈N,
b  = [r>0],       h  = d−1−r,
s  = r−1 when r>0, and any natural number when r=0.
```

Indeed every natural pair with difference q has exactly that common-shift form. This describes all fibers and proves existence for every signed input. Even when r is positive, the free k gives infinitely many witnesses. Setting k=0 and, when r=0, s=0 recovers the parent's canonical witness without changing the truth output.

The parent adds the two residuals `q+q−` and `(1−b)s`. For every signed tuple its complete atom polynomial satisfies the exact difference identity

```
P_canonical − P_existential = (q+q−)² + ((1−b)s)².
```

The two polynomials are not identical and their natural zero sets are not in bijection on unchanged coordinates. The canonical section above is a zero-set retraction that preserves only the exported Boolean value. Do not substitute this construction into an argument that counts canonical certificates.

## Composition and fully charged arithmetic

For an ordinary existential quantifier-free Presburger compiler with disjoint private atom coordinates, replacing canonical congruence atoms preserves acceptance. A parent zero remains a new zero. Conversely each new zero has the same uniquely determined Boolean atom outputs; canonically replacing each atom's private witnesses leaves every Boolean gate and the output guard unchanged and gives a parent zero. This is a direct argument for the whole existential formula, rather than an inference from a favorable internal row count.

In the notation of the parent compiler, witness count remains `2I+5C+G`, while residual count falls from `2I+5C+G+1` to **`2I+3C+G+1`**. The uniqueness conclusion does not transfer. This applies only after effective Presburger elimination has produced the fixed formula; elimination itself and general CA reachability are not provided by this gadget.

The literal schedule shares `bs=b·s` and `r=bs+b`. It computes `q=q+−q−`, multiplies it by d, forms the quotient and bound residuals, and computes `b(b−1)`. These three residuals cost `3M+7A`. Their three squares and two final additions cost `3M+2A`. The total is **6M+9A=15**, versus the parent's displayed `9M+12A=21` schedule. Multiplication by the fixed modulus is paid even for d=1; this is a uniform schedule comparison, not an arithmetic optimum. All fifteen emitted gates contribute to the output.

The standalone atom excludes evaluation of L, use of the output expression `1−b`, other atoms, Boolean gates, and the complete outer final sum. These must still be charged in a full compiler. One cannot infer a universal-equation bound by multiplying fifteen by an atom count. No maintained 87-operation universal bound is changed.

## Fourteen operations with an unsquared Boolean product

Let A and C be the first two residuals and let `B=b(b−1)`. For every integer b, `B≥0`, with equality exactly when b is zero or one. Consequently

```
A²+C²+B = 0  iff  A=C=B=0  iff  A²+C²+B² = 0
```

on every integer tuple. This stage preserves the full integer zero set of the fifteen-gate version on the same coordinates, so it also preserves its natural fibers and the existential composition proof. Its polynomial values differ by `B²−B`. No all-value polynomial identity is claimed. This zero-equivalence stage is separate from the earlier removal of canonical-witness constraints.

The fourteen-gate schedule removes only the multiplication that squares B. Every other operation and both final additions remain. Thus the complete count is **5M+9A=14**, with two squared quadratic residuals and one unsquared quadratic product. The exact degree is still four: the coefficient of `b²s²` is two. The compiler residual count remains three per congruence atom, but its final polynomial is now a sum of squares and integer-nonnegative products. Summing such atom polynomials with the other squares preserves conjunction over natural witnesses.

This is an integer-domain argument. At `d=1,L=0,q+=0,q−=1/2,b=1/2,s=h=0`, the mixed polynomial is zero, while the fifteen-gate sum of squares is `5/16`. Thus the same-coordinate real zero sets differ even with an integer input and nonnegative real witnesses.

The default `build(d)` and `evaluate(d,inputs)` use the fifteen-gate SOS. Pass the exact flag `square_boolean=False` for the fourteen-gate version. No constant specialization or circuit minimum is claimed.

## Verification

The checker authenticates the canonical parent's exact source bytes before compiling them. It verifies complete symbolic residuals, exact degree four and both full difference identities, including modulus one and a fifty-digit modulus. Bounded complete-fiber enumerations check both schedules against the independent Euclidean characterization, including non-Boolean candidates and noncanonical quotient shifts. Large signed inputs, explicitly divisible fibers and a complete two-atom NAND/output-guard example exercise the acceptance-preserving composition. The real-domain counterexample and exact mode guards are checked. Exact-type input checks reject Booleans and floats. These tests accompany, rather than replace, the unbounded fiber proof above.

```
python presburger_congruence_existence15.py --expect presburger_congruence_existence15.json
```

The checker uses SymPy for symbolic identities. Its returned source and parent hashes bind the saved receipt to this implementation. All public domain checks use explicit exceptions.

The [independent review](review_presburger_congruence_existence15.md) verifies both literal gate lists and full difference identities, enumerates 22,464 unfiltered natural tuples per finalizer, and supplies separate signed/rational and private-coordinate counterexamples. Its complete emitted two-atom NAND example pays the truth expressions, Boolean relation, acceptance guard and final accumulation: 53 operations with the canonical atoms, 41 with the fifteen-gate atoms, and 39 with the fourteen-gate atoms. Root reproduced that receipt byte for byte and separately matched the author's 56,593-check receipt with assertions disabled.
