# Independent review: 88/30 to retained free-J endpoint source audit

This bounded review pins the author audit and all 17 source/graph inputs in
`pins.json`. The author receipt reproduces. No Lean code, provider replay, or
axiom report has been run; these checks do not establish the final endpoint,
any PDF or JSON semantics in Lean, or a consistency sentence equivalence.

The three pinned graphs use the same witness order and ports. The author
checks their source literal rows and the exact row differences, including
`(V+u)²−V² = u*((V+u)+V)` for the retained product graph. Independently,
our checker evaluates each entire graph at 240 signed assignments and checks
all common named fields and the three displayed outputs. This is finite
corroboration of the author's exact algebra, not a substitute for formal graph
binding.

For `A=A0`, `B=A1`, `F=Fa`, and `S=Fs`, the respective outputs are
`A²+B²+(F−1)²+(S−1)²`, `A²+B²+(FS−1)²`, and
`SF(1+A)(1+B)−1`. A four-square zero yields a paired zero, and a paired zero
yields a product zero in an ordered difference ring. Conversely, the retained
`FreeJ13.factor_units p v` declaration explicitly assumes the product zero and
concludes all four graph-specific factors are positive units; `unit_iff_one`
converts those signed pairs into ring equalities. These equalities recover
the four-square zero. The abstract assignment `A=B=0, F=S=−1` separates the
paired and four-square expressions; it is not a demonstrated graph zero. The
checker tests 2,401 small abstract factor assignments without treating them as
a proof or as actual graph witnesses.

The source directions in the 88/30 model draft and its 88/46 parent match
the stated equivalences and preserve the same `p` and `v`. The local proposed
`zero_iff` statements take arbitrary integer ports and model-natural valuations;
their source signatures do not require positivity. The retained
`FreeJ13Halt.positive_model_iff` specializes to `CompactSymbolicModelIff.p`
and requires every valuation coordinate positive. That condition enters when
the two proposed local maps are composed with the halting endpoint. The
88/30 native client states the internal biconditional between `nativeNoZero`
of its positive shift and negated `mappedNativeRefutation embedding`; it does
not alone identify a physical displayed equation or a separately selected
ZFC consistency encoding.

The 88 model and endpoint proof scripts remain unelaborated; the retained
87 endpoint has only its separately documented author-side provenance. An
actual coherent dependency/provider replay, translation/axiom checks, fixed
bytes and physical-file binding are independent obligations. No concrete
mathematical or premise-direction mismatch was found in this bounded review.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive88-freej-endpoint-independent/check.py | cmp - reviews/ordinary13-positive88-freej-endpoint-independent/receipt.json
```
