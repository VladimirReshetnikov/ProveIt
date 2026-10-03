# Independent review: existential congruence atoms

The existential reduction is sound for an already evaluated signed integer `L`, a fixed exact positive integer modulus `d`, and five natural witnesses. Dropping the two uniqueness constraints preserves the congruence truth value, with infinite witness fibres. The additional Boolean-square deletion is sound over every integer tuple and saves one further multiplication. It does not preserve real or rational zero sets.

This review reads the complete emitted source and accompanying proof. The [independent helper](review_presburger_congruence_existence15.py) authenticates the candidate, its canonical parent and the saved author receipt before loading or executing them. It uses its own ordered-DAG evaluator, expands the actual source, checks complete output identities, independently charges a full two-atom Boolean composition, and runs the original saved-receipt replay. Exact source hashes and counts are in the [independent receipt](review_presburger_congruence_existence15.json). No repository files were modified.

## Natural fibres and truth

Write the retained residuals as

```
A = L − d(q+−q−) − b(s+1),
C = b(s+1) + h − (d−1),
B = b(b−1).
```

Both finalizers force `A=C=B=0` on natural witnesses. Hence `b` is zero or one. The value `r=b(s+1)` is a natural number, and `C=0` says `r≤d−1`. The first row gives `L=d(q+−q−)+r`. The unique Euclidean division of signed `L` by positive `d` therefore fixes the quotient `q=q+−q−` and remainder `r=L mod d`.

If `r=0`, naturalness of `s` forces `b=0`; `s` is unrestricted. If `r>0`, then `b=1` and `s=r−1`. In both cases `h=d−1−r`. Every natural quotient pair of difference `q` is uniquely

```
q+ = max(q,0)+k, q− = max(−q,0)+k, k∈N.
```

This proves the full fibre formula for every signed input, including modulus one. The exported `1−b` is exactly the divisibility truth bit. Each fibre is infinite because `k` is arbitrary, whether or not `s` is also free. Setting `k=0` and, in a divisible fibre, `s=0` is the canonical retraction to the five-row parent. It preserves the public truth bit. It is not a canonical-witness-preserving replacement.

## Complete polynomial identities and costs

Let `P21` denote the canonical parent's complete polynomial. The two candidates are

```
P15 = A²+C²+B²,
P14 = A²+C²+B.
```

The exact all-value identities are

```
P21 − P15 = (q+q−)² + ((1−b)s)²,
P15 − P14 = B²−B.
```

The helper checks these against every emitted gate and residual, rather than treating the displayed formulas as the implementation. For integer `b`, `B=b(b−1)≥0`; thus `A²+C²+B=0` if and only if `A=C=B=0`. This proves the complete integer zero-set equivalence between the 14- and 15-operation polynomials, including signed internal coordinates. Congruence truth itself still needs the natural witness domain.

| Complete standalone atom | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Canonical five-row parent | 9 | 12 | 21 |
| Three-row sum of squares | 6 | 9 | 15 |
| Two squares plus Boolean product | 5 | 9 | 14 |

The three residuals cost `3M+7A`. Three squares plus two additions give the 15-operation schedule. Reusing the computed Boolean product directly removes exactly one multiplication. Each schedule pays multiplication by the fixed modulus, even when `d=1`; no optimality is asserted. Every charged gate is live, and every declared input occurs in the complete output. Both new polynomials have exact degree four: the coefficient of `b²s²` is two, independently of `d`.

These atom counts exclude evaluation of `L`, formation or use of the exported expression `1−b`, other Boolean gates and the surrounding accumulation. They must all be paid in a larger compiler.

## Composition and its limits

With disjoint private atom coordinates, a full existential Boolean compiler may replace each canonical atom. A canonical zero stays a new zero. Conversely the natural fibre proof fixes every Boolean atom value at a new zero. Retracting each atom's private coordinates to the canonical representative leaves the Boolean gates and acceptance guard unchanged, and supplies a canonical parent zero. This proves acceptance equivalence for the full formula.

The review constructs the complete two-atom NAND source, including both atom polynomials, the two truth expressions, the NAND relation, a final `output=1` guard, their squares and all final additions. Its sum-of-squares-atom version costs `15M+26A=41`; the canonical-parent version costs `21M+32A=53`. Replacing both atoms by their 14-operation form gives `13M+26A=39`. These are small fully paid examples, not a universal equation record. The source has eleven natural auxiliary coordinates and eight zero conditions, with the two signed affine inputs already supplied.

For a fixed quantifier-free Presburger formula, the stated witness count stays `2I+5C+G` and residual count drops to `2I+3C+G+1`. The interpretation of `I,C,G`, input-affine evaluation and outer finalizer remain those of the parent compiler. Presburger elimination is not supplied by this atom. No canonical/finite-fibre theorem, general reachability compiler, fixed-arity universal representation or improvement of the maintained universal bound follows from these local counts.

The private-coordinate condition is necessary. At `d=1,L=0`, the new natural witness `(q+,q−,b,s,h)=(1,1,0,0,0)` vanishes and satisfies an additional test `q+q−=1`. The canonical parent can never satisfy that test because its own row forces `q+q−=0`. Thus exporting private quotient coordinates to an arbitrary outer predicate can change acceptance. The documented truth-only interface prevents this example.

Two explicit domain boundaries also matter. For `d=2,L=0`, the signed tuple `(0,0,1,−1,1)` makes all three residuals zero but gives the wrong divisibility truth. For `d=2,L=1`, the nonnegative rational tuple `(1/2,0,0,0,1)` does the same. These are not natural-domain counterexamples.

Finally, the Boolean-square deletion fails over nonnegative rationals: with `d=2,L=1` and `(q+,q−,b,s,h)=(0,0,1/2,0,1/2)`, the three residuals are `(1/2,0,−1/4)`. Consequently `P14=0` while `P15=5/16`. This supports the explicit integer-only boundary of that second reduction.

## Executable scope

The fresh pinned author replay passes all **56,593** saved checks. The independent helper checks **22,464 unfiltered natural tuples per finalizer**, 120 large independently constructed fibres per finalizer, 507 complete NAND truth cases per finalizer, 720 signed complete-polynomial correction/zero-equivalence cases, and 100 exact public-domain rejection calls. Four fixed-modulus specializations, including one and a 106-digit value, have full symbolic source/correction and exact-degree checks.

The independent natural census varies every coordinate independently in its declared box, including `h`, and uses no equation to prefilter candidates. Large signed inputs independently exercise nonzero common quotient shifts and divisible inactive slacks. Symbolic expansion checks all emitted residuals and complete correction identities. The full composed-source identity is checked symbolically as well as on finite truth cases. Exact-domain rejection tests cover Boolean, float, rational and integer-subclass impostors, negative natural coordinates, missing/surplus keys and invalid moduli. Mutating a returned build does not affect a later build.

The unbounded conclusions are established by the fibre and nonnegativity arguments above. The finite checks supplement them. The helper has no fixed temporary-directory dependency and does not expose imported modules through `sys.modules`.

```
python review_presburger_congruence_existence15.py \
  --root /path/to/native-stream-queue \
  --expect review_presburger_congruence_existence15.json
```

The exact pins and final replay counts are recorded in the receipt. The review retains the distinction between all-value correction identities, integer zero-set equivalence of the two new finalizers, and natural-domain existential acceptance equivalence with the canonical parent.

The candidate source is frozen at SHA-256 `18d66ff01e7b13b0aecd9b9c1255d4eb199d8a85df7798c96ef4c6b5df438525`, its author receipt at `d244625e6e35a57742b48844cc59b66ddfa7132b6a08fbd9e843a11bc4ebd589`, and its canonical parent at `f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc`. No unresolved proof, count, implementation or scope defect was found in this bounded review.
