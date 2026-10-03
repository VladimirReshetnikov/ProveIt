# Independent review of the complete joint-affine U15 compiler

**PASS; no unresolved finding.** The complete [536 compiler](u15_packed_joint_affine536.py), its [saved source receipt](u15_packed_joint_affine536.json), and its [proof and API note](u15_packed_joint_affine536.md) agree. The ordinary polynomial costs **536=219M+317A**, with 87 positive witnesses and 31 comparisons. The raw half-tape polynomial costs **338=126M+212A**, with 51 positive witnesses and 11 comparisons. These are complete emitted arithmetic schedules; the separate universal 87-operation benchmark is unchanged.

The reviewed compiler source SHA-256 is
`eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330`.
Its immediate source dependencies are the frozen 561 compiler
`c4411ccfc9b62b1d8efe366686b99d4287031378b3acc0f5c07a1c10c52ef126`
and the affine rewrite helper
`3467d394885167260ca7f85f2b23033661de056bdba1959a45c9fc15ff516d2a`.
The [independent checker](review_u15_joint536.py) authenticates all three before importing the compiler. The authenticated compiler then checks its inherited source lineage, including on warm-cache access.

## Algebra and complete cost

For both interfaces, the checker reconstructs each of `J,S,Dir,W,WD,Qdev,Ndev` as an integer affine expression in all 29 edge hats. It compares the old and new coefficients to the actual literal rule table, including the constant offsets. This proves fourteen affine-vector identities without assuming Boolean edge digits, one-hotness, native typing, or a zero.

After replacing only these seven certified cut expressions by shared formal symbols, an independently interned expression DAG proves equality of every old and new comparison operand, all semantic, tag and computed-loader registers, and the complete sum-of-squares output. Thus the 536 and 561 polynomials agree on every integer tuple, and the same polynomial identity holds over the rationals and reals. The exact cut proof also establishes that no deleted private affine register escapes into a retained consumer.

The checker reconstructs each SOS finalizer literally, checks topological closure and unique names, proves every emitted gate reaches the output, and recounts all binary operations. Coefficient multiplications are charged. The counts are:

| Interface | Certificate | Finalizer | Complete polynomial |
|---|---:|---:|---:|
| Raw | 306=115M+191A | 32=11M+21A | 338=126M+212A |
| Ordinary | 444=188M+256A | 92=31M+61A | 536=219M+317A |

The helper changes the 124-gate affine block to 99 gates, saving exactly 25 additions. No multiplication or coordinate is removed by this composition step. The ordinary witness reduction belongs to the preceding 561 graph projection.

## Ancestor relation and API scope

The implementation correctly distinguishes immediate parent 561 from graph ancestor 611. `canonical_parent()` returns 561; `graph_ancestor()` returns 611. The original comparison map is renamed `ancestor_comparison_map`, and every retained child operand is updated to an actual 536 comparison. The computed-loader definitions remain unchanged. The complete canonical packet check includes this metadata and the source lineage.

For the 611 restoration map `R` and the two normalized tape residuals `tL,tR`, the composed identity is

```
F611(R(v)) = F536(v) + 3*(tL(v)^2+tR(v)^2).
```

The independent evaluation checker reconstructs all ancestor residuals directly: each removed defining residual is zero on the graph, each retained residual is unchanged except for the two literal factors of two, and the complete SOS difference is the displayed correction. This is not a claim that 536 and 611 are the same polynomial on unchanged coordinates. The 561 restoration positivity proof and graph bijection are documented and independently reviewed in the [561 review](review_u15_downstream561.md); this review read the full relevant source and checked its composition rather than claiming a new review of the entire historical universality proof.

The default raw interface accepts natural `L0,R0`, with all other supplied coordinates positive. The ordinary interface accepts positive coordinates; the inherited first-halt theorem is on the fixed effective valid-program slices. Signed evaluation allows exact integers only. Projection defaults to requiring the complete restoration graph. The explicit `require_graph=False` option merely forgets coordinates; the note accurately limits its meaning.

Exact Boolean switches, complete coordinate dictionaries and exact integer scalars are enforced. Canonical checks reject equal-valued float or Boolean substitutions. Public packet accessors return independent copies. The caches and module holders are private. Private-copy tests altered each of 586, 561 and 611 after warming the cache; every access rejected the changed source. Cold-import module isolation is inherited from the authenticated parent chain and was reviewed there; this bounded review does not claim protection against arbitrary hostile Python monkeypatching.

## Exact degree

The checker independently propagates formal upper degrees and evaluated homogeneous leading coefficients through each complete emitted polynomial. Fixed program parameters have degree zero; the other supplied coordinates have degree one. Both interfaces have upper degree 1936, and the complete degree-1936 part evaluates nonzero at both tested primes:

| Interface | Modulo 998244353 | Modulo 1000000007 |
|---|---:|---:|
| Raw | 617095362 | 460522416 |
| Ordinary | 823103080 | 803354412 |

The input leading values are `(i mod 5)+2` in the packet's ordered parameter/auxiliary list. Conservative dependency propagation shows these leading coefficients have no dependence on the fixed program numerals. A nonzero modular evaluation proves that the integer homogeneous polynomial is nonzero, so the degree is exactly 1936 on every fixed valid-program slice. This agrees with the inherited degree certificate and with the exact polynomial identity to 561. The ledger's conservative `exact_degree_claimed=False` is not mistaken for a refutation of the separately proved exact degree.

## Reproducible evidence

The [saved independent receipt](review_u15_joint536.json) records:

- 14 exact affine matrices and 2 complete residual/SOS DAG identities;
- 4 independent nonzero leading-coefficient certificates;
- 64 full parent/ancestor cases, including 32 signed cases and 1,344 retained scalar residual checks;
- 158 malformed-call rejections, including a float-coefficient mutation evaluated against 100-digit supplied integers;
- 6 defensive-copy checks and all 15 explicit nongraph projection cases;
- 3 warm-cache source-pin rejections on private copies.

A fresh independent run reproduced the entire saved JSON byte for byte. A separate fresh default author replay also passed and matched its complete saved receipt: 192 full parent/ancestor identities, 96 signed cases, 4,032 individual residual identities, 1,227 rejected malformed calls and 8 defensive-copy checks. Additional focused wrapper checks confirmed source authentication before execution, type-sensitive receipt comparison, rejection under optimized Python, and absence of machine-specific CLI defaults.

From this maintained directory, replay the portable independent checker with explicit paths:

```sh
python review_u15_joint536.py \
  --source u15_packed_joint_affine536.py \
  --root . \
  --expect review_u15_joint536.json \
  --output review_u15_joint536.fresh.json
python u15_packed_joint_affine536.py --root .
```

The checker uses no fixed temporary or workspace path. It requires assertions and authenticates the full 536 source plus the actual selected 561/586 dependency files before importing them. The compiler supplies deeper lineage authentication. These finite evaluations corroborate the exact source identities and public contracts; they do not enumerate the unbounded positive solution set or instantiate astronomical Pell witnesses.
