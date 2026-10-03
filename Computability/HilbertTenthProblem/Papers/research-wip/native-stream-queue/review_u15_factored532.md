# Independent review of the factored history-index compiler

**PASS; no unresolved finding.** The complete [532 compiler](u15_packed_factored_index532.py), [source receipt](u15_packed_factored_index532.json), and [proof note](u15_packed_factored_index532.md) agree. The change saves exactly four additions from both complete interfaces and preserves their supplied coordinates and full polynomials on every integer tuple. The ordinary count is **532=219M+313A**; the raw count is **334=126M+208A**.

Reviewed source SHA-256:
`ed716945027275990e5aff1f7d4d180533af3e44b2a8c1862c3db4a7db7cf954`.
The [portable independent checker](review_u15_factored532.py) authenticates that full source, its actual selected 536 parent, and the separately reviewed binary affine helper before executing them. The parent and helper pins are recorded in the [independent receipt](review_u15_factored532.json).

## Exact algebra and full source

With `a=scaled_A`, `A=a+12`, `B=padded_B`, `Z=F3`, the original index is

```
(q-A-B+Z-1) + q*(A-Z) + q^2*(B-Z) + q^3*Z.
```

The replacement is

```
(q-1)*(a+13+(q+1)*(B+(q-1)*Z)).
```

Both have exactly the same ten nonzero monomials in the four independent variables `(a,q,B,Z)`. The independent checker extracts each actual local source closure from the emitted packets, stopping at these four inputs, expands both closures coefficientwise, and compares them with the explicitly derived ten-term polynomial. The old closure has twelve rows; the new closure has eight. Both have three multiplications. The constant shift 12 to 13 reuses the old addition; it does not introduce an unpaid `A+1` gate.

Every row outside that local closure is literally unchanged, up to topological order. An independently interned complete DAG proves that all four cut-input expressions also remain unchanged, then proves equality of every comparison operand, named semantic/tag/computed-loader register, and complete SOS output after replacing only the proved packed-index expression by a common formal symbol. This establishes the full polynomial identity, without positivity, norm, typing, or zero assumptions. The `native__bs_packed` output name is preserved.

The checker reconstructs the literal finalizers, validates topological closure and unique names, and proves every emitted gate reaches the output. Independently recounted costs are:

| Interface | Certificate | Finalizer | Complete polynomial | Positive witnesses / comparisons |
|---|---:|---:|---:|---:|
| Raw |302=115M+187A|32=11M+21A|334=126M+208A|51 / 11|
| Ordinary |440=188M+252A|92=31M+61A|532=219M+313A|87 / 31|

## Metadata, domain and public guards

The three truth fields are no longer live source registers or supplied coordinates. Their former definitions, including the old padded-A addition, appear only in the explicitly named `proof_only_truth_reconstruction`. Direct evaluation of those six historical rows reproduces the parent's old intermediate values in all 48 bounded full-tuple checks, including 24 signed cases.

The inherited `removed_comparisons` descriptor also mentions a removed padded-A register, as it already did in the parent. It is a record of previously removed constraints, not an active comparison list. The independent metadata scan excludes exactly these two historical descriptors and confirms that no removed private register appears anywhere else in the packet. The active comparison list, semantic registers and computed loader fields all resolve to the current complete source. The immediate parent descriptor correctly names 536; historical ancestor data retain their inherited scope.

The complete positive-zero and unbounded first-halt relation therefore transfer by identity from the reviewed 536 parent. Raw `L0,R0` remain natural; the remaining raw coordinates and ordinary supplied coordinates are positive. The effective valid-program-slice qualification is retained. This review does not independently redo the whole earlier universality construction or extend its claim to arbitrary program tuples.

Public switches use exact Booleans, assignments require exact integer scalars and complete coordinate keys, and full packets are matched type-sensitively. A changed float 13.0 coefficient is rejected before evaluation even against 100-digit supplied integers. Packet and source accessors return independent copies. Two private-copy tests warmed the cache, then changed 536 or 561 source bytes; the subsequent public build rejected each changed dependency. The source includes the required optimized-Python rejection; inherited deeper source authentication remains active.

## Degree and independent composition

Exact degree 1936 transfers from the identical parent polynomial. The independent checker also propagates the new source's formal degree and evaluated homogeneous leading coefficient modulo 998244353 and 1000000007. Both interfaces have upper degree 1936 and nonzero leading coefficients. Conservative dependency propagation shows that those coefficients are independent of the fixed program parameters. This confirms exact degree on the inherited fixed valid-program slices. The conservative ledger flag `exact_degree_claimed=False` remains distinct from this mathematical certificate.

The separately frozen [binary affine rewrite](u15_joint_binary_affine_rewrite.md) accepts both actual 532 packets under its exact 99-row boundary contract. Its complete-DAG proof composes with the index factorization without any row-name or metadata exception. The resulting full sources cost:

| Interface | Composed certificate | Composed polynomial |
|---|---:|---:|
| Raw |293=107M+186A|**325=118M+207A**|
| Ordinary |431=180M+251A|**523=211M+312A**|

These composition counts and their exact affine proofs are recorded in the independent receipt. They are demonstrated arithmetic compositions, not a separate maintained canonical compiler API. Both retain the identical full polynomial, so no new semantic proof obligation is introduced by their arithmetic combination. The universal 87-operation benchmark is unchanged.

## Replay evidence and limits

The saved independent receipt records:

- Two exact local polynomial identities and two complete residual/SOS DAG identities.
- Four nonzero leading certificates and two historical metadata scope checks.
- Two binary affine compositions and 48 full parent/composed evaluations, including 24 signed tuples and 1,008 scalar residual checks.
- 288 checked historical reconstruction rows and the raw zero-input boundary.
- 126 malformed-call rejections, six defensive-copy checks and two warm-source pin checks.

A separate fresh default author replay passed and matched its entire saved receipt: 96 full polynomial/index identities, 48 signed cases, 2,016 scalar residual identities, 465 malformed-call rejections and six defensive-copy checks. A fresh independent replay matched its full saved receipt byte for byte, with exact type-sensitive comparison. Finite assignments corroborate the all-value algebra and public contracts; they do not enumerate unbounded positive solutions or materialize astronomical Pell witnesses.

Run in the maintained artifact directory, using the Python environment for the inherited compiler dependencies:

```sh
python review_u15_factored532.py \
  --source u15_packed_factored_index532.py \
  --root . \
  --affine u15_joint_binary_affine_rewrite.py \
  --expect review_u15_factored532.json \
  --output review_u15_factored532.fresh.json
python u15_packed_factored_index532.py --root .
```

All paths are explicit; the helper has no fixed temporary or workspace path. Assertions must remain enabled. Authentication occurs before importing the reviewed source, while the authenticated compiler checks the deeper source lineage itself.
