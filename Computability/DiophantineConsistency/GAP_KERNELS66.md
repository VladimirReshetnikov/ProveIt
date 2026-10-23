# H2082 literal source and kernel certificate

The H2082 coefficient extraction is supplied by `GapGeometry66`,
`GapCertificate66`, `GapKernelData66` and `GapKernels66`. The source equations
are exactly the frozen `GapSource66.rows`; this stage supplies a new target
layout and coefficient tables without defining a second copy of those rows.

There are 31 actual input coordinates, with the same distinct positive weights
as the split116 construction and maximum weight116. The new layout has22
distinct targets, with maximum2050. Its85 coefficient records divide into6
constant,36 linear and43 quadratic records. The39 active quadratic pairs have
unique weight sums among all496 unordered input pairs. The Lean geometry
certificate checks the span and cross-target exclusions for all22450 possible
same-degree interactions. It imposes no cross-degree exclusion.

`GapCertificate66.coeff_source_rows` proves, over every commutative ring, that
the generic degree-separated product's coefficient at each literal target is
twice the corresponding permuted source row. Its integer zero equivalence
therefore holds without an additional coefficient or native-calibration
hypothesis. The row permutation is checked to be surjective.

`GapKernels66.D0_eq`, `D1_eq` and `D2_eq` bind the three literal sparse kernels
to those generic coefficient channels. `sourcePolynomial_zero_iff` identifies
all target-coefficient zeros with all22 source-row zeros. The degree bounds are
1627,1941 and1850 respectively; the quadratic kernel has coefficient1 at1850
and hence exact degree1850 over every nontrivial coefficient ring. The whole
source product has degree at most2082. Consequently its high-word block needs
2083 positions, and the combined low/high word needs2200 positions.

All85 literal coefficient recipes have the strict generic bound `2*Bcap*Kcap`
under `Bcap>=2`, `Kcap>=16*Bcap` and the four port bounds

```
0 <= beta,MC < Bcap; 0 <= MF < 2*Bcap; 0 <= K < Kcap.
```

`kernel_heights_box` transfers that bound to every coefficient of each sparse
kernel. `kernel_heights_pow` expresses it as `2^(p+q+1)` for
`Bcap=2^p`, `Kcap=2^q` and `p+4<=q`. Thus the whole compact54 bounds
`p=429959`, `q=434054` give the stated height `2^864014` without mixing ports.
The unconditional all-one source obstruction remains row9 = -7, so a source
zero in successor coordinates has a positive digit.

The generators read inert JSON with these exact pins:

| Input | SHA256 |
|---|---|
|source.json|`e4f50dbede42c421defa2d7d36268413351dd1e023763c584ea34f3b9a827957`|
|layout.json|`d4b85e61d6cc88a385d608f11a938f8b36bf4280940f4d236be897573d3b6f51`|
|kernels.json|`7a2a497fdb37c41e0246b4ef6dc2ccdba8c32f5ac5b4f00be454d1e4bf1b37d4`|

`generate_gap_certificate66.py` independently recomputes the source-channel
coefficients and all geometric exclusions before emitting the Lean data.
`generate_gap_kernels66.py` emits the literal kernel recipes, identities and
height proofs. Both support `--check` without writing. Dedicated check files
audit the geometry, source binding, literal kernel binding and bounds; only
Lean's standard axioms occur.

This certificate supplies the literal 85-record source-to-coefficient bridge.
The subsequent [word-range stage](GAP_WORDS66.md),
[rank calibration](GAP_NINE_RATIO66.md) and
[unbounded source contract](GAP_SOURCE_NINE66.md) now pass Lean. The
443/450-operation DAG's identity with that arithmetic contract, whole-tuple
native calibration and the internal ZFC biconditional remain separate.
