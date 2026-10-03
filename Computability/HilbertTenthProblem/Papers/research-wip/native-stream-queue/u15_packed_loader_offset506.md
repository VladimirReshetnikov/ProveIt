# One loader addition removed from every complete U15 frontier source

The complete ordinary-input compiler drops from **507 to506 operations**, and the four inherited degree-frontier representatives become **506/4881,508/3120,510/2116,512/1936**. This is an exact polynomial rewrite on the existing coordinates. It removes no witness, comparison, native unit factor or finalizer requirement.

## Actual source identity

The authenticated [507 parent](u15_packed_cross_projection507.py) contains this loader subgraph, where `u` is the emitted register `input__congruence_right0`:

```
input__restored_Ahat = u + 1
input__and__scaled_Z = 16 * input__restored_Ahat
input__and__F3       = input__and__scaled_Z - 8
```

Its complete source has exactly one consumer of `input__restored_Ahat`: the displayed multiplication. The new [compiler](u15_packed_loader_offset506.py) emits

```
input__and__scaled_Z = 16 * u
input__and__F3       = input__and__scaled_Z + 8
```

because `16*(u+1)-8=16*u+8` identically. Three paid operations become two. The intermediate register named `scaled_Z` changes value; its consumer `F3` keeps exactly the same polynomial. No claim that every intermediate register is unchanged is needed.

The wrapper checks the three literal old rows, the single-consumer condition and the historical field map before rewriting. It proves the local identity as sparse polynomials in the independent atom `u`. An exact shared expression-DAG audit then checks that `u` itself is unchanged and that, after substituting the proved `F3` identity, every complete comparison operand, every present native unit factor and the complete output have identical expression DAGs. This proves equality of the entire old and new polynomials on all integer and rational assignments. It is stronger than zero-set equivalence and involves no sign premise or division.

The source includes all loader, packed history, native kernel and finalizer operations. All finalizer rows remain literal, and every emitted operation is live. The six protected norm factors and sole unrestricted checksum factor of the grouped ordinary forms are identical to the parent's factors. The two raw-input forms contain no such ordinary-loader subgraph and remain byte-for-byte identical as arithmetic schedules.

## Fields, domains and degree

`input__restored_Ahat` was already an arithmetic definition for a formerly projected ancestor field; it is not a supplied coordinate in507. The new source therefore has exactly the same parameter and witness lists. Its active `computed_loader_fields` map contains the fourteen remaining emitted restorations. The fifteenth field, `input__Ahat`, has the explicit proof-only formula `u+1` in `computed_loader_field_formulas`. That historical formula describes restoration to the older loader, not an uncharged register in the new circuit. The original positive restoration remains valid because the mathematical value `u+1` has not changed.

All natural raw-tape and positive ordinary-input domain conditions, fixed valid program-slice hypotheses, arbitrary-duration history semantics and first-halt relation are inherited without alteration. The public evaluator preserves the parent's exact-integer domain checks: raw `L0,R0` may be zero, while other semantic coordinates are positive. Explicit `signed=True` evaluates arbitrary integer tuples for polynomial identity tests. Neither mode silently broadens the imported computational theorem to invalid program slices.

Since each **complete polynomial is identical**, the exact degrees and their fixed-program uniformity follow directly from the parent certificates. The wrapper stores those certificates under an explicit complete-polynomial identity certificate; it also separately computes a syntactic degree upper bound. This does not assert a new leading-coefficient calculation or infer exactness from the syntactic bound.

## Complete paid counts

Every binary `+`, `-` and `*`, including multiplication by a nontrivial fixed numeral, costs one operation. The single omitted gate was an addition. Counts refer to the complete final polynomial.

| Complete form | Parent total | New M | New A | New total | Witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|---:|
| Raw ungrouped |321|116|205|321|51|11|1936|
| Raw grouped |319|116|203|319|51|10|3464|
| Ordinary ungrouped |519|209|309|518|87|31|1936|
| Ordinary grouped |507|209|297|506|87|25|4881|
| Frontier representative0 |507|209|297|506|87|25|4881|
| Frontier representative1 |509|209|299|508|87|26|3120|
| Frontier representative2 |511|209|301|510|87|27|2116|
| Frontier representative3 |513|209|303|512|87|28|1936|

The ordinary grouped and frontier0 packets preserve their distinct inherited provenance but emit the same operation count. Only these eight canonical forms are claimed as emitted and reviewed. The previous full partition search is not rerun, and these counts do not establish global optimality or improve the separate87-operation universal-polynomial record.

## Authentication and replay

The parent source is pinned to SHA256 `dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4`. Before use, all eight actual parent packet descriptors must match fixed, type-sensitive hashes. The exact hashed source bytes are compiled directly, and warm calls propagate the parent's complete source-lineage checks. Public packet and source accessors return defensive copies; all supplied canonical packets require recursively exact types. The module refuses `python -O` because historical dependencies use assertions.

The deterministic [receipt](u15_packed_loader_offset506.json) includes every full source and inherited degree certificate. Author verification checks192 complete numeric polynomial identities, including96 signed cases,4,392 individual residual identities,24 rational identities, six historical loader-field restorations,1,686 malformed-call rejections and24 defensive copies. Two raw zero-tape checks preserve the natural boundary. Symbolic compositional proofs are generated for all eight packets; finite evaluations supplement those identities.

Run from the WIP directory containing the pinned parents, using the existing research environment (adjust the interpreter path for another installation):

```sh
/tmp/diophantine-research-venv/bin/python u15_packed_loader_offset506.py
```

For a separate scratch copy, pass `--root /absolute/path/to/native-stream-queue`. Default execution compares the complete freshly generated receipt with the saved JSON using exact types. Only `--write` updates the receipt. Replay requires SymPy through the historical compiler dependencies; the established research virtual environment supplies it. No external network access is needed.
