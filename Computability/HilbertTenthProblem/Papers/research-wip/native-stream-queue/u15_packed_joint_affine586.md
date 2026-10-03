# Exact joint affine computation:611→586

This packet replaces the seven affine projections `J,S,Dir,W,WD,Qdev,Ndev` in the frozen611 complete U15 compiler. The complete ordinary polynomial uses586 operations,239 multiplications and347 additions/subtractions; the raw polynomial uses343 operations,131 multiplications and212 additions/subtractions. The saving is exactly25 additions/subtractions in both interfaces. Every supplied coordinate, every comparison and the complete polynomial value are preserved on every integer tuple. This changes arithmetic sharing only: no state relabel, new witness, equation-only substitution, semantic relaxation or exact-degree claim is introduced.

The source helper is [u15_packed_joint_affine586.py](u15_packed_joint_affine586.py), and [u15_packed_joint_affine586.json](u15_packed_joint_affine586.json) contains both complete emitted sources and exact coefficient certificates. Canonical611 source SHA-256 is `3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce`; its complete saved receipt SHA-256 is `440da084053344360ee21ffc6a7ad41c9aab72732663d7f2b201f27cdfb44244`.

## The shared schedule

Write `h_i=edge_i` for the positive controller coordinates, so the represented field is `E_i=h_i−1`. All following identities also hold when these coordinates are arbitrary integers. Keep exactly the frozen29 relabeled rows `(q_i,s_i,n_i,d_i,w_i)`; the state center remains7.

Partition the rows by the three Boolean table coefficients `(s,d,w)`. The eight unshifted sums `C_sdw` have these literal supports:

| Bin | Edge indices |
|---|---|
|000|0,16,19,21,27|
|001|2,8|
|010|4,6,12,23,25|
|011|10,14,18|
|100|26|
|101|1,3,20,22,24,28|
|110|5|
|111|7,9,11,13,15,17|

Let `G_dw=C_0dw+C_1dw`. Compute

- `Dhat=G_11+G_10`, `What=G_11+G_01`;
- `Jhat=Dhat+G_01+G_00`;
- `Shat=C_100+C_101+C_110+C_111`.

Then the exact cut expressions are

`J=Jhat−29`, `S=Shat−14`, `Dir=Dhat−15`, `W=What−17`, `WD=G_11−9`.

The integer offsets are the actual sums of the corresponding table coefficients. Their five subtraction gates are included in the emitted source.

Continue to share source-state pairs for the centered source projection. The center7 pair is unused by this schedule and is removed as dead code before emission; thirteen source-state pair sums remain. Two additional sums, `h_22+h_24` and `h_13+h_15`, occur both inside Boolean bins and inside target-state bins. Their two gates are paid once each. The Boolean bin `C_101` also provides `h_1+h_3` to the target-zero bin through ordinary common-subexpression sharing.

For `k=1,…,7`, use the same signed centered-state formula as611:

`Qdev=Σ k*(S_(7+k)−S_(7−k))−6`,

`Ndev=Σ k*(T_(7+k)−T_(7−k))+17`,

where `S_q` and `T_n` are unshifted sums of hats with the indicated source or target code. The nontrivial constant multiplications by2,…,7 each count as one multiplication. Multiplication by1 is an identity and emits no gate. Signed intermediate sums are permitted; they are expressions, not positive witness coordinates.

## Literal arithmetic ledger

The complete new affine block has99 binary gates:

| Component | Multiplications | Additions/subtractions |
|---|---:|---:|
|13 source-state pairs and two shared cross pairs|0|15|
|Remaining eight-bin sums|0|19|
|Five Boolean/global projections, including all offsets|0|16|
|Centered source state, after the pair sums|6|14|
|Centered target state, after shared groups|6|23|
|Total|12|87|

The canonical611 affine ancestor block has124 gates:12 multiplications and112 additions/subtractions. The complete emitted replacement therefore saves25 additions. All99 new rows are reachable from the final polynomial; all other emitted arithmetic is charged as before.

| Interface | Certificate | Complete polynomial | Positive witnesses | Equations |
|---|---|---|---:|---:|
|Raw|311=120M+191A|343=131M+212A|51|11|
|Ordinary|449=193M+256A|586=239M+347A|102|46|

The complete polynomial degree bound remains1936; `exact_degree_claimed` is explicitly false. The polynomial is identical to611, but this helper does not independently author a leading-coefficient certificate. The exploratory four-bin schedule gave595 operations; deriving `S` by its difference from `W` gave590; the eight-bin schedule without the two additional shared pairs gave588. These were bounded alternatives, not an optimality search.

## All-integer identity and source privacy

The helper expands all seven old and new cut expressions into exact dictionaries of integer coefficients in the29 hats and a constant. Each dictionary agrees exactly. In particular, the state deviations remain deviations; they are not silently renamed numerical state values.

The removed block is the complete ancestor closure of the seven canonical611 cut registers. Its124 rows must match the embedded reviewed rows exactly, including operators, coefficients and scalar types. Every edge leaving this closure must pass through one of the seven cut registers. An extra source or comparison consumer of any other internal register is rejected. Metadata is inspected recursively as well: an alias to a cut is rewritten, while a reference to a removed private intermediate is rejected. Consequently no other semantic register is left referring to removed arithmetic.

After substituting the seven new cut registers, all retained downstream rows and all comparison operand pairs are literal copies of their incoming counterparts. Induction through the remaining straight-line source gives equal values at every retained expression and residual for every integer input tuple. Rebuilding the exact sum-of-squares finalizer therefore gives the same complete polynomial. This is a source-level proof from affine coefficient equality and private cut substitution; the bounded numerical tests are additional corroboration.

The identity preserves any natural or positive zero set and any existing parent projection/lift theorem without a new positivity argument. The raw/ordinary loader, native field ports, fixed program parameters and halting semantics are inherited unchanged from the caller's proved parent. This is not an87-operation universal-polynomial result.

## Narrow reusable API

`rewrite(packet)` returns `(fresh_complete_packet, proof)`.

The input must have the exact canonical611 affine closure, seven cut names and relabeled rule table. Other downstream source rows, comparisons and declared coordinates may have been changed independently. The complete incoming circuit must be valid, have no dead emitted arithmetic, and have its exact canonical sum-of-squares finalizer. Input rows may use either builtin lists or tuples; atom types are checked exactly, so Booleans and numerically equal floats cannot replace integer coefficients. Metadata must use builtin JSON-like data, with no fractional scalar values.

The result rebuilds the complete finalizer and operation/degree ledger. It preserves unrelated parent metadata and adds `affine_rewrite` provenance. It does not authenticate the caller's entire parent module or establish that an arbitrary supplied parent represents halting. A maintained composition must pin its own parent source, rebuild its own top-level provenance and retain the appropriate parent zero-set proof. Historical comparison-index maps should be removed or relabeled by that composition rather than presented as maps to the new affine parent.

`replacement()` returns fresh copies of the99 rows and the seven new cut-register names. The proof returned by `rewrite` exposes the old-to-new register map, exact affine coefficient dictionaries, incoming complete-polynomial digest, and exact row counts. There are no public mutable caches. Reordering the independent affine block or adding a legitimate downstream cut consumer is supported. Adding a private-node consumer is rejected.

The CLI is deliberately narrower: it authenticates the frozen611 source and receipt before emitting the two canonical586/343 children and executing its bounded checks:

```sh
python u15_packed_joint_affine586.py \
  --parent-source u15_packed_centered_states611.py \
  --parent-receipt u15_packed_centered_states611.json \
  --output u15_packed_joint_affine586.json
```

The saved receipt records64 complete polynomial-and-residual comparisons, including32 signed tuples;38 malformed-source/type/metadata rejections;8 defensive-copy checks; and4 supported adapter cases. The exact seven-cut proof is checked on both complete sources. Existing expensive frontend suites were not repeated.

## Composition check with downstream561

A separate bounded adapter check applied this same frozen helper directly to the currently saved downstream561 packets. Both were accepted without helper changes. Every supplied tuple in32 complete comparisons, including16 signed tuples, preserved all residuals and the full polynomial. The resulting source ledgers are raw338=126M+212A and ordinary536=219M+317A. The latter retains the downstream parent's87 positive witnesses and31 comparisons; raw retains51 witnesses and11 comparisons.

The downstream parent's `computed_loader_fields` and existing historical `comparison_map` were unchanged by this arithmetic rewrite. A public536 wrapper remains a separate integration artifact and must expose its relation to the actual561 parent, with restoration delegated through that parent. These composition checks do not replace the independent review of the downstream field elimination or the final public536 wrapper.
