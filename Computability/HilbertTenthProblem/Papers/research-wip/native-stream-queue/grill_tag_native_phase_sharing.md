# Exact phase sharing in the native Grill compiler

The complete native compiler for the fixed Grill program `(0,1,1)` drops from **219 to209 operations**, with **94 multiplications and115 additions/subtractions**. Its complete sum-of-squares alternative drops from243 to233. The rewrite preserves the entire polynomial on every supplied tuple, every comparison and native factor, all positive coordinates, and the parent's unbounded-duration scope. The saving is four multiplications and six additions in each finalizer mode.

This is a separate child of [native Grill word closure](grill_tag_native_word_closure.md), pinned to source SHA256 `80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7`. The [child source](grill_tag_native_phase_sharing.py) and [complete receipt](grill_tag_native_phase_sharing.json) contain the literal emitted schedules and proof checks. The parent is not edited. The counts are for a fixed small program, not an instantiated universal Grill program or an improvement to the separate87-operation universal equation.

## 1. Three simultaneous affine identities

Fix a nonempty natural program tuple of length `m`. Its `2m` tile IDs retain the order `(phase0,head0),(phase0,head1),…`. Let the supplied positive selector hats be `Shat_i`. For arbitrary values of those coordinates, put

\[
 T_p=\widehat S_{2p}+\widehat S_{2p+1},\qquad
 J=\sum_{p=0}^{m-1}T_p-2m,
\]

and

\[
 R=\sum_{p=1}^{m-1}pT_p-m(m-1).
\]

The parent's two numerical phase projections are

\[
 Q=\sum_{p=0}^{m-1}(p+1)(T_p-2),\qquad
 N=\sum_{p=0}^{m-1}\bigl((p-1\bmod m)+1\bigr)(T_p-2).
\]

The first is the current phase code, and the second is its reverse chronological successor. They satisfy the exact affine identities

\[
 Q=J+R,\qquad N=R+m(T_0-2).
\]

Indeed `R=Σ_{p>=1}p(T_p−2)` because `2Σ_{p>=1}p=m(m−1)`. Adding `J=Σ_p(T_p−2)` gives the current-phase weights. In the successor projection the weight is `m` at phase zero and `p` at every phase `p>=1`, giving the second identity.

These identities use the actual definition of `J`. Treating `J` as an independent unconstrained leaf would not be sufficient. The compiler proves each old and new projection as an affine polynomial in **all original `2m` selector hats**, including their constant terms:

| Projection | Hat coefficients at phase p | Constant |
|---|---:|---:|
| J |1,1|−2m|
| Q |p+1,p+1|−m(m+1)|
| N |`((p−1) mod m)+1` on both hats|−m(m+1)|

There is no Boolean, positive-zero, selector-typing or phase-path premise in these equalities. In particular, `R` is a shared arithmetic expression, not a new witness or a new equality constraint. Computing `Q−J` again is unnecessary because it is already represented by `R`.

For `m=1`, `R=0` and `Q=N=J=T0−2`. The implementation handles the coincident aliases without introducing cycles. It preserves the original arithmetic schedule when the candidate is not strictly cheaper; both one-phase representative programs therefore remain literal no-ops.

## 2. Whole-source substitution and paid scope

The transformation starts with a complete canonical packet from the pinned parent. It emits the pair sums, their total for `J`, the weighted shared expression `R`, and the two phase projections. It reuses only identical already-emitted arithmetic subexpressions and folds literal zero/one operations. Every nontrivial fixed-coefficient multiplication, offset subtraction, pair sum and final combination is paid.

It then substitutes the three equal projections into the complete source and traces every dependency of the final output. An old state-weight multiplication may also feed the affine lower-history update `nextV`; such a gate remains live and is retained. This matters for the actual saving, which depends on the program coefficients and existing sharing. No count is inferred by deleting an isolated phase block on paper.

After the affine equalities are proved, an exact shared expression-DAG comparison substitutes the three established values and verifies every complete comparison operand, every named semantic interface, each native unit factor when present, and the final polynomial. The whole finalizer tail remains literal. Thus the child is exactly the **same full polynomial**, over the integers and also over the rationals or reals. The source change has no nonzero correction term, witness projection, choice of sign branch or new positivity obligation.

The current interface fields `J,Q,Next` point to the new live registers and retain their original numerical meanings. Every other semantic interface has the same value. Counts for the current certificate, wrapper and whole polynomial are recomputed. The inherited unit compiler's old raw-parent operation count is moved to explicitly historical metadata; it is not presented as a current child count. No eliminated source register remains in active metadata.

The child keeps the same fixed-program maps, positive input and witness lists, prescribed-native-AND ports, unit factors, output, and comparison list. The parent's ordinary padded-input, phase chronology, input-width and native completeness conditions remain fully paid. Consequently its exact positive-zero relation is inherited without weakening: duration is already packed existentially by the parent, and its accepted padded Grill inputs and possible post-halt word closures are unchanged. The parent has not instantiated a universal Grill program or verified an ordinary-input universality decoder; the child adds neither claim.

## 3. Actual complete schedules

Both finalizers are emitted for each of the four representative programs. All entries include the complete native kernel and finalizer.

| Fixed program | Finalizer | Parent operations | New M | New A | New operations | Witnesses | Comparisons | Degree upper bound |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `(0,)` | Sum of squares |192|84|108|192|32|20|304|
| `(0,)` | Native unit product |168|78|90|168|26|11|737|
| `(1,)` | Sum of squares |195|86|109|195|32|20|304|
| `(1,)` | Native unit product |171|80|91|171|26|11|737|
| `(0,1,1)` | Sum of squares |243|100|133|233|37|20|484|
| `(0,1,1)` | Native unit product |219|94|115|209|31|11|1187|
| `(2,0,1)` | Sum of squares |252|106|135|241|38|20|520|
| `(2,0,1)` | Native unit product |228|100|117|217|32|11|1277|

The `(2,0,1)` forms save five multiplications and six additions. The `(0,1,1)` forms save four multiplications and six additions because more of the parent's phase arithmetic is already shared with another live update. There is no uniform ten-operation-saving claim for arbitrary programs. The compiler emits the candidate only when its full operation count is strictly lower; otherwise it keeps the exact parent source.

The degree entries remain **formal upper bounds**, not exact-degree claims. They are propagated on the complete new DAG and agree with the parent values for all builds. The parent's `exact_degree=None` is retained. Complete polynomial identity would transfer any separately established exact degree, but no such degree theorem is newly asserted here.

## 4. Public interface and bounded evidence

`build(program=(0,1,1),*,unit_product=True,root=None)` returns a fresh canonical child packet. `checked` validates the complete source, exact scalar/container types and metadata against that canonical emission. `canonical_parent(packet)` returns the corresponding fresh parent packet; `rewrite(parent_packet)` accepts only that exact complete canonical parent. `polynomial_source` returns a defensive copy. `evaluate` accepts all and only the named positive-integer coordinates, with explicit `signed=True` for unrestricted integer algebra checks. `identity` returns the shared complete output and residual values after checking both executions. All these calls accept the optional `root` directory for the pinned WIP dependencies.

The private canonical caches do not weaken authentication: every relevant public call rechecks the direct parent's bytes and all72 inherited local source pins. First construction uses the parent's isolated source-only dependency loader. The child itself executes the direct parent from authenticated bytes. No public mutable cache holder is exported, and all packet/source builders return copies.

The author checker emits and audits eight complete schedules, proving24 simultaneous affine identities,124 exact comparison residual identities and eight full final-polynomial identities. It checks96 complete integer evaluations, including48 signed cases and1,488 individual residual evaluations, plus16 rational evaluations. The guard suite checks malformed packets, parent packets, scalar types, coordinate domains and hatted-key types; nested public copy isolation is exercised24 times. Two private warm-source tests check both a changed direct parent and an inherited source after canonical caches have been populated. No full enormous native Pell witness is constructed by this arithmetic child; all computational semantics follow from full polynomial identity with the reviewed parent.

Portable replay from the directory containing the frozen parent and inherited compiler dependencies:

    /path/to/research-venv/bin/python grill_tag_native_phase_sharing.py \
      --expect grill_tag_native_phase_sharing.json \
      --output /path/to/fresh-receipt.json

For a separate scratch source, add `--root /path/to/native-stream-queue`. The interpreter must satisfy the historical dependencies. The receipt has no absolute worktree paths or timing fields; it includes every complete child source. Only an explicitly requested output and temporary private guard copies are written. Optimized execution is rejected.
