# Independent review of the exact U15 cross-projection reduction

**PASS; no unresolved finding.** Reviewed final source `u15_packed_cross_projection507.py`, SHA256 `dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4`, and complete companion note SHA256 `25f27db244a3eeecf17beabbd48cf8b5c608a1fe2dc52f9630bb05e9b6f0d4dd`. The change saves exactly2M+2A in each of eight complete emitted forms, without changing the entire polynomial, any comparison residual, any supplied coordinate or any semantic domain.

I read the candidate implementation and note, the actual511 parent implementation/proof and earlier independent review, and the partition-frontier proof. The checker independently reads and pins the complete saved parent emissions, compares them against the candidate's canonical parent descriptors, and checks every emitted old/new schedule. This does not re-prove the earlier native/loader universality constructions or repeat the4,140-partition census. No full universal accepting Pell tuple is materialized.

The independent checker is `review_u15_cross_projection507.py`, and its saved receipt is `review_u15_cross_projection507.json`. They authenticate the candidate and two immediate parent sources before import, plus both saved parent receipts. The candidate is executed directly from authenticated source bytes. All paths are supplied explicitly; the checker has no permanent worktree or temporary-path dependency.

## Algebra and complete source identity

The four identities hold as formal integer polynomials, without any positive-zero assumption, native typing, radix geometry, Boolean selection or decoded computation:

1. With `a=binary28`, `b=binary14`, `c=binary15`, the parent's actual controller rows give `W=a+b+c−17` and `WD=c−9`. Thus `2W−ZU−2WD=2(a+b−8)−ZU`. The new left-tape cut includes precisely this expression, including the offset−8 and the paid multiplication by2. The original `ZU+2WD` remains computed for the right-tape consumer.
2. `Qdev=binary83−6`, followed by adding7, is exactly `binary83+1`. The deleted Qdev register is not used by another live arithmetic consumer.
3. `Dir*(B−1)*(P+1)+Dir*P²` is `Dir*((B−1)*(P+1)+P²)`.
4. `(D−1)*J*(P+1)*P³+(K29*J)*P⁵` is `J*((D−1)*(P+1)*P³+K29*P⁵)`.

I independently expanded each old/new cut using SymPy and compared it with the handwritten polynomial above. For the last cut the independent atoms extend through the entire direction part of Mjoin, rather than treating the preceding direction cut as a free oracle. This gives32 exact local identities across eight forms.

A separate exact expression interner then proves that all cut inputs are unchanged, every comparison operand is identical, every native unit factor is identical, all retained native/tag/loader ports are identical, and the final output DAG agrees after inserting the four proved identities. The complete finalizer suffix is also required to match the saved parent's suffix literally. These checks cover183 comparison residuals and eight entire polynomials. They do not merely compare numerical zeros or assume a final sum of squares.

The ordinary grouped anchor can be signed away from zeros; it need not be nonnegative for this proof. Since its **whole polynomial value** is unchanged, the original integer-unit and sign argument transfers directly. No strong-rank equation or positivity assumption is replaced by a local shortcut.

## Fully paid counts and aliases

The independently counted complete schedules are:

| Form | Certificate | Complete polynomial | Equations | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| Raw ungrouped |289=105M+184A|321=116M+205A|11|51|1936|
| Raw grouped |290=106M+184A|319=116M+203A|10|51|3464|
| Ordinary ungrouped |427=178M+249A|519=209M+310A|31|87|1936|
| Ordinary grouped |433=184M+249A|507=209M+298A|25|87|4881|
| Partition representative0 |433=184M+249A|507=209M+298A|25|87|4881|
| Partition representative1 |432=183M+249A|509=209M+300A|26|87|3120|
| Partition representative2 |431=182M+249A|511=209M+302A|27|87|2116|
| Partition representative3 |430=181M+249A|513=209M+304A|28|87|1936|

The eight forms include two copies of the same507 anchored schedule, under different authenticated parent interfaces; they are not asserted to be eight different polynomials.

All constants, binary operations, squares and finalizer gates are charged. Every emitted gate is reachable from the complete output. Compared with each actual parent, both certificate and polynomial schedules lose precisely2M+2A. The thirteen pruned registers are

    binary43,binary44,binary78,binary84,
    v166,v168,v173,v174,v251,v258,v259,v260,v261.

Nine new gates replace them. The left-tape rewrite contributes the one-addition saving because it replaces W's three private affine operations by two; it does not count shared WD work as deleted. The two mask factorizations each remove one multiplication. Offset folding removes the other addition.

The five old convenience aliases `W,Qdev,direction_mask,range_mask,Mc` point only to these deleted registers and are moved to explicitly historical, proof-only formulas. No supplied witness is deleted. Current metadata exposes `WminusWD` and `Qdev_plus7` and never pretends the old five values remain emitted. Existing comparison maps, native factor records, tag registers and computed-loader fields are unchanged. Historical affine/composition metadata and any ancestor polynomial-identity flag are separated from the new immediate-parent identity claim.

## Degree, domain and API

Exact polynomial identity transfers the parent's exact degree for every fixed program slice. It also avoids any need to treat a loose syntactic degree upper bound as exact. The source copies the authenticated parent's stronger degree certificate and separately recomputes its own conservative gate-based ledger.

As an independent attainment check, I evaluated **every coefficient** of each emitted polynomial under an explicit univariate specialization modulo1009, using exact carry-free integer convolution. The resulting degrees are1936,3464,1936,4881,4881,3120,2116,1936 respectively, with nonzero leading coefficients967,361,984,257,257,715,9,984. This checks the actual full gate lists, without a special main-norm cancellation override. The uniform upper bounds follow from the full polynomial identity and previously established parent certificates, not from this finite specialization alone.

Raw `L0,R0` remain natural, including zero, and all51 raw witnesses remain strictly positive. Ordinary input x, four fixed program numerals and all87 ordinary witnesses remain positive. Valid-program qualification and unbounded first-halt semantics are inherited. Unrestricted signed evaluation is only an algebra-check API, not an enlarged computational domain. The separate global87-operation universal-polynomial benchmark is unchanged.

The public canonical APIs use exact flag/scalar types, whole-packet comparisons, authenticated parent-descriptor hashes and defensive copies. The generic `rewrite` explicitly claims only a locally checked algebraic rewrite for an arbitrary packet, with no invented universal theorem. Parent source hashes and their inherited dependencies are revisited on warm-cache access. The new loader compiles authenticated bytes directly, and the module rejects `python -O` before invoking historical parents that rely on assertions.

## Independent evidence and reproduction

The checker passed:

-32 exact local polynomial identities, eight complete DAG identities and183 exact residual identities;
-96 complete numerical evaluations, including48 signed cases and raw zero-half-tape inputs;
-eight literal full-polynomial degree expansions;
-344 malformed packet/scalar/domain/flag rejections, including equal-valued float coefficients before huge-integer evaluation;
-16 public copy checks and two private warm-cache parent-source mutation checks.

The final author writer and the integrating root's fresh default replay from the maintained repository both passed. That replay covers256 integer and32 rational identities,5,856 residual comparisons and852 rejections. Those broader author-suite counts are not counted as independent tests here.

Run the independent receipt check with explicit paths:

    /path/to/sympy-python review_u15_cross_projection507.py \
      --source /path/to/u15_packed_cross_projection507.py \
      --root /path/to/native-stream-queue \
      --output /path/to/fresh-review.json \
      --expect review_u15_cross_projection507.json

Only the named output and private temporary copies are written. There were no repository edits, archive edits or Git mutations in this review.

Root subsequently ran this independent checker from the maintained repository
against the frozen receipt. It passed all stated checks and reproduced the
receipt byte for byte, separately from the author-suite replay above.
