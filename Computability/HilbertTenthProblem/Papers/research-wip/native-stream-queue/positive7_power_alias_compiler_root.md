# Complete positive7 compiler with paid geometric support aliases

For r>=1 the complete symbolic family now costs

    (223+30r+gM-A-B-C)M+(508+41r+gA-B)A,
    total731+71r+gM+gA-A-2B-C.                            (1)

Here m=8+2r, ell=62+6r, and gM,gA retain the paid geometric extension of the [shared-decoder parent](positive7_shared_decoder_compiler_root.md). The indicators refer to the binary expansion of m: A marks prefix101, B marks prefix1110 with at least five digits, and C marks prefix10011. They are pairwise disjoint. The certificate is(200+30r+gM-A-B-C)M+(463+41r+gA-B)A. There remain96+6r positive witnesses,23 comparisons,6+15r linked fixed roles and the same ordinary positive input. The r=0 fallback remains903/96, general84 is unchanged, and numerical universal relator data, source degree and optimality remain open.

This composes the [local support-alias theorem](positive7_pack_power_alias_aristotle.md) into a new complete source. It deletes duplicate operations and redirects their actual uses to already paid earlier values. The three complete parent examples r=1,2,4 yield2,709 saved rows at809/876/1024 operations. The all-r grammar proof covers further seed7/B/C branches, but no complete saved examples for those branches are present in the parent or claimed in this receipt.

## 1. Exact earlier producers and alias identities

Write P for the lane scale and R_n=1+P+...+P^(n-1). The retained prefix chooses seed6 or7 for leading110 or111 of m, otherwise seed2 on leading10. Each remaining bit first doubles a pair(P^n,R_n) with

    geom_P(2n)=P^n*P^n,
    geom_factor_(2n)=P^n+1,
    geom_R(2n)=R_n*geom_factor_(2n).

For an odd bit it also appends geom_R(2n+1)=geom_R(2n)+geom_P(2n) and geom_P(2n+1)=geom_P(2n)*P. The handwritten finite geometric identities prove this grammar over Z[P]. If d bits remain and e are odd, its cost is gM=2d+e,gA=d+e; none of these already paid operations is removed here.

Since m>=10, every chosen seed has at least one subsequent doubling. The first doubling supplies both a power and a plus-one factor that the later left support would otherwise recompute. The exact alias table is:

| Later record removed | Earlier producer retained | Condition |
|---|---|---|
| left_support_P4 | geom_P4 | seed2 |
| left_pair_factor_2 | geom_factor_4 | seed2 |
| left_support_P5 | geom_P5 | A=1 |
| left_support_P12 | geom_P12 | seed6 |
| left_pair_factor_6 | geom_factor_12 | seed6 |
| left_support_P14 | geom_P14 | seed7 |
| left_pair_factor_7 | geom_factor_14 | seed7 |
| left_support_P28 | geom_P28 | B=1 |
| left_pair_factor_14 | geom_factor_28 | B=1 |
| native_shared_P19 | geom_P19 | C=1 |

The first pair saves1M1A in every case. A adds1M, B adds1M1A, and C adds1M, giving deltaM=1+A+B+C and deltaA=1+B. The earlier and later records need not have identical operands: P2*P3=P4*P=P5, and P12*P7=P18*P=P19. The table uses polynomial identities, not equality at a special numerical P or an uncharged supplied power.

Growing binary prefixes prove the exact conditions. In the seed2 branch only its first odd append produces P5. P28 requires prefix14 followed by another digit, giving B's length condition. P19 requires prefix10011; since m is even its first possible complete case is m=38. The other native exponents m+19,2m+38,3m+38 exceed m, while all geometric exponents are at most m. The theorem exhausts these named supports against this prefix, not arbitrary sharing elsewhere.

## 2. Complete source transformation and same polynomial

The sole input is the committed shared-decoder JSON e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95. The original composer reads it as inert row/name metadata, builds the alias map from the fixed m, removes exactly its later definitions and replaces every surviving operand reference to those definitions by the corresponding earlier producer name. Every other row is literal. No new arithmetic record, witness, ordinary input, coefficient role or runtime case branch is introduced.

The retained geometric targets all precede the removed supports, so every replacement points backward to an actual earlier definition. Substitution preserves every affected consumer polynomial by induction in source order, including support-to-support and support-to-native edges. It therefore preserves all later native residuals, action increments, recurrence comparisons and the full final polynomial. These equalities hold for every integer P, including0,1 and negative values, and every integer runtime tuple with the same fixed-role assignments. Under the inherited canonical valid fixed recipe, the same supplied positive zero tuples and ordinary-input projection are preserved. No guard or carry argument is weakened.

The semantic lanes and all decoder/form/quotient bindings remain unchanged. Computed-value ports are rebound too: in seed6, ports.left_support_P12 points to geom_P12. The final native T exit stays native_shared_scale. When C=1 the earlier geom_P19 replaces native_shared_P19, and only three new native-scale products remain, so native_scale_products is4-C rather than a stale4. The receipt's generic ledger states that case dependence. No C=1 graph is among the three saved examples, all of which retain four products.

The old form_decoder_splice is replaced by the actual pack_power_alias_splice: exact alias map and earlier target records, every removed row, literal survivor names, every before/after rebound row, changed ports, old/new source digests and paid deletion count. The fixed-data recipe and r=0 fallback remain literal. All role occurrences remain paid:5+15r roles occur in multiplications and gamma occurs in one addition, preserving the parent's recorded correction.

## 3. Disjoint all-r ledger and saved-example coverage

The complete three-pack/support stage becomes(107+13r+gM-A-B)M+(90+10r+gA-B)A. The native scale is(4-C)M. All other stages retain the shared-decoder parent's disjoint costs. Together they give the certificate in the opening and the unchanged23M45A finalizer gives(1). Equivalently subtract deltaM M+deltaA A from the exact parent; the direct stage derivation agrees.

The full grammatical rebound-record counts are2r+A+C for seed2,5 for seed6,3 for seed7 without B, and2 for seed7 with B. In the last case two altered operands meet in left_four_seven_factor, while the intermediate P28 and plus-one-P14 definitions themselves disappear. These count surviving records, not changed operand occurrences. The same casewise fanout proof covers branches absent from the saved examples.

| r | Removed M/A | Literal rows | Rebound rows | Certificate M/A | Full M/A | Operations | Witnesses |
|---:|---:|---:|---:|---:|---:|---:|---:|
|1|2/1|806|3|234/507|257/552|809|102|
|2|1/1|871|5|262/546|285/591|876|108|
|4|1/1|1016|8|326/630|349/675|1024|120|

Thus2,693 literal rows and16 rebound rows cover all2,709 successor records. Seven duplicate parent records disappear and no new arithmetic rows are added. Every source name/operand, operation census, fixed-role set and supplied/computed liveness is checked structurally; all68 finalizer rows and23 comparisons remain unchanged. The r2 P12 computed-port change is explicit. These author metadata checks are not substituted for the separate independent complete source audit.

## 4. Retained boundaries and evidence

**Remark1 (the prefix length is necessary).** At m=14, binary1110 ends immediately after the first seed7 doubling, so no geom_P28 exists. The unqualified prefix1110 alias claim fails there. B includes at least one more digit; no absent producer is treated as free.

**Remark2 (valid weaker observation and fixed-role correction).** The earlier powers-only1M guarantee, with an extra P5 at r1, remains valid; the plus-one aliases improve it. The parent's frozen claim that every fixed role occurs in a multiplication remains refuted by program_tau=program_scaled+gamma. The correct one-paid-occurrence statement and gamma exception are used here; no parent error or failed reviewer attempt is erased or replayed.

**Remark3 (saved coverage is not a missing branch experiment).** The all-r table and its source grammar include seed7, B and C, but this particular parent contains only r1/2/4. The three saved graphs cannot certify literal examples of the missing branches. Their algebraic grammar and fanout are proved separately. No old source count is reassigned and no synthetic parent is invented as evidence.

**Open question1 (further reductions and numerical universality).** Further center sharing, coefficient specialization or other powers require separate paid proofs and complete compositions. Actual numerical universal relators and the resulting equation bound, source degree and global optimality remain open. This packet resolves the prior local alias theorem's complete-composition question only for the precise all-r grammar and saved graphs documented here, without enlarging predecessor historical scopes.

All mathematics is handwritten. The new original metadata-only composer was read in full by root and independently preflighted by Riemann before its sole successful run. It is now frozen with its first receipt. No supplied, archived, committed, predecessor or frozen helper is executed or imported; no saved source or coefficient array is numerically or symbolically evaluated, no degree is propagated, and no scientific sampling or build is used. Independent proof and source reviews must bind this exact author trio and distinguish all-r reasoning from literal saved-row coverage.

Frozen positive7_power_alias_compiler_root.py SHA256: 55e8e002fc1988f54b050748e09be1a5d23a8f9aa5ffd176e1da90b06993872a.

Frozen positive7_power_alias_compiler_root.json SHA256: e2985ae7fa1754c347261bca096c4d360f263bcbabf58481f7a0e1d305558b2a.
