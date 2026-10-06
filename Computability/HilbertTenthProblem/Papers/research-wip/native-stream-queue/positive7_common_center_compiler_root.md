# Complete positive7 compiler with shared common-center contributions

The complete compiler now incorporates the [paid common-center proof](positive7_common_center_pack_pascal.md) into the [power-alias parent](positive7_power_alias_compiler_root.md). The saved r=1,2,4 graphs cost **809,875,1021 operations**, respectively. The same integer final polynomial, ordinary positive input,96+6r positive witnesses,23 comparisons and6+15r linked fixed roles are preserved. The r1 choice exchanges one addition for one multiplication at equal total cost. No numerical universal presentation, source degree, optimality or improvement of general84 is claimed.

For r>=1 let m=8+2r, ell=62+6r. Inherit the paid geometric-extension costs gM,gA and indicators A=prefix101, B=prefix1110 with at least five bits, C=prefix10011 of binary m. Put eta=1 when binary m begins100, otherwise0. The source grammar chooses uniform sharing for1<=r<=7 and collected sharing forr>=8. Its complete counts are

    uniform:   (224+30r+gM-A-B-C)M+(508+40r+gA-B)A,
               total732+70r+gM+gA-A-2B-C;
    collected: (227+30r+gM-A-B-C-eta)M+(512+39r+gA-B-eta)A,
               total739+69r+gM+gA-A-2B-C-2eta.             (1)

Subtract23M45A for the certificate. The saving from the exact power-alias parent is max(r-1,2r-8+2eta). These formulas describe a handwritten all-r source grammar. The actual frozen parent and successor contain only r1/2/4, all uniform; no collected, seed7, B or C complete saved example is invented. The separate r0 fallback remains903 operations and96 witnesses.

## 1. Paid cut, exact substitutions and semantic forms

For relator j the retained shared decoder and sparse products supply

    L1=decoded_u_sum_j=u1*c1+u2*c2,
    L2=decoded_v_sum_j=v1*c1+v2*c2+v3*c3,
    W=center_word=lambda*D*J.

The old producer appends A1=L1+W and A2=L2+W at2A per relator. Its sole arithmetic consumers are left_form_pair_j for A1 and left_form_shift_j for A2. The actual paired-lane stage uses

    shift=P*A2, pair=shift+A1,
    acc=P4*acc+(1+P2)*pair,

descending through the relators from an initial DP+S. It then appends the four seven-field blocks and the two six-field pairs. All history block contents, support powers/factors, selector joins, right/output packs and later stages are inherited literally except the substitutions specified here.

Both routes remove exactly those2r center-addition records and preserve all5r coefficient products and3r dot-product additions, including zero and unit coefficient roles. The renamed stage sparse_uncentered_input_forms costs5rM3rA. The canonical SAME-V recipe, ell=V*C guard bounds and fixed coefficient preparation are unchanged.

The removed names also occur in centered_input_forms and in the left components of native lanes. These fields now contain explicit descriptors

    {"semantic_sum": ["decoded_u_sum_j", "center_word"]},
    {"semantic_sum": ["decoded_v_sum_j", "center_word"]}.

There are2r form descriptors and4r lane occurrences. Each refers to actual existing L and W producers. It describes the same mathematical A=L+W, not a supplied value or an executable register. No absent A name remains an arithmetic or computed-port binding. Existing semantic_product descriptors and all actual computed ports remain unchanged. The explanatory semantic_lane_note now covers both descriptor types. Neither L alone nor an uncorrected accumulator is asserted positive.

At a full zero, the inherited guard still makes the same semantic A values positive and in range. More strongly, the identities below preserve the entire final polynomial on every integer tuple with the same fixed-role assignments, without requiring positivity, dyadic, selector or carry hypotheses. Thus the valid inherited fixed recipe has exactly the same positive zero tuples and ordinary-input projection. Semantic lane bookkeeping records this proof; it supplies no unpaid arithmetic operation.

## 2. Uniform route and exact record partition

Before the high-left block prepare common_center_pair=pack_R2*center_word, charging1M. For every j replace the old shift by P*L2 and the old pair definition by

    left_form_uncentered_j=left_form_shift_j+L1;
    left_form_pair_j=left_form_uncentered_j+common_center_pair.

The last line is a newly charged addition and restores the original pair exit name. Since common_center_pair=(1+P)W, the exit equals the old A1+P*A2 identically. The existing repeated-factor consumer continues to use that exit name. Every following accumulator and all later pack exits agree with the parent.

This deletes2r additions, rewrites2r old rows and inserts one product plus r additions. Net change is+1M-rA, saving r-1. For a parent with N rows, the disjoint successor partition is N-4r literal rows,2r rewritten rows and r+1 inserted rows. The rewritten old pair definition changes its output label; the inserted correction row reuses the old exit label. Distinct final definitions and source order are preserved, so that label reuse is not an extra deletion or a duplicate definition.

| r | Deleted rows | Literal | Rewritten | Inserted | Certificate M/A | Full M/A | Total |
|---:|---:|---:|---:|---:|---:|---:|---:|
|1|2|805|2|2|235/506|258/551|809|
|2|4|868|4|3|263/544|286/589|875|
|4|8|1008|8|5|327/626|350/671|1021|

Thus2,681 literal rows,14 rewritten rows and10 inserted rows cover all2,705 successor rows. Fourteen parent rows disappear. The complete64-row native certificate and68-row finalizer remain literal, as do all23 comparisons, the exact positive auxiliary lists and every fixed-role occurrence. Gamma remains the sole fixed role in an addition; the other5+15r roles occur once each in paid multiplications.

## 3. Collected route, support aliases and general fanout

For r>=8 each old shift and pair instead becomes P*L2 and P*L2+L1 with no per-relator extra row. After the r quartets the omitted center is W*R_(4r). After the four seven-field blocks the difference is W*P28*R_(4r), where R_n=1+P+...+P^(n-1). Restore it immediately after left_seven_high_join, before its sole arithmetic consumer left_six_high_shift_b.

The division-free identity

    (Pm+P8)*(Rm-R8)=P16*R_(4r)

follows from m-8=2r, Rm-R8=P8*R_(2r), and Pm+P8=P8*(1+P^(2r)). It holds at P=0,1 and negative P as an integer polynomial. The complete paid insertion is

    P8=pack_P7*P; R8=pack_R7+pack_P7;
    plus=Pm+P8; difference=Rm-R8;
    shifted=W*P12; times_plus=shifted*plus;
    correction=times_plus*difference;
    restored=left_seven_high_join+correction.

Use the inherited selector_power and selector_geometric_sum ports for Pm,Rm, and left_support_P12's port for P12. In seed6 that last port already points to geom_P12, so no retired power name is resurrected. When eta=1 the retained geometric extension supplies both geom_P8 and geom_R8 earlier, and the first two new rows disappear. Increasing binary prefixes prove that this happens exactly at prefix100, independently of A/B/C; no geometric support is credited twice.

Redirect left_six_high_shift_b to restored and keep its P12 operand. After that point every parent accumulator and pack exit agrees again. The uncorrected intermediate quartet and seven-block accumulators generally differ; their sole downstream chain and this restoration establish the final-polynomial claim. No claim of equality at every intermediate register is needed.

The general cut deletes2r additions, rewrites2r+1 old rows and inserts(4-eta)M+(4-eta)A. Relative to N parent rows, the literal/rewritten/inserted partition is N-4r-1,2r+1,8-2eta. This is a source-grammar proof, not saved-array coverage of an absent r>=8 example. The original composer contains this branch but its saved-example loop and count assertions are deliberately restricted to the actual r1/2/4 input graphs.

Uniform and collected savings differ by r-7+2eta. For1<=r<=7 uniform wins or ties: eta=1 only forr4,5, with a tie atr5; r7 also ties. Forr>=8 collection is strictly cheaper. This proves the route choice in(1) among these two displayed schedules, not a minimum over all circuits.

## 4. Disjoint full count and exact metadata obligations

The unchanged input/geometry/guard stage costs8M+(134+12r)A; shared decoding costs5A; sparse uncentered forms cost5rM3rA. Three packs and supports cost

    uniform:   (108+13r+gM-A-B)M+(90+11r+gA-B)A;
    collected: (111+13r+gM-A-B-eta)M+(94+10r+gA-B-eta)A.

The remaining disjoint stages are the inherited native scale(4-C)M, native certificate33M31A, paired action30M168A, selected centers/quotient appends12rM14rA, fused positive lift12M21A, and recurrence right sides6M14A. Their sum gives certificates(201+30r+gM-A-B-C)M+(463+40r+gA-B)A for uniform and(204+30r+gM-A-B-C-eta)M+(467+39r+gA-B-eta)A for collected. Adding the23M45A finalizer proves(1).

The exact source parent is the committed power-alias JSON e2985ae7fa1754c347261bca096c4d360f263bcbabf58481f7a0e1d305558b2a at4cd909451. The new receipt replaces pack_power_alias_splice by common_center_splice and records the route, eta, every deleted/rewritten/inserted row, literal survivor names, old/new source digests, paid cut ledgers and explicit semantic descriptors. Stage rename, changed semantic fields and the absent collected-example boundary are stated. Source/stage/full/certificate counts and static checks are updated. All remaining fields, including the fixed recipe, r0 fallback, actual ports, supplied lists, native scale cost and endpoint aliases, remain inherited. Independently auditing these facts is separate from the author's original metadata checks.

## 5. Retained claims and remaining scope

**Remark1 (centers cannot simply disappear).** The frozen local counterexample remains: without compensation, the final high word changes by W*P52*R_(4r), which is15*2^52 at r1,P2,W1. This is a local polynomial counterexample, not a full compiler zero. L cannot replace A in the native positivity statement.

**Remark2 (no free quotient; valid weaker alternatives retained).** Dividing R_(2m)-R16 by P16 is neither a free arithmetic operation nor defined at P0. The paid factored schedule avoids division. The preliminary7M4A and6M4A whole-high-word schedules remain valid weaker alternatives, as proved in the local note.

**Remark3 (historical role and power-prefix corrections retained).** The parent's predecessor falsely said every fixed role occurs in multiplication. Its gamma addition and the reviewer's failed overstrong audit remain frozen; this source uses the corrected split. Likewise m14 does not provide a P28 alias merely from prefix1110; the inherited B length condition remains unchanged. No frozen helper is corrected or replayed.

**Remark4 (scope of complete composition).** The local common-center question is now resolved by the precise general source grammar and the actual uniform r1/2/4 graphs. No missing collected or seed7/B/C saved graph is manufactured, and earlier source counts and review scopes are not reassigned. At r1 the total ties rather than improves; r0 is separate.

**Open question1 (numerical universality and further cost reductions).** A concrete universal relator presentation and ordinary-input fixed data still need materialization. Source degree, further arithmetic sharing, coefficient specialization and optimality remain open. The two-schedule comparison is not a lower bound.

All new identities and counts are handwritten. Root and Riemann fully read the195-line original metadata-only composer before its sole successful run. It is now permanently frozen with its first receipt. No supplied, archived, committed, predecessor or frozen helper was executed/imported. Source arrays were only constructed/inspected as inert records: no arithmetic/coefficient evaluation, symbolic execution, degree propagation, scientific sampling or build occurred. Separate independent all-r and complete saved-source reviews must bind this exact trio.

Frozen composer SHA256:5630441e5c9700c1f8578f97a964cc67038f40052703285cf6a701bd48c00e06.

Frozen first receipt SHA256:ff634059250ac399883ae3311a81354204a84be82b6ae973983e2e9e95b7d6db.
