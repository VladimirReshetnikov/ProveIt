# Complete compiler with repeated mask blocks and one shared selector prefix

This complete composition uses an all-integer polynomial identity for the complete quotient-pair compiler's three packs. For r>=1 put m=8+2r and ell=62+6r. Let pc(t)=floor(log2 t)+popcount(t)-1. The complete emitted ledger is

    (252+34r+pc(ell)+gM(m))M + (541+46r+gA(m))A
      =793+80r+pc(ell)+gM(m)+gA(m).

The positive witnesses remain96+6r; the23 comparisons, fixed roles6+18r and all native lanes remain the same. The new original metadata-only composer has emitted complete graphs for r=1,2,4; its independent mathematical and full-source reviews are separate companion artifacts. No frozen predecessor source is reassigned the new count. The previous complete quotient source costs(303+40r+pc(ell))M+(595+52r)A. The predicted saving is(51+6r-gM)M+(54+6r-gA)A. General84 and the unmaterialized numerical universal presentation are unchanged.

## 1. Actual lane order and exact pack identity

Write P for lane_scale, B for cell_radix, D for digit_height, S for the history sum, s_0,...,s_(m-1) for the raw selectors and J=sum s_i. Every pack means sum_i lane_i*P^i in the same inherited order, from lowest to highest. There are m selector lanes; then one selected block for each slot with lengths

    n_0,...,n_(m-1)=(6,6,6,6,7,7,7,7,2,...,2),
    sum n_i=52+4r;

then the aggregate and height lanes. The right entries are J in every selector lane, (B-1)*s_i repeated n_i times in each selected block, then (D-1)*J and D-1. The left and output selector entries both equal s_i. These are facts of the exact saved source's lane grammar, not a property inferred from sample evaluations.

Define R_n(P)=1+P+...+P^(n-1), n>=1. Starting from the high two right lanes, compute

    A=(D-1)*(J+P).

For i=m-1 down to0 replace

    A <- P^n_i*A + (B-1)*R_n_i(P)*s_i.

Finally set right=P^m*A+J*R_m(P). This is the original right pack as an exact integer polynomial: appending n copies of q beneath a high word a gives P^n*a+q*R_n(P). Induction over the stated block order proves the identity, including the two top lanes. No positivity, guard, selector exclusivity, geometric-series division, P!=1 assumption or native semantics is used.

For the left and output packs, retain exactly the high Horner rows down to lane m, giving high words L and O. Set

    Q=s_0+s_1*P+...+s_(m-1)*P^(m-1),
    left=P^m*L+Q, output=P^m*O+Q.

The shared Q is computed once by ordinary Horner in descending selector order. This is an exact identity on arbitrary signed selectors, not a deduction that AND distributes over addition.

## 2. All supporting powers and geometric sums are paid

Prepare exactly these records, where products by variable P and the masks all count:

    P2=P*P; P3=P2*P; P6=P3*P3; P7=P6*P;
    R2=P+1; R3=R2+P2; U3=P3+1; R6=R3*U3; R7=R6+P6;
    C2=(B-1)*R2; C6=(B-1)*R6; C7=(B-1)*R7.

This is8M4A. C_n is shared across the blocks of its size. P2 is exactly the parent's first native exponentiation row scale_square_0 and is moved here, so the old power stage has one fewer row. All prescribed ell>=68 start with this same square in the frozen binary-power grammar.

The only additional pair is(P^m,R_m). Use the prepared pairs for n in{2,3,6,7}. If the first three binary digits of m are110 or111, start at n=6 or7 respectively; otherwise its first two digits are10 and start at n=2. Consume the remaining binary digits. A doubling n->2n uses

    P2n=Pn*Pn; U=1+Pn; R2n=Rn*U

at2M1A. If the next bit is1, also compute

    R2n1=R2n+P2n; P2n1=P2n*P

at1M1A. Let d be the number of consumed bits and e their number of ones. Then gM(m)=2d+e, gA(m)=d+e. No previously generated scientific code or array is evaluated to establish this formula. Since m>=10 the indicated leading digits exist. In terms of L=floor(log2 m), the first case has d=L-2,e=popcount(m)-popcount(seed); the second has d=L-1,e=popcount(m)-1.

The complete new right-pack construction therefore costs(11+2m+gM)M+(6+m+gA)A: supporting records8M4A, geometric extension gM/gA, top tail1M1A, m blocks2M1A each, and the bottom selector block2M1A. The old right pack costs(ell-1)M+(ell-1)A. Its m separate letter_mask products and one aggregate_mask product become unused and are removed. Moving the already counted P2 also removes one multiplication from the old exponentiation stage. The net right-pack saving is(44+4r-gM)M+(47+4r-gA)A.

The old left and output selector prefixes together cost2mM+2mA. One Horner Q costs(m-1)M+(m-1)A and the two final joins cost2M2A. The net additional saving is(m-1)M+(m-1)A=(7+2r)M+(7+2r)A. Its P^m was already fully paid in the right-pack geometric extension; it is a shared computed polynomial, not a free variable power.

Adding both changes gives the announced complete ledger. For the saved full examples:

| r | m | ell | geometric seed | d,e | gM,gA | polynomial M,A | operations | witnesses |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1|10|68|2|2,1|5,3|298,590|888|102|
|2|12|74|6|1,0|2,1|330,634|964|108|
|4|16|86|2|3,0|6,3|403,728|1131|120|

These handwritten counts match the first emission's literal operation-label census. The three saved graphs contain2,983 rows. Only the separate independent source audit establishes their full row/binding coverage. The r=0 fallback stays unchanged at903 operations/96 witnesses.

## 3. Complete-source construction and domain preservation

The composer reads only the pinned complete quotient-pair JSON as inert records. It removes exactly aggregate_mask, the m letter_mask rows, every right_shift/right_join row, the left/output shifts and joins below index m, and the first scale_square_0 from its old position. The same scale_square_0 is emitted earlier. It retains all other rows verbatim except the three pack input references in the native header. Each old geometry/helper name removed from the executable source remains only a semantic lane expression in the receipt; it is represented by an explicit semantic_product descriptor, never as an uncomputed runtime port.

The paired action, centered-form and quotient append, comparison endpoints, finalizer, ordinary input, positive supplied list and fixed coefficient recipe are unchanged. Because all three new packed polynomials equal their parents for every integer runtime assignment, every native residual and consequently the entire final polynomial agree at exactly the same supplied tuple. The parent's positive-domain, guard, carry and completeness arguments therefore transfer identically; no new existential variable or map is introduced. No new degree claim follows without its own proof.

**Remark1 (geometric division is not used).** R_n is constructed by polynomial addition and multiplication. The shorthand(P^n-1)/(P-1) is not a legal uncharged runtime division and would not itself justify P=1. The recurrences above establish the identity for all integer P, including0 and1.

**Remark2 (shared selectors are paid, not independent).** Q and J*R_m are different polynomials. For m=2, s_0=1,s_1=0, Q=1 but J*R_2=1+P. The selector prefix may be shared between left and output; it cannot be replaced there by the right selector block. This illustrative identity check is handwritten and does not assert a complete compiler zero at m=2.

**Open question3 (further left-pack repetition, credited to root).** The unchanged high left pack also repeats the same two formed inputs for the plus/minus relator slots and repeats paired-letter history blocks. These can potentially be factored with all powers, shared sums and consumer joins paid. No saving for them is included in this draft. They need a separate exact schedule and complete-source audit.

All work here is handwritten algebra and inert source reading. No frozen, supplied, archived or predecessor helper is run/imported; no saved arithmetic source, coefficient array or degree is evaluated. The original metadata-only emitter constructed these records once and is now frozen with its first receipt. It must never be rerun or imported.

## 4. Disjoint ledger and frozen evidence

The independent mathematical challenge also derived the following disjoint count, without using the old-minus-new subtraction as its proof.

| Stage | M | A |
|---|---:|---:|
| Input, geometry, center and guard without separate masks | 8 | 134+12r |
| Centered form producers | 8r | 8r |
| All three packs, geometric support and shared prefix | 141+14r+gM | 128+12r+gA |
| Remaining prescribed power after the shared square | pc(ell)-1 | 0 |
| Native certificate | 33 | 31 |
| Paired action | 30 | 168 |
| Selected centers and quotient appends | 12r | 14r |
| Fused positive lift | 12 | 21 |
| Recurrence right sides | 6 | 14 |
| Certificate | 229+34r+pc(ell)+gM | 496+46r+gA |
| Residuals, squares and sum | 23 | 45 |

The emitter binds the removed row records, the relocated square, every retained literal row name, all three native-header substitutions and full compact source digests. It checks topological closure, unique definitions, liveness of every computed and supplied port, exact fixed-role equality, the unchanged finalizer and each complete M/A ledger. The receipt contains only the three full graphs, not additional formula-only examples. All old rows after the native header, including the complete quotient action and finalizer, stay literal.

Root derived the factorization and paid schedule, then read the entire fresh composer before its sole run. Aristotle and Riemann independently read the full proof draft and challenged every polynomial identity, seed branch and M/A count before that emission; both requested no correction. Aristotle additionally derived the disjoint ledger above. Their final review artifacts distinguish handwritten mathematics from the independent full source/binding audit. The source emitter performs metadata construction only and proves no polynomial identity by evaluation.

Frozen positive7_repeated_pack_compiler_root.py SHA256: 87208277efbd316332f2a9a0bb98b68ba1fe2cd3a416e63b98ff2982078d9e50.

Frozen positive7_repeated_pack_compiler_root.json SHA256: 2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a.

Its sole input is the committed quotient-pair receipt eda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674. The existing numerical universal84 frontier remains unchanged; this is a smaller symbolic positive7 compiler whose actual universal presentation and source degree are still open.
