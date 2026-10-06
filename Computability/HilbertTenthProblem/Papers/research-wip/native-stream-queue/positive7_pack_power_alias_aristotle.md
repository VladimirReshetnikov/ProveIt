# Paid aliases for repeated positive7 pack supports

For every integer r>=1, the frozen joint high-left/native-scale compiler has at least one multiplication and one addition whose values were already computed in its retained geometric extension. Removing those duplicate records and rebinding their consumers preserves the entire integer polynomial, including its positive ordinary-input zero set. This is a local source-cut theorem and a prospective ledger, not a newly emitted complete compiler. All existing source bytes and published counts remain unchanged.

Root requested this investigation after Riemann observed the first duplicated power and the extra P5 at r=1. This note proves the exact branch classification for the displayed power and plus-one supports, identifies the additional P28 and native P19 cases, and charges every surviving producer. It does not change the separate shared-decoder proposal or combine its savings.

## 1. The retained geometric grammar

Put m=8+2r>=10. The frozen parent chooses seed6 or seed7 if the binary expansion of m begins110 or111, respectively, and otherwise seed2 on the leading10. The corresponding paid initial power is P^s and repunit is R_s=1+P+...+P^(s-1). For each remaining binary digit epsilon, its original handwritten grammar is

    geom_P(2n) = Pn*Pn;
    geom_factor_(2n) = Pn+1;
    geom_R(2n) = Rn*geom_factor_(2n).

If epsilon=1, it also computes

    geom_R(2n+1) = geom_R(2n)+geom_P(2n);
    geom_P(2n+1) = geom_P(2n)*P.

Then n becomes2n+epsilon. These are the actual retained producer records, not new free powers. An induction on the binary prefix proves their power values and geometric-sum identities in Z[P]. All exponents produced are at most m. No positivity or dyadic assumption is used in these identities.

Because m>=10 has at least four binary digits and every seed consumes only two or three, at least one geometric doubling is performed. Its records include

| Seed | Retained power | Retained plus-one value |
|---:|---|---|
|2|geom_P4=P4|geom_factor_4=1+P2|
|6|geom_P12=P12|geom_factor_12=1+P6|
|7|geom_P14=P14|geom_factor_14=1+P7|

The complete geometric extension occurs before the new left-support stage and before the shared native-scale stage. Thus each displayed value is both paid and topologically available when the duplicate is encountered.

## 2. Exact alias classification within the displayed supports

Use the following indicators of the binary expansion b(m):

    A = 1 if b(m) begins101, otherwise0;
    B = 1 if b(m) begins1110 and has at least five digits, otherwise0;
    C = 1 if b(m) begins10011, otherwise0.

They are pairwise disjoint. The length qualification for B matters: m=14 has binary1110 but has only one post-seed doubling. Since m is even, the C case automatically has at least six digits; its first example is m=38.

The following table lists every match between a retained geometric producer and the five new left powers, their four plus-one factors, or the new native P19 producer.

| Duplicate record to remove | Existing record to use | Exact condition | Saved operation |
|---|---|---|---|
|left_support_P4|geom_P4|seed2|M|
|left_pair_factor_2|geom_factor_4|seed2|A|
|left_support_P5|geom_P5|A=1|M|
|left_support_P12|geom_P12|seed6|M|
|left_pair_factor_6|geom_factor_12|seed6|A|
|left_support_P14|geom_P14|seed7|M|
|left_pair_factor_7|geom_factor_14|seed7|A|
|left_support_P28|geom_P28|B=1|M|
|left_pair_factor_14|geom_factor_28|B=1|A|
|native_shared_P19|geom_P19|C=1|M|

Here powers and plus-one values are polynomial identities, not necessarily literal operand-record equality. In particular left_support_P5=P2*P3 agrees with geom_P5=P4*P, native_shared_P19=P12*P7 agrees with geom_P19=P18*P, and the addition operands1+Pn and Pn+1 may be reversed.

To prove completeness of this table for these particular targets, follow the growing binary prefix. The only possible power4 is the first doubling of seed2; power5 is its immediate odd append and therefore requires the next bit1. Power12 is the first doubling of seed6, and power14 the first doubling of seed7. Power28 requires a prefix14 followed by another bit: hence the seed7 branch, next bit0, and at least one further bit. Power19 requires the odd append to18, hence the prefix10011. A branch beginning10 cannot later acquire prefix110 or111, and conversely. Once the prefix exceeds a target, later doubled or appended exponents cannot return to it. The factors1+P2,1+P6,1+P7,1+P14 occur exactly when the corresponding geometric doubling4,12,14,28 occurs.

The other new native powers have exponents m+19,2m+38 and3m+38. They exceed m and cannot equal any retained geometric power in Z[P]. There is no assertion that this table exhausts arbitrary arithmetic sharing elsewhere in the compiler. It exhausts these named later support values against this particular earlier geometric grammar.

Consequently the exact deletion tally for the table is

    delta_M = 1+A+B+C,     delta_A = 1+B.                 (1)

In particular1<=delta_M<=2 and1<=delta_A<=2. The guaranteed uniform saving is1M+1A. This guarantee is sharp for this table, for example at m=12 or16. Higher cases save3 operations if A=1 or C=1, and4 operations if B=1. No division, new multiplication or runtime case-selection is introduced: the branch is fixed by the compiler's fixed integer r.

## 3. Fanout and source-boundary obligations

The frozen joint emitter copies the entire geometric prefix before emitting any left support. The alias map must be applied to every later operand, including support-to-support and support-to-native edges. In its actual grammar the affected arithmetic consumers are:

| Removed name | Consumers requiring substitution when that alias is used |
|---|---|
|left_support_P4|all left_form_high_shift_j|
|left_pair_factor_2|all left_form_repeated_j|
|left_support_P5|left_short_history_correction|
|left_support_P12|left_six_high_shift_b, left_six_high_shift_a, native_shared_P19 unless that record is itself removed|
|left_pair_factor_6|left_six_repeated_b, left_six_repeated_a|
|left_support_P14|left_support_P28 and left_pair_factor_14, unless those records are themselves removed|
|left_pair_factor_7|left_four_seven_factor|
|left_support_P28|left_seven_high_shift|
|left_pair_factor_14|left_four_seven_factor|
|native_shared_P19|native_shared_m_plus_19|

A complete implementation must also rebind computed-value metadata, notably ports.left_support_P12, rather than leave references to removed names. In the C case only three new shared-native-scale products remain; native_scale_products=4 is then historical parent data, not the new runtime count. The old stage counts, splice record, source hashes, static receipts and full counts likewise cannot be reused as successor assertions. The prescribed native T exit remains the same polynomial and no new supplied port is introduced.

Every retained alias target precedes all its new consumers. Aliasing can only redirect edges backward in this ordering, so the replacement introduces no cycle or forward reference. The targets were already live, and each removed record has a retained equal producer. A fresh complete structural audit must still verify every source record, every operand substitution, exact fixed-role and witness sets, topology, remaining liveness, finalizer and comparison bindings. The static inspection supporting this note is limited to the displayed families and their exact consumer names in the three saved examples, together with the full general emitter grammar; it is not a new whole-source audit.

All equalities hold for every integer P, including0,1 and negative values, and for arbitrary integer values of the other original supplied coordinates. Substituting the aliases therefore preserves each affected consumer polynomial inductively, then all downstream native residuals, actions, history comparisons and the final polynomial. Under the inherited valid linked fixed recipe the same ordinary positive input and exactly the same positive supplied witness tuples remain zeros. The integer argument is stronger than projection equivalence and requires no renewed guard or history induction.

## 4. Paid predictions and exact examples

The frozen parent count is

    (224+33r+gM)M+(504+44r+gA)A.

For a complete successor implementing precisely the table, the predicted count is

    (224+33r+gM-delta_M)M+(504+44r+gA-delta_A)A,           (2)

with unchanged23 comparisons,96+6r positive witnesses and6+18r fixed roles. The certificate loses the same rows; the finalizer remains23M45A. Formula(2) is conditional on a separately emitted and audited complete replacement. It does not lower any count attributed to the unchanged frozen parent.

| r | m and binary | Aliases in addition to the first power/factor pair | delta_M,delta_A | Predicted M,A,total |
|---:|---|---|---|---|
|1|10=1010|P5|2,1|260,550,810|
|2|12=1100|none|1,1|291,592,883|
|4|16=10000|none|1,1|361,682,1043|
|3|14=1110|none; no second doubling|1,1|parent minus1M1A|
|10|28=11100|P28 and1+P14|2,2|parent minus2M2A|
|15|38=100110|native P19|2,1|parent minus2M1A|

These are handwritten binary-prefix and ledger substitutions, not evaluations of saved arrays. The initial powers-only observation gives the weaker valid1M guarantee and the powers-only example savings2M,1M,1M. The addition aliases strengthen it.

**Review remark 1 (retained weaker claim, credited to Riemann).** The initial first-doubling observation guaranteed one duplicate multiplication, with a second at r=1 from P5. That statement remains true; the plus-one factors and the later P28/P19 branches extend it. No previously frozen bound is silently changed.

**Review remark 2 (prefix length and fixed-data boundaries).** The unqualified statement “prefix1110 supplies P28” would be false at m=14: the extension ends after producing P14 and no P28 exists. The correct B definition includes a further digit. Equality at a special numerical P such as0 or1 also does not justify a uniform source alias between different monomials. The table uses polynomial identities with actual retained producers, not a special-value or uncharged-port argument.

**Open question 1 (complete splice, credited to root).** Emit and independently audit a complete source realizing these aliases, including casewise fixed grammar, all fanout and computed-port metadata. The local theorem does not certify a changed source array. Further sharing outside the named support families, interaction with the separate shared-decoder proposal, degree and circuit minimality are not decided here.

## 5. Provenance and execution scope

The entire frozen89-line joint primary and146-line joint emitter were read as inert text. The entire178-line earlier repeated-pack emitter was also read; its geometric grammar is the proof source. This note additionally inspected only named geometric/support/native-power records and their consumer names, ports and branch metadata in the joint receipt's three saved examples. Every saved record remained inert. The predecessor's independent whole-source review remains separate inherited evidence. Exact byte pins and these read scopes are in the metadata companion.

Root independently read and passed the full local proof, exact branch classification, ledger and boundary statements. Pascal independently read the full note and both complete emitter texts, verified the binary-prefix classification and every displayed consumer family, and confirmed the computed-port and native-scale metadata obligations. Neither reviewer requested a correction. Their challenges do not replace the still-pending complete successor emission and literal source audit.

No supplied, archived, committed, predecessor or frozen helper was run or imported. No saved source or coefficient array was evaluated, no degree was propagated, and no scientific sampling, emitter or build was executed. Fresh original metadata work only hashed bytes and inspected record labels and operand references. All new files are under/tmp; no repository/Git or frozen source bytes were altered.
