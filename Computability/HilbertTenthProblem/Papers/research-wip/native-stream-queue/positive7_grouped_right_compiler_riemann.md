# Complete positive7 grouped right-pack compiler

The grouped right-pack construction replaces the common-center parent's paid right-block loop and native power chain. With the three additional fixture specializations proposed by root, the complete saved r=1,2,4 sources cost **799,864,1007 operations**, respectively. Their general unspecialized schedule saves at least 2r+5 multiplications and no additions. The same final polynomial, ordinary input,96+6r positive witnesses,23 comparisons and6+15r fixed roles are preserved by the identities below.

This primary proof accompanies a fresh original metadata-only composer, `positive7_grouped_right_compiler_riemann.py`. After root and Pascal each fully preflighted its 298 lines, the exact original composer ran once and passed its record-only checks. Its first receipt contains the complete three sources with the counts below. The emitter and first receipt are permanently frozen; independent literal-source review is separate. No numerical universal relator presentation, degree bound or new general84 bound is claimed. The r>=151 floor belongs only to the retained unpruned embedding recipe, whose concrete fixed data remain a separate task.

## 1. Exact predecessor and private replacement

The only source input is the frozen common-center JSON SHA256 `ff634059250ac399883ae3311a81354204a84be82b6ae973983e2e9e95b7d6db`, first published at commit d2b9e11c06ea6f4bb914dfb9875939fab07bf6ed. The [local grouped-right proof](positive7_grouped_right_pack_riemann.md), SHA256 `2f3832c6537e82ee4f2c016b2cc05729a199125c68e1e82c9b83e149f990a31a`, is frozen and independently hand-challenged by root and Pascal. The present source realizes that schedule, with the separately proved fixture sharing in Section 3.

Set m=8+2r, ell=62+6r and P=lane_scale. Write Pn=P^n and Rn=sum_{k=0}^{n-1}P^k. The source already supplies P2,P6,P7,P12,P28,Pm and R2,R6,R7,Rm. P12 is accessed through ports.left_support_P12, which already resolves the geometric alias in the seed6 case. The retained tail is

    tail=height_mask*(J+P)=(D-1)*(J+P).

The old right-block widths are 6 four times, then 7 four times, then 2 exactly 2r times, indexed from the low end. Its descending recurrence is

    acc <- P_width*acc + C_width*selector_i,
    C_width=cell_mask*R_width=(B-1)*R_width.

The removed cut consists of the three C_width producer rows, all m right_block triples, and the private native power chain. It costs (23+4r-C)M+(8+2r)A, where C is the parent's prefix10011 alias indicator. Cut-row guards compare every old definition with these prescribed literal records; the emitter does not infer values by running the records.

Every old C_width consumer is a deleted lower product. Every nonfinal block join feeds the next deleted shift. The cut has precisely two external arithmetic uses: right_block_join_0 in right_selector_shift, and native_shared_scale in pell_q. The new terminal rows reuse those two exit names after removing their old definitions. Consequently every outside source row, including the whole64-row native certificate and68-row finalizer, remains literal. The source identity is established by the mathematical proof, while record equality and fanout closure establish its composition.

## 2. Generic grouping and joint power identity

Build three selector polynomials by descending Horner multiplication, using only the paid P6,P7,P2:

    Q6=sum_{i=0}^{3} selector_i*P^(6i),
    Q7=sum_{i=0}^{3} selector_(4+i)*P^(7i),
    Q2=sum_{i=0}^{2r-1} selector_(8+i)*P^(2i).

They cost (2r+5)M+(2r+5)A. Grouping the old equal-width runs gives the all-integer polynomial identity

    high=cell_mask*[R6*Q6+P24*(R7*Q7+P28*R2*Q2)]
         +P^(2m+36)*tail.                                    (1)

The tail exponent is 24+28+4r=2m+36. The ten reconstruction rows are exactly seven products and three additions: three Rn*Qn products; shift the Q2 contribution by P28 and add the Q7 contribution; shift by P24 and add the Q6 contribution; multiply by cell_mask; form H*tail; add the two parts. The exit is right_block_join_0. The old outer joins packed_right=Pm*high+J*Rm and both other native packs remain unchanged.

For the generic schedule, let D18 indicate binary m beginning1001 with at least five bits, and E24 indicate prefix1100 with at least five bits. Use the already computed geom_P18 or geom_P24 exactly in those cases. Otherwise pay P18=P12*P6 or P24=P12^2. Then

    Y=Pm*P18; H=Y^2;
    native_factor=Pm*P2; T=H*native_factor.                  (2)

Thus H=P^(2m+36) and T=P^(3m+38), exactly the inherited native scale. This costs4-D18-E24 shared support products and2 final native products. The generic new cut is (18+2r-D18-E24)M+(8+2r)A, saving

    (2r+5-C+D18+E24)M, and0A.                              (3)

C implies D18, so this is at least2r+5M. The geometric extension's increasing prefixes prove the precise aliases; m=18 supplies P18, while m=12 stops at P12 and does not supply P24. These facts are source-grammar proofs, not evaluation of saved arithmetic instructions. No r>=8, C, D18 or E24 complete fixture is invented in the saved packet.

## 3. Additional paid fixture specializations

Root found the following improvements before the original composer was run. Riemann and Pascal independently checked their identities and the actual retained power names. The generic schedule remains valid and remains the general-r construction; these are explicit fixed-r choices.

* **r=1,m=10.** The required H is P56, so H=P28^2 uses one product. The native factor P^(m+2) is the existing P12. Paying P24=P12^2, H=P28^2 and T=H*P12 costs3M total, saving3M against generic(2). No P18 or Y is produced.
* **r=2,m=12.** Form Y=P28*P2=P30 and H=Y^2=P60. The native factor is the existing P14. Paying P24,Y,H,T=H*P14 costs4M, saving2M. P12 is the existing geom_P12 port; P14 and P28 have their retained left-support names.
* **r=4,m=16.** The generic new P18 is also P^(m+2). Retain P24,P18,Y,H and form T=H*P18. These5M save1M by removing the duplicate native-factor product.

All three saved cases therefore pay one final native product. Their shared support costs2,3,4 products respectively, and their total joint costs are3,4,5. No other small-r specialization is assumed. Define f(1)=3,f(2)=2,f(4)=1 and f(r)=0 otherwise; the actual saved saving is(3) plus f(r)M.

## 4. Whole ledger and actual record partition

Retain the common-center parent's A=prefix101, B=prefix1110 with at least five bits, eta=prefix100, and geometric-extension costs gM,gA. The generic unspecialized full counts become

    uniform: (219+28r+gM-A-B-D18-E24)M+(508+40r+gA-B)A;
    collected: (222+28r+gM-A-B-D18-E24-eta)M
               +(512+39r+gA-B-eta)A.                       (4)

The common-center route choice remains uniform for1<=r<=7 and collected forr>=8. Subtract f(r)M for the three adopted fixtures; f=0 throughout the requested r>=151 regime. Generic total operations are727+68r+gM+gA-A-2B-D18-E24 and734+67r+gM+gA-A-2B-D18-E24-2eta respectively. Subtract23M45A from any full ledger for its certificate. The r0 fallback is inherited literally and receives none of these changes.

For an independent disjoint-stage check, the new generic pack stage totals are uniform(105+11r+gM-A-B-D18-E24)M+(90+11r+gA-B)A, or collected(108+11r+gM-A-B-D18-E24-eta)M+(94+10r+gA-B-eta)A. Its native stage is2M. The fixtures save an additional2,1,0M in packs and1M in the final native stage. All input, decoding, action, recurrence and finalizer stages retain their parent's counts.

| r | Deleted cut | Literal outside | Inserted cut | Certificate M/A | Full M/A | Full total |
|---:|---:|---:|---:|---:|---:|---:|
|1|37|772|27|225/506|248/551|799|
|2|43|832|32|252/544|275/589|864|
|4|55|966|41|313/626|336/671|1007|

These counts partition all2670 successor rows as2570 literal outside rows plus100 inserted rows. All135 parent cut rows are removed; no outside row is rewritten. The two reused exit labels belong to newly inserted definitions, not retained definitions. Every supplied witness and fixed-role occurrence remains literal: gamma is the unique fixed role in an addition, and all other5+15r roles occur once each in paid multiplication.

## 5. Emission, active metadata and exact domain

The composer only reads the pinned parent JSON as inert records. It checks every old cut row, all outside cut consumers, stage boundaries, operation labels, unique names, operand availability, output liveness and active metadata bindings. It never evaluates a saved arithmetic instruction or interprets a fixed coefficient. Existing r1/2/4 are the only accepted example list.

The original shared_pack_powers_and_coefficients stage loses C2,C6,C7 and is renamed shared_pack_powers_and_repunits, costing5M4A. A new grouped_right_pack_and_joins stage inserts the shared support and selector Horner rows before right_tail_sum, retains that tail, inserts the high reconstruction before right_selector_shift, and retains all outer joins. The original native stage is replaced in place by native_scale_from_right_tail_power. This ordering puts all existing power prerequisites before their uses.

The active native_scale_products field records the final link cost1 in every saved example; grouped_right_support_products records2/3/4 and joint_right_native_products their sum3/4/5. The top-level general grammar separately states costs2,4-D18-E24 and6-D18-E24. The old parent_binary_power_cost field remains explicitly historical. No stale4-C native-cost claim remains active.

The old common_center_splice is replaced by grouped_right_splice, whose immutable parent reference preserves the earlier provenance. The new receipt lists every deleted and inserted record, every literal outside name, the two preserved exits and their consumers, source hashes, stage renames, fixture choice, support rows, cut ledgers and allowed changed top-level fields. All other fields must compare literally with the parent, including ports, semantic descriptors, supplied lists, fixed data recipe, comparisons and r0 fallback. No centered semantic form is reinterpreted.

All relevant identities hold in the integer polynomial ring, including P=0, P=1 and negative P; they use no division or zero-locus hypothesis. The final polynomial is therefore identical on the same tuple under the inherited linked fixed recipe. Positive zero equivalence, ordinary-input projection, witness count and guard/native domain proofs transfer unchanged. This is stronger than a projection-only reduction and does not require a fresh carry argument.

## 6. Retained boundaries and validation status

**Remark1 (valid generic fixture schedule retained).** The frozen local schedule predicted802/866/1008 operations for these fixtures. That schedule is valid and fully paid; root's subsequent3/2/1M power sharing yields the stronger complete-source counts here. No frozen count or proof is silently rewritten.

**Remark2 (no uncharged powers or coefficients).** Grouping a run does not supply its total-shift power for free. The proof pays H and P24 explicitly, reuses P18/P24 only under their exact availability conditions, and pays the outer cell_mask product after removing the three C_width producers. The preliminary weaker schedule retaining C_width remains a valid2M-worse alternative in the local note.

**Remark3 (historical source boundaries).** The inherited gamma multiplication overstatement, missing short-prefix power aliases, and center-deletion counterexample remain in their frozen notes. This source retains the corrected fixed-role split, exact power-prefix conditions and complete common-center compensation. Small fixtures are not asserted to instantiate the universal presentation.

**Open question1 (concrete universal data and further bounds).** Materialize the universal presentation and named images before assigning a numerical universal r or matrix alphabet. The present general collected grammar applies conditionally to r>=151 for the retained unpruned recipe; it supplies neither that list nor a minimality or source-degree theorem.

**Execution and review status.** Root and Pascal each read all298 lines of the wholly original composer before authorizing its sole metadata-only run. That exact source ran once, exited successfully and reported2670 records with full counts799/864/1007. Source, first receipt and first-run log are permanently frozen. No composer/helper replay, scientific sampling, source arithmetic, coefficient evaluation, degree propagation or build occurred. Root owns publication and Git. Root then read the full primary proof and passed its identities, fixture refinements, disjoint ledgers, record partition, metadata and final-polynomial scope without correction; root also inspected the first receipt as inert data. This primary note is now frozen. Full independent literal-row review remains pending at this freeze and must be bound by a separate downstream review; the author does not claim that review as completed.

Frozen emitter SHA256: `4ce81f4690fed2d6da8564c0fb804f200c74d4032ca36b8e1153c7877091d9a9`.

Frozen first receipt SHA256: `4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c`.

Frozen first-run log SHA256: `3bed8d52de33e11f636fcd3ba299767cf5ab341e01a9f034dad59a7c0399dbe2`.
