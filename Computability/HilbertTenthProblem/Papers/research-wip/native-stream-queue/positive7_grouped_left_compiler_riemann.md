# Complete positive7 compiler with grouped left joins and a shared tail

The complete saved r=1,2,4 compilers now cost **798,862,1003 operations**, respectively. The new left-pack schedule saves exactly r multiplications and no additions from the grouped-right parent. It uses already paid P24 and H=P^(4r+52) producers, moving their records earlier rather than duplicating them. The same final integer polynomial, ordinary input,96+6r positive witnesses,23 comparisons and6+15r fixed roles are preserved.

The original249-line metadata-only composer was written by Riemann and fully read by root before execution. After the local proof froze, its pending proof pin was the sole code change; root checked that final hash and ran the composer exactly once. It passed and produced the first frozen receipt containing2,663 complete records. This proof describes that result. A separate original whole-source audit is still pending at this primary freeze; neither the composer nor its receipt may be replayed, imported or edited. No scientific values, coefficients or source degrees were computed.

## 1. Frozen predecessor and exact paid cut

The sole source-array input is `positive7_grouped_right_compiler_riemann.json`, SHA256 `4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c`. Its full source review is separately frozen in `review_positive7_grouped_right_compiler_pascal.md`. The new [local proof](positive7_grouped_left_shared_tail_riemann.md), SHA256 `a555ae04bfeb8d9ca3dbbf5bdb7551b22f7e2390d41d88050cf1cfaef4e9479f`, has full independent handwritten challenges by root and Pascal. Its receipt records exact inherited cut rows, external consumers and support availability. It does not itself claim an emitted successor.

Let m=8+2r, P=lane_scale, Pn=P^n, U2=1+P2, U6=1+P6 and G7=(1+P7)(1+P14). The source supplies P4,P12,P24,P28,U2,U6,G7 and H=P^(2m+36)=P^(4r+52). Retain the paid history words

    B7=left_history_join_1,
    B6a=left_history_join_2,
    B6b=left_short_history_b,

with blocks(H1,...,H7), (H2,...,H7), (H1,H2,H3,H4,H5,H7), respectively. Retain V=left_high_tail=DP+S and every already computed pair p_j=left_form_pair_j. In the actual saved uniform route p_j is the centered pair A1_j+P*A2_j, supplied by the unchanged common-center correction.

The removed cut is precisely the3r repeated-form/accumulator rows named `left_form_repeated_j`, `left_form_high_shift_j`, `left_form_high_join_j`, followed by the nine seven/six-block product-and-join rows ending at `left_six_high_join_a`. Its cost is(2r+6)M+(r+3)A. All form producers, their fixed coefficient roles, tail/history words, supporting powers and common-center arithmetic remain outside this cut and remain paid.

The complete parent-array scan finds one external arithmetic consumer of the cut: `left_selector_shift` consumes its final exit `left_six_high_join_a`. The only active metadata occurrence is `ports.high_left_pack` with that same name. Every other arithmetic use of a cut output lies inside the cut. The new final row reuses exactly that exit name after deleting its former definition. Every outside arithmetic record remains literal, including the complete64-row native certificate and68-row finalizer; nine of those literal records move in source order.

## 2. Exact integer identity and new records

Compute

    Q=sum_(j=0)^(r−1) p_j*P^(4j)

by descending Horner steps in P4, starting at p_(r−1). This pays(r−1)M+(r−1)A. At r1 Q is simply the existing pair alias, so no fictitious zero-step operation is introduced.

The old quartet accumulator starts at V and updates by P4*acc+U2*p_j. Hand induction gives P^(4r)*V+U2*Q. The seven-block join multiplies by P28 and adds G7*B7; the two six-field joins each multiply the higher word by P12 and add a U6-weighted block. Expanding those two final joins gives

    L = H*V + U6*(B6a+P12*B6b)
        +P24*(G7*B7+P28*U2*Q).                            (1)

The new source implements(1) with seven products and four additions after Q: U2*Q, P28 times that product, G7*B7, the upper sum, P24 times the upper sum, P12*B6b, the lower sum with B6a, U6 times the lower sum, H*V, and two final sums. Its eleven final records end in the preserved old exit. Combined with Q, the new cut costs(r+6)M+(r+3)A and saves exactly rM.

These are polynomial identities over the integers, including P=0,1 and negative P. The paid source power definitions impose P12^2=P24 and P24*P28*P^(4r)=H. No division, nonzero condition, positivity, selector exclusivity, carry induction or native zero is needed. Hence the same left packed word and unchanged remaining arithmetic preserve the entire final polynomial on the same supplied tuple under the inherited linked fixed recipe. Positive-zero equivalence and ordinary-input projection transfer without a new domain proof.

## 3. Moved powers, source order and stage accounting

The parent paid the following support in its right-pack stage:

* r1: P24=P12^2 and H=P28^2, two products.
* r2: P24=P12^2, Y=P28*P2 and H=Y^2, three products.
* r4: P24=P12^2, P18=P12*P6, Y=Pm*P18 and H=Y^2, four products.

The source moves these exact2/3/4 records, in their existing dependency order, immediately before `left_high_tail_shift`. Every operand is available there; r2 accesses P12 through the unchanged geom_P12 port alias. The moved powers keep their former names and all right/native consumers. Their former occurrences are removed, so each is still charged exactly once. The new Q/reconstruction rows are inserted at the old final left exit, after all retained pair producers. Unique names, forward operand availability and final-output liveness are checked over the complete emitted array.

The old `repeated_high_left_pack` stage becomes `grouped_high_left_pack_with_shared_powers`. Its product count changes by support_count−r; its addition count is unchanged. The right-pack stage loses precisely support_count multiplications. Every other stage is unchanged, including the final native scale product. Thus whole pack work decreases by rM even though the left stage itself can grow when it acquires shared support.

| r | Unmoved literal | Moved literal | Old cut | New inserted | Left stage M/A | Right stage M/A | Certificate M/A | Full M/A | Total |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1|785|2|12|11|23/18|19/14|224/506|247/551|798|
|2|846|3|15|13|27/21|21/16|250/544|273/589|862|
|4|982|4|21|17|32/27|25/20|309/626|332/671|1003|

The disjoint total partition is2,613 unmoved literal records,9 moved literal records and41 inserted records, giving2,663. All48 old cut records disappear. The9 moved records are not deleted/recomputed operations and the reused final exit is not a retained old definition. No outside operand is rewritten. All supplied values stay live; all6+15r fixed roles still occur once, with gamma the sole addition role and every other role a multiplication.

## 4. General collected route and whole ledger

The actual receipt contains only the supplied uniform r1/2/4 graphs. For the inherited collected route r>=8, the retained pair is uncentered and the old proof supplies

    Gamma=W*P28*R_(4r)
          =W*P12*(Pm+P8)*(Rm−R8).

Its producer remains fully paid, with the existing eta-dependent support aliases. The general replacement uses(1) with Gamma added inside the P24 parentheses. That one restoration addition replaces the old `common_center_restored` row, whose sole arithmetic consumer was the deleted first six-field shift. Add1A to both old and new cut ledgers. The saving stays rM. Moving generic P24/H support earlier is valid by the same source grammar: Pm and any geometric aliases precede the left stage, and P12/P6 precede V. No collected successor array or missing power-alias fixture is fabricated here.

Let gM,gA and A,B,D18,E24,eta have exactly their inherited geometric-prefix definitions. The general complete counts are

    uniform: (219+27r+gM−A−B−D18−E24)M+(508+40r+gA−B)A;
    collected: (222+27r+gM−A−B−D18−E24−eta)M
               +(512+39r+gA−B−eta)A.                       (2)

Subtract the inherited fixture correction f(1)=3,f(2)=2,f(4)=1 from the M term where applicable, with f=0 otherwise. The uniform total is727+67r+gM+gA−A−2B−D18−E24−f(r); the collected total is734+66r+gM+gA−A−2B−D18−E24−2eta. Subtract23M45A for each certificate. The r0 fallback remains the inherited903-operation/96-witness branch and receives no new construction.

As a disjoint check, the general pack stage totals become uniform(105+10r+gM−A−B−D18−E24)M+(90+11r+gA−B)A, or collected(108+10r+gM−A−B−D18−E24−eta)M+(94+10r+gA−B−eta)A. The generic native link remains2M. The saved fixtures retain the parent's additional2/1/0M pack reductions and1M native-link reductions. All other disjoint stages are inherited literally, yielding(2). In the conditional unpruned r>=151 regime this construction saves at least151 further multiplications; it does not supply a numerical universal presentation or an arithmetic lower bound.

## 5. Active metadata and retained boundaries

The first receipt replaces `grouped_right_splice` by `grouped_left_splice`, binding the immutable parent receipt instead of treating its old literal/deleted-name lists as current bindings. The new splice records every removed and inserted row, all moved records, every unmoved literal name, the preserved exit/consumer, old/new source hashes, insertion positions and exact field-change list.

The active support counters now read `shared_left_right_support_products=2/3/4` and `joint_pack_native_products=3/4/5`. The latter includes the still-paid single final native product. The obsolete right-only support counter names are removed; `native_scale_products=1` remains literal. The metadata does not claim these products are exclusive to the right pack after their new left uses.

The only other changed fields are source/stage/full/certificate counts and certificate prefix length. All ports, ordinary/supplied domains, comparisons, semantic centered-form descriptors, lane order, terminal alias, fixed data recipe, static role census and fallback remain identical. The original metadata program verifies active string bindings without interpreting semantic descriptors as uncharged gates. Fixed SAME-V coefficient preparation and the guard's dependence on ell are unchanged.

**Remark1 (false tail shortcut retained).** Multiplying a Horner word initialized at V by U2 would introduce an extra U2 on the tail. At r1,P1,V1,p0=0 and zero history blocks, it gives2 instead of1. This is a local integer-cut counterexample, not a full positive native zero. Equation(1) retains H*V separately.

**Remark2 (valid weaker schedule retained).** A separately paid P52=P24*P28 gives a correct but one-product-worse schedule. It would save r−1 rather than r. The nested expression avoids that extra producer; no optimality claim follows.

**Remark3 (frozen historical scope).** The local note's pending-composition question and the parent primary's pending-review wording remain unchanged. The parent's independent Pascal review already resolved the latter. This first emission resolves construction of the actual three local successor arrays, while independent full-row audit remains a separate downstream result. The local note's final-source preflight language concerns the still-unbound proof pin at that freeze; root had already read the full draft composer and then separately verified the final pin-only change. No frozen helper or earlier source claim is silently rewritten.

**Open question1 (remaining evidence and numerical scope).** Independently audit every saved new row, fanout, stage, fixed role and active metadata binding against the pinned parent and hand identities. Materialize the actual universal presentation and named matrix data before substituting a numerical universal r. General source degree, further optimization and missing collected saved fixtures are not certified here.

## 6. Sole-run provenance and evidence pins

Root fully preflighted the original249-line composer before authorizing execution. Riemann changed only LOCAL_PIN after the local proof/receipt froze; root checked that delta and final SHA256. Root then executed that exact original once, received PASS and permanently froze its source, first JSON and first-run log. Riemann did not rerun or import it. Ordinary source reading and fresh byte/metadata inspection after the run do not evaluate its arithmetic records. No supplied/frozen scientific program, coefficient evaluator, degree routine or build was run. Root owns all Git/publication actions.

Frozen composer:7d2d4bb215633afc340068a43913eb80b7396d3baa7427d2a3f8df679a0622af.
Frozen first receipt:f247d5f4b7f04a0fe14847b9dfe5db46c60b002c709dde71fd248e306868d8d1.
Frozen first-run log:c996faafb6c09939cd63baed9237fccd1b26c943d97f1a11619c765425ebcc06.

Root read the complete103-line mathematical draft and passed the exact identity, both center routes, stage moves, disjoint record partition, actual/certificate/general ledgers, support names and metadata/domain preservation without correction. This primary proof and its separate provenance receipt are now frozen; the only edits after that challenge record this status and review provenance. The first source receipt, composer and first-run log are unchanged. The independent complete source audit is being prepared separately; no completed audit is claimed at this freeze, and its later downstream review must retain this historical scope.
