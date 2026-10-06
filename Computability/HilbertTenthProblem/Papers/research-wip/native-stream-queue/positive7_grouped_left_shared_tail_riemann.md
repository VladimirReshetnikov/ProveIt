# Grouping the left pack around the shared tail power

The current grouped-right compiler admits a further exact local saving of **r multiplications and no additions** for every r>=1. It collects the repeated relator quartets, factors the two six-field history pairs together, and reuses the already paid right-tail power. The prospective r=1,2,4 totals are798,862,1003, instead of799,864,1007. This note proves the local identity, paid ledger and source-boundary obligations; it does not emit or certify a complete successor.

The source parent is `positive7_grouped_right_compiler_riemann.json`, SHA256 `4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c`. Its primary proof and frozen independent Pascal review certify the inherited construction separately. Here the saved rows are read only as inert records for names, operands, positions and consumers. The general collected route remains a handwritten source-grammar claim; no absent r>=8 example is manufactured.

## 1. Exact paid interface

Write m=8+2r, P=lane_scale, Pn=P^n, U2=1+P2, U6=1+P6 and G7=(1+P7)(1+P14). The source already pays P4,P12,P24,P28,U2,U6,G7 and

    H=P^(2m+36)=P^(4r+52).

The grouped-right proof supplies H through `group_right_tail_power`, with its explicit saved-fixture or generic support schedule. P24 is `group_right_P24`, or the existing geometric alias in the generic E24 branch. These are actual paid producers, not new powers to be credited without a consumer audit. They need to move earlier to serve the new left pack, with no change of expression or count.

Retain the existing history producer and its three exits:

    B7 = left_history_join_1,
    B6a = left_history_join_2,
    B6b = left_short_history_b.

Their meanings are, respectively, the packed blocks(H1,H2,H3,H4,H5,H6,H7), (H2,H3,H4,H5,H6,H7), and(H1,H2,H3,H4,H5,H7). Retain the already paid tail V=DP+S=`left_high_tail`. Retain every existing `left_form_pair_j` producer. With indices0,...,r−1, write its output p_j.

In the uniform center route p_j=A_(j,1)+P*A_(j,2), implemented by the retained uncentered pair and common correction. In the collected route p_j=L_(j,1)+P*L_(j,2), and retain the paid correction

    Gamma=W*P28*R_(4r), where W=center_word.

Its source exit is `common_center_correction`. Its producer uses W*P12*(Pm+P8)*(Rm−R8); the common-center proof establishes its displayed meaning without division. Uniform uses no Gamma and pays no zero-addition row. All input forms, common-center producers, B7/B6a/B6b, supporting powers and V lie outside the arithmetic replacement count below.

## 2. Exact identity and paid schedule

Define the collected relator word

    Q=sum_(j=0)^(r−1) p_j*P^(4j).

Compute it by descending Horner steps with base P4, starting at p_(r−1). This costs(r−1)M+(r−1)A, including zero steps at r=1.

The parent starts a quartet accumulator at V, then appends each repeated two-form block with

    acc <- P4*acc+U2*p_j.

Induction by hand on this recurrence gives P^(4r)*V+U2*Q. The next parent seven-block join gives P28 times that word plus G7*B7. Its collected route adds Gamma at this point. The following two six-field joins give the exact identity

    L = H*V + U6*(B6a+P12*B6b)
        +P24*(G7*B7+P28*U2*Q [+ Gamma]).                 (1)

The bracketed addend occurs only for the collected route. Indeed P12^2=P24, P24*P28=P52, and P52*P^(4r)=H. Expanding the two final parent joins gives(1) directly. This is an identity of integer polynomials. It holds at P=0,1 and negative P, without selector, positivity, carry, divisibility or zero-locus assumptions.

After the Horner producer, the uniform route pays exactly these eleven records:

    t_forms = U2*Q;                  s_forms = P28*t_forms;
    t_seven = G7*B7;                 b_high = t_seven+s_forms;
    t_high = P24*b_high;
    t_six = P12*B6b;                 b_low = B6a+t_six;
    t_low = U6*b_low;
    t_tail = H*V;                    b_partial = t_low+t_high;
    L = b_partial+t_tail.                                  (2)

They cost7M+4A. The collected route adds `b_restored=b_high+Gamma` and uses b_restored instead of b_high in t_high. That one addition replaces the parent's existing `common_center_restored` addition; the Gamma producer is retained. Hence it does not change the saving.

The parent cut has2rM+rA in its repeated-form/accumulator triples, followed by6M+3A in the nine seven/six history-join records. The new cut has(r−1)M+(r−1)A for Q and7M+4A for(2). Thus

    old: (2r+6)M+(r+3)A,
    new: (r+6)M+(r+3)A,
    saving: rM.                                           (3)

For the collected route add1A to both cuts for the restoration row. Every pair producer and the entire existing center correction remain charged outside this cut. Moving existing support rows costs no additional arithmetic but does not delete their charge.

## 3. Complete local fanout in the three saved graphs

The prescribed old cut contains every `left_form_repeated_j`, `left_form_high_shift_j`, `left_form_high_join_j`, and the nine records

    left_seven_repeated, left_seven_high_shift, left_seven_high_join,
    left_six_repeated_b, left_six_high_shift_b, left_six_high_join_b,
    left_six_repeated_a, left_six_high_shift_a, left_six_high_join_a.

Independent inert scans of the three complete saved source arrays found exactly one external arithmetic consumer of the entire cut:

    left_selector_shift = left_six_high_join_a * selector_power.

The only active metadata occurrence outside `source` and the explicitly historical parent-splice record is `ports.high_left_pack=left_six_high_join_a`. Reusing that final exit name for L in(2) preserves both consumers. No other removed intermediate is an active computed port, comparison side, semantic lane component or witness. Every other arithmetic consumer of a cut name is inside the cut.

| r | Old cut M/A | New cut M/A | Old cut rows | New cut rows | Prospective full M/A | Total |
|---:|---:|---:|---:|---:|---:|---:|
|1|8/4|7/4|12|11|247/551|798|
|2|10/5|8/5|15|13|273/589|862|
|4|14/7|10/7|21|17|332/671|1003|

The zero-based source cut positions are230–241 for r1;250–252,256–267 for r2;304–306,310–312,316–318,322–333 for r4. The sole external consumers are at positions385,424,515 respectively. These are record positions in the pinned parent, not text line numbers or evaluated executions.

The existing right support rows to move are positions354–355,388–390,470–473 respectively. Their exact names are P24 and H in r1; P24,`group_right_m18`,H in r2; P24,P18,`group_right_m18`,H in r4. Their operands are all available in dependency order immediately before `left_high_tail_shift` at positions225,245,299. In particular P12 is the port alias geom_P12 in r2, not a resurrected old register. A static availability scan passed for all three moves. The same source-grammar ordering works generically: the geometric extension and all left-support powers precede V, and the H support uses only Pm,P12,P6 and its own earlier support products. Geometric P24/P18 aliases, when present, remain earlier still.

The pair, history and power producers stay live: their exits feed Q or(2), and the moved P24/H retain their existing right/native consumers. In r1 Q is the existing p0 alias; the inherited geometric P4 is still live elsewhere. For r>=2 P4 feeds the new Q Horner shifts. The U2 factor is used once, U6 once, and G7/B7/P12/P28/V all remain needed. This is a cut-boundary/liveness argument, not a claim that a new complete graph has been constructed or audited.

For a general collected graph, include `common_center_restored` in the old cut, retain the Gamma producer, and redirect its one paid restoration into(2). Its old intermediate could not remain an active output, but its only arithmetic use in the inherited grammar is the deleted `left_six_high_shift_b`. A future composition must replace the old parent splice metadata or mark it explicitly historical; it must not treat historical removed-name lists as live computed bindings.

## 4. Conditional whole-source consequence and boundaries

Subtracting(3) from the frozen grouped-right proof gives the following prospective general full counts, with the same geometric costs and indicators:

    uniform: (219+27r+gM−A−B−D18−E24)M+(508+40r+gA−B)A;
    collected: (222+27r+gM−A−B−D18−E24−eta)M
               +(512+39r+gA−B−eta)A.                       (4)

Subtract the inherited fixture adjustment f(1)=3,f(2)=2,f(4)=1 from the M term where applicable. The resulting uniform total is727+67r+gM+gA−A−2B−D18−E24−f(r); the collected total is734+66r+gM+gA−A−2B−D18−E24−2eta, with f=0 in its range. In the conditional unpruned r>=151 regime this is at least151 further saved multiplications. No numeric universal relator list is assumed.

If a complete composition verifies the stated fanout, ordering and metadata obligations, the same packed left polynomial and unchanged other packs imply the same entire final polynomial on the same tuple. The inherited96+6r positive witnesses,23 comparisons, fixed6+15r roles, gamma addition exception and all guard/native domain proofs would transfer. No new carry argument is needed. These are conditional consequences of the exact local identity; full successor source coverage is still an open task.

**Remark1 (tail cannot be put inside the repeated factor for free).** A tempting shortcut is to initialize Q at V, run the same P4 Horner loop, and multiply that whole result by U2. It multiplies the required high-tail contribution by an extra U2. At r1,P1,V1,p0=0, with all history blocks zero, the correct high word is1 while this shortcut gives2. This is a local all-integer cut counterexample, not an assertion about a full native positive zero. Equation(1) keeps H*V separate.

**Remark2 (a valid weaker factored schedule).** Expanding the P24 parentheses and paying a separate P52=P24*P28 would give a valid schedule with one extra multiplication, saving only r−1. The nested formula(2) avoids that new support product. This does not erase the valid weaker identity or claim that the present schedule is optimal.

**Open question1 (complete source, credited to root's task).** Compose this cut into the frozen grouped-right compiler, move the paid support rows without duplicating their cost, preserve the old final exit, audit all successor rows/metadata/roles and retain both uniform and collected source-grammar scopes. No composer has been emitted or run in this note. Further algebraic minimization and numerical universal instantiation remain separate questions.

The work here is handwritten algebra and inert source-record inspection only. No supplied/frozen helper was executed or imported, no scientific array was evaluated or degree-propagated, and no build or repository mutation occurred. Root read the complete114-line mathematical draft and passed the identity, paid ledgers, saved r1 alias, collected Gamma relocation, conditional whole-source scope and both retained remarks. Pascal independently read the same full draft and passed the complete handwritten identity/count argument, including the four final sums, both center routes and all-r subtraction; he did not claim an additional source-record audit.

This local proof and its byte/static-boundary receipt are now frozen after those challenges. Root subsequently assigned a separate original composer draft; its text is being preflighted and it has not been run. No successor array has been emitted or independently audited at this local freeze. Later complete-source evidence must resolve that question downstream without rewriting this note. Final edits after the hand challenges change only this status/provenance.
