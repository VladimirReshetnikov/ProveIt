# Held composition and validation boundary

## Exact source composition

Let P be the accepted partial-selector 216 source, whose ordered primitives and full register-machine control flow agree with the accepted dominated 217 source. The new submission factors the counter-field read out of common command dispatch and AX setup and into each command that actually needs it. Its explicit source recipe deletes the closed spans `[23,37)` and `[187,201)` and replaces each closed load span `[228,254)` and `[4659,4685)` by `walk11 ; (transfer3 ; load26)`. The latter is a closed 40-leaf source expression. The command bodies at paths `111`, `110101`, and `110100101` are then permuted by order `(2,1,0)`.

The own composition program first applies this recipe to the unchanged accepted 217 source and reproduces the submitted `frozen202.json` and submitted primary command-permuted source byte for byte. Applying the identical recipe to P yields the held source. It checks exact equality of the 4,751 ordered opcode/register rows and all 6,175 guarded edges against that independently calibrated command-permuted reference. Two different CFG resolvers agree. This supplies an identity-on-register-values bisimulation by ordinal between the two source programs, including the initial ordinal and halt instructions. No claim that the changed field-reader commands preserve the old unpermuted command semantics is needed: that transformation is the separately reviewed submission's compiler theorem.

The entire partial-selector subtree, including its state-172 context repair, remains unchanged as a source subtree. Its interval shifts from `[412,4586)` to `[398,4572)`, at path `1101001001110101`. Its two used zero branches are the unchanged intervals `[398,452)` and `[4560,4570)`. The other children remain live program subtrees; they are unused only by this partial selector.

Thus the held source inherits the submitted command compiler's ordinary consistency calibration. Connecting it to the held binary machine additionally requires the quantified primitive-runtime theorem and the calibrated blank startup; finite source equality alone does not provide either.

## Physical allocation and the two marker selectors

The physical allocation begins with the accepted partial-selector 216 table. It preserves all selected engine/helper rows except the explicit local81 repair. The old engine census used during allocation is an inherited synthesis filter, not a fresh proof about all internal values. A bounded MILP assigns the 22 changed source nodes to existing labels; the exact resulting table is frozen before any final acceptance checks. The solver finds 215 graph-reachable states by removing label224, with no fresh labels. It does not prove optimality over other sources or allocation policies.

The first marker fold retains:

- `69/0 = 0L213`, `69/1 = 1R31`;
- `213/0 = 0R92`, `213/1 = 1R90`;
- `92/0 = 0R104`, `90/0 = 0R105`.

The only incoming edges to69 are `53/1 = 1R69` and `100/0 = 0R69`. They retain the opposite predecessor markers that distinguish the two zero endpoints. Reallocating92/1 does not affect either three-step marker block, which reads92 only on zero.

The second fold retains:

- `164/0 = 0L201`, `164/1 = 1R98`;
- `201/0 = 0R195`, `201/1 = 1R196`;
- `195/0 = 0R150`, `196/0 = 0R77`.

The only incoming edges to164 are `135/1 = 1R164` and `205/0 = 0R164`. Thus its opposite predecessor markers remain valid. Both selector arguments are exact local whole-tape blocks after their stated incoming edges. Other ordinary decoder visits to the provider states still require their own source/runtime correspondence.

## Local81 repair

At state81 with current symbol zero, both the old `0L92` entry and new `0L111` entry take exactly three transitions, leave the tape unchanged, and move one cell right. If the predecessor symbol is zero, both end in123; if it is one, both end in21:

- old zero marker: `81 → 92 → 104 → 123`;
- new zero marker: `81 → 111 → 104 → 123`;
- old one marker: `81 → 92 → 107 → 21`;
- new one marker: `81 → 111 → 128 → 21`.

Only the current zero and predecessor bit are read. This is a two-case all-tape proof, not a bounded blank simulation. It frees92/1 for the new decoder assignment. The held finite audit independently checks both blocks from their literal rows.

## Alias correction and remaining checks

The original allocator's final global-node gate required state13 for the shared `(CD6,CC2)` node, because state13 works at every occurrence. Eight occurrences actually reach retained state108. Every one has the required `101` suffix, unchanged tape and head, and unchanged rows `108/0=0R21`, `108/1=0L10`. A separate finite local-entry reader validates these exact occurrences rather than replacing the table or weakening the tape-restoration condition. The first global-only rejection remains historical evidence.

The corrected finite audit walks every internal source prefix directly from dispatcher84, checks the unchanged known prefix tape, and verifies the exact reached logical role. It checks every leaf entry against the accepted literal action catalogue, with the proved local81 exception and the explicit108 context rule. The deterministic source/table reconstruction and dense-state renaming are also checked independently of the solver. None of these finite checks substitutes for the complete quantified runtime checker.

The remaining acceptance obligations are:

1. The inherited unbounded primitive checker must establish every guarded source case, with exact arbitrary register-value/tape/spare parameters and all430 table rows accounted for.
2. Blank execution must reach the exact canonical frame required by the command-permuted source compiler, with complete marker/register/spare information and an independent replay.
3. Those results must be bound to the unchanged held source/table and the submitted ordinary command-calibration theorem.

Until those obligations pass, the result is a 215-state held table with successful finite source and entry gates, not a completed Busy Beaver lower-bound claim.
