# CurrentReflectedGeometry2011 author verification

**Author verification: PASS; independent review remains separate.** Author: circuit_reduction. The new 350-line module and 57-line checks were read in full before the final fresh runs. No previously frozen source, central document, or git state was edited. This note records the exact new arithmetic result and its remaining premises.

## Frozen files

Paths are relative to Computability/DiophantineConsistency.

| File | SHA-256 |
| --- | --- |
| Lean/DiophantineConsistency/CurrentReflectedGeometry2011.lean | 268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1 |
| Lean/DiophantineConsistency/CurrentReflectedGeometry2011Checks.lean | dff4b89f56f3823b3480ea7b8b07c47e59b98cc98516ac7b41bbd4d69c083095 |
| Lean/DiophantineConsistency/CurrentKernel2011.lean | 6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55 |
| Lean/DiophantineConsistency/WangTiles942Permutation.lean | 3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef |
| Lean/DiophantineConsistency/CurrentMasks2011.lean | 72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06 |

Direct imports are CurrentKernel2011 and WangTiles942Permutation. The kernel author confirmed that the imported CurrentKernel2011.olean was freshly built from the exact final source above, including the public transition_mass theorem. Its independently checked object SHA-256 is 149b7322775beeda97e66e0272d9f4869e66bd1489a2da6c8c80df7b1bb698c2. The new geometry object SHA-256 is 02ad0013e1cdfac2c86d310a862d16668720661ab1ffeae9043e37e8b5749cdc.

## Literal definitions and proof

`reflected c k` is exactly the last sum of CurrentKernel2011.convolution_eq: for every Entry e it includes 2*weight e times c(k-(1005-position e)). All reflected and bare collisions remain counted. The proof uses the actual 942-selector physical permutation and the exact 34 control entries in their true packed west/north/east/south positions.

- `position_injective` combines the proved selector-position injection with the disjoint control intervals. `doubled_weight_lt` bounds every entry coefficient strictly below 2^45; this includes control coefficients that may act on selector sources. `doubled_control_mass` kernel-checks the complete 34-entry sum as 2^45-2048.
- `reflected_even` proves evenness at every cyclic position with no Booleanity, support, one-selector, or phase hypothesis.
- For a base b whose residue modulo 2011 is zero, `reflected_source` shows that a reflected source with h+position<1005 vanishes: its preceding-cell residue lies beyond the supported maximum 1004. Otherwise its exact same-cell offset is source(h,e)=h+position(e)-1005. The complete sum identity is `reflected_cell`. For h<=1004 every surviving source is at most 984. Fields below 20 have no reflected contribution at all.
- The conditional bound splits by **source position**, not by entry constructor. The weighted sum on selector sources is bounded by (2^45-1) times their unweighted sum. An injective partial reindex into Fin 942 proves that this unweighted sum is at most the explicit physical selector count. The at-most-one premise then makes the weighted selector-source contribution strictly less than 2^45.
- A nonselector source at h<=1004 forces coefficient position>=943; at h<=1003 the stronger bound is >=944. Hence no selector entry contributes to that part. Booleanity bounds all remaining terms by the entire control sum 2^45-2048, including arbitrary controls and the Boolean dummy977. No decoded label equality is used.

Thus `reflected_lt` proves E_h < 2*2^45-2048 for every h<=1004. This includes the marker itself, slightly strengthening the reset domain needed in ordinary sections 5–6. The three non-reflected monomials contribute at most three Boolean units; arbitrary temporal digits bounded by 2^46 and incoming carry at most 57 give

```text
E_h + 3 + 2^46 + 57 < (2*2^45-2048) + 3 + 2^46 + 57
                         = 2^47 - 1988 < radix.
```

`low_raw_budget` states this inequality for the actual folded-kernel convolution. `outgoing_carry_zero` then resets every bounded solution of the literal carry recurrence, not just a particular constructed least fixed point. `incoming_carry_zero` covers every field 1 through 1004. `copy_marker_incoming_zero` specializes to the 17 copy tests at 960..968 and 987..994 and the marker at 1004.

## Explicit hypotheses and scope

The conditional bound assumes exactly: a nonempty cyclic length N*2011; a Boolean digit function c; zero c outside the actual periodic lowSupport; a cell base residue zero; and the explicit physical sum over fields 0..941 at that cell at most one. The reset wrappers additionally require temporal digits r<=2^46, carries<=57, and their exact recurrence using CurrentKernel2011.folded. These are visible theorem arguments.

There is no assumed label decoding, zero incoming carry, temporal phase alignment, native tableau, machine execution, or consistency equivalence. The result does not by itself prove the at-most-one selector premise from a current polynomial zero. The independent early-tail/padding and preliminary-count work must supply that premise before these conditional resets are applied. Temporal bounds and the actual carry solution likewise come from separate normalization/rotation results.

## Fresh checks

Both final invocations use the configured Lean v4.32.0 with `-M6000 -j1` and the source's `Elab.async false` option. The module object is new; no unrelated object was overwritten. Dependencies were reused and are not claimed freshly replayed by these two commands.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentReflectedGeometry2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentReflectedGeometry2011.olean
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentReflectedGeometry2011Checks.lean
```

Final module: PASS, exit 0, 7.28 seconds, peak 3288372 KB, no diagnostics. Final checks: PASS, exit 0, 3.37 seconds, peak 3221864 KB. Logs: /tmp/reflected2011-final-module.log and /tmp/reflected2011-final-checks.log. Earlier draft failures concerned a control-sum simplification and a closed support-membership check; the final files above supersede them.

The focused checks verify the actual west/east coefficient mapping, the first reflected field20, a control coefficient acting on selector source941 at marker1004, the arbitrary dummy977 contribution, actual supported/unsupported boundary positions, the full control sum, and the exact worst-phase reset margin. All 12 requested axiom reports use only propext, Classical.choice, and Quot.sound. No sorry, new axiom, or native_decide is introduced.
