# Proposed construction direction for the compact44 free-J graph

This document is the original construction plan; its individual status notes
below are historical. A later [guarded Lean theorem](../compact44-halt-rank-no-high-prototype/README.md)
now constructs, from a model-internal halt, a full symbolic compact packing
and calibrated rank without extra physical premises. It does not construct a
positive graph zero, prove an all-model converse, identify the retained tuple
with the symbolic ports, or produce a derivation in iPRA. The intended first endpoint is conditional on a
model of `IΣ₁`: from an internal halting time of the selected `decimal215`
run, construct twelve strictly positive model naturals at which the **actual
free-J literal** `Ordinary12FreeJ.literal` has `InternalZero`, with the four
specific compact44 symbolic ports. The literal's final expression is a
polarized 95-operation representation of the ordinary 12-variable graph;
the natural polynomial is read in the model's difference ring through the
existing split-expression semantics. This implication is the direction
needed to show that no graph zero implies no encoded refutation. It must
include nonstandard model halting times, not only standard finite examples.

## Reusable construction and its boundary

[`ArithmeticCurrentConstruction2011.halt_positive_zero`](../../../Lean/DiophantineConsistency/ArithmeticCurrentConstruction2011.lean)
already gives, in any `IΣ₁` model and under its explicit
`ArithmeticPackingCells.LocalNormalization` premise, a positive zero of the
**14-variable 2011 equation** from a halt of the represented decimal215 run.
Its [`ArithmeticConstructionAssembly.construction`](../../../Lean/DiophantineConsistency/ArithmeticConstructionAssembly.lean)
exhibits the useful proof sequence: build a definable old-table `MarkedWord`
from a halted run; pack a base tableau; choose safe dummy bits by a controller;
derive rank/population and transport; choose positive outer and auxiliary
Pell seeds; assemble the vector; and prove the literal zero. The marked word
and the general arithmetic/Pell infrastructure are reusable proof ingredients,
not a theorem about the new graph. The actual 2011 construction fixes width
`94517 = 47*2011`, the current 2011 K and masks, and its own controller
residues. Compact44 instead uses `590069 = 67*8807` and different K and masks.
Substituting the new beta into the old fixed-port result is invalid.

For a supplied, model-definable old `MarkedWord`, the independently audited
[`CompactMarkedTransport.forward_marked_word`](../compact44-row-transport-prototype/MARKED-RESULT.md)
maps the old rows into the 943-row compact table while preserving the stated
marker and cyclic matches. Its forward definability theorem and the
single-side supplied-word equivalence are documented in
[`compact44-word-existence-prototype`](../compact44-word-existence-prototype/RESULT.md).
They do not supply a marked word, pack it into the compact44 arithmetic
interface, or identify finite table recipes with retained/displayed data.

The compact44 [controller data/choice pair](../../../reviews/compact44-controller-pair-independent-audit/README.md)
checks a definable Boolean controller choice and rank-calibration result for
width `590069` and modulus `581197`, **under its stated size, support and
unit hypotheses**. Its contextual historical-parent and provider limitations
remain. The external compact44 [coefficient recipe](../../../candidates/free-j-polarized-positive/source/positive/coefficients/recipe/PROOF.md)
describes the required new unit and dummy placement, but its ordinary
mathematical discussion is not the missing model theorem.

## Missing model construction

1. Construct the compact word from the halted run on one coherent provider.
   Carry the old word's definability, positive dimensions, marker, bounds and
   exact cyclic horizontal/vertical matches through the 942-to-943 relabeling.
   Do not assume an arbitrary marked word is already available from a run.
2. Define the actual compact44 cell and repeated word, with symbolic
   `rho=2^67`, period `8807`, low/high masks and `paramKernel rho`. Prove the
   compact counterparts of the local normalization, digit bounds, cyclic
   packing, transport and mask/no-carry facts used in the 2011 assembly,
   including all model-length and wrap cases. The 2011 `cellN`, K and masks
   are different and cannot serve as the required concrete compact object.
3. Establish the compact controller's **actual** premises: a sufficiently
   large model-internal tableau with the chosen power-of-`581197` dimensions,
   definable safe dummy locations and their exact rank variation, plus a
   unit/inverse for the compact `Gamma`. The recipe proposes a proof from the
   stated modular residues and a Boolean subset construction; its exact
   model-level unit and connection to the chosen K/dummies still need Lean
   proofs. Apply the paired controller only after the same witness and all
   size/support/unit assumptions have been supplied.
4. Prove rank/population/phase and positive transport data for that same
   compact packing. Reuse generic `ArithmeticRankForcing`,
   `ArithmeticConstructionVariation`, `ArithmeticOuterSeed` and
   `ArithmeticPellAuxiliarySeed` only at their actual hypotheses; the
   2011-specialized rank forcing and its numeric constants are not a compact
   calibration. The existing free-J graph-to-population facts run in the
   opposite direction, from a graph zero, and do not construct these witnesses.
5. Build a compact-port version of the enriched positive carrier assembly,
   retaining the precise rank, divisibility, size and auxiliary-seed facts
   needed by the 12-variable reduction. The 2011
   `ArithmeticAdaptiveConstructionReduced2011.reduced_zero_of_enriched_assembly`
   and `ArithmeticAdaptiveConstructionRunDraft2011.reduced_zero_of_run` are
   useful patterns but are specialized to 2011 ports and a 13-variable literal;
   their import/source existence alone is not a compact44 proof.
6. Give and verify a 12-coordinate positive witness for the literal free-J
   graph. The ordinary completeness argument in
   [`ordinary-unit-products`](../../ordinary-unit-products/README.md#completeness)
   proposes taking `t=f-1`, `n=i_ordinary+u`,
   `i_ordinary=Delta*i_normalized`, and the adaptive
   `gamma=gamma_old-w+v/U`; establish all divisions, inequalities and
   positivity **in the model** before using these as natural coordinates.
   The free-J candidate keeps the already positive J directly. Prove that the
   first and main residuals vanish and use the actual polynomial polarization
   identity for the ordinary residual, then verify `InternalZero` for the
   exact folded `Ordinary12FreeJ.literal` and four stated symbolic ports.
   A standard-integer polynomial identity or a previously constructed
   arbitrary 14-variable zero does not supply these model witnesses.
7. Identify the symbolic compact tuple with the intended retained
   coefficients/display and calibrate the construction to the selected ZFC
   refutation predicate. External byte matches and finite diagnostics are
   evidence but do not prove the corresponding Lean equality. Join the other
   implication separately, then use the established all-model/translation
   bridge to prove existence of the intended intuitionistic PRA derivation.
   A model `IΣ₁` construction alone is not that internal iPRA theorem.

The search and source references above were inspected without a Lean run.
Any implementation requires a coherent same-side source rebuild; the existing
marked-word and graph overlays contain incompatible objects and cannot simply
be mixed.
