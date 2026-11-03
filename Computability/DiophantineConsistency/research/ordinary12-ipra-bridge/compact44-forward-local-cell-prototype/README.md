# Proposed compact44 occupied-cell aggregate lemma

`CompactForwardLocalCell.lean` is **uncompiled exploratory source**. It
proposes a model-level calculation in any `IΣ₁` model: if the selector count
is one, its weighted complement sum is that of a specified row, and the 41
copy bits have that row's payload sum, the actual finite selector-and-copy
coefficient sum is `1 + 2^51`. Its proof attempts to combine
`CompactCoefficientDecoder.finite_decomposition`,
`Compact943Decoder.tileValue_bounds`, truncated-subtraction cancellation, and
the exponential addition law. These three sum hypotheses are explicit; the
source does not assume or claim they follow automatically from any word.

Before this can be used in the construction, a coherent source build must
compile the draft and its dependencies. The imported coefficient and row
decoder prototypes have their own exploratory/provider evidence; no combined
build with the word side is claimed. `#print axioms` is a proposed check, not
an observed report. No Lean process was run for this draft.

The next bridge must define the 943-selector one-hot function and 41 actual
copy bits from a bounded compact row lookup, prove each of the three sum
hypotheses (including the payload's bit expansion and all seven occupancy
and anchor bits), then connect this finite local sum to the corresponding
digits of the actual packed `paramKernel rho` product. In particular, neither
the table lookup nor the symbolic kernel/retained-byte identification follows
from this lemma. Establish the mask disjointness, no-carry and neighboring
cell identities separately. This source gives no compact packed word,
positive graph zero, or iPRA derivation.
