# Reusing the already computed selected marker

Review status: author verification and independent root and binary complete
proof/source reviews and fresh runs passed without findings. Mathematical
construction and arithmetic are frozen.

This exact successor to `EXPLORATION_IMPLICIT_SELECTOR_COMPLEMENT_TAG.md`
costs **112 operations=55 multiplications+57 additions/subtractions**, with
**36 positive existential unknowns and23 equations**. It preserves the full
positive encoded-word halting equivalence, with the same arbitrary nonempty
appendant and deletion-number contracts. It imposes no new bound or first-
selector promise. No raw numerical-input conversion or universal operation
bound is claimed, and the frozen113 predecessor is unchanged.

## 1. The redundant adapter and comparison

The113 schedule has the three instructions

    M1=F_M1-1,
    twice_Q=2Q,
    marker1=twice_Q+S1,

and compares marker1=M1. The first instruction merely adapts a separate
positive supplied copy of a value already computed by the other two.

Delete F_M1 and its adapter. Rename the marker1 output to M1 and delete
the comparison. Keep every use of M1 unchanged. Because Q=F_Q-1 and
S1=F_S1-1 remain nonnegative computed coordinates,

    M1=2Q+S1>=0

holds before any power or mask proof. No additional positivity test or
arithmetic is required. This saves exactly one subtraction, one supplied
unknown and one comparison; the two existing marker instructions remain.

## 2. Exact positive solution correspondence

Every new solution has the unique positive extension

    F_M1=M1+1=2F_Q+F_S1-2>=1.

It satisfies the old adapter and comparison. Conversely, the old comparison
forces exactly this value, so forgetting F_M1 gives a new solution. This
argument holds directly on the integer source equations and domains; it
does not require a preliminary mask conclusion.

Every retained coordinate and computed value has the same numerical value
as before. In particular the order

    Gstar,Q,S0,S1,M0,M1,E,Ebar,Nbar,N

and its packed value P are unchanged. The index r, positive scale and bound
witnesses, and all seventeen positive Pell auxiliaries are unchanged.
The113 pre-mask bounds, signed-field recovery and complete positive converse
therefore transfer without alteration. This is a literal positive-coordinate
bijection, not a repacking or a fresh-index construction.

## 3. Exact source and fresh verification

The checker `../verification/explore_derived_selected_marker_tag.py`
constructs the complete112-instruction schedule. Under the substitution

    F_M1=2F_Q+F_S1-2,

the removed source is identically zero, and all remaining source polynomials
agree exactly. The checker independently evaluates all twelve outer and
eleven kernel source comparisons, including the shifted norm-source
correction at combined index20. It verifies the identical packed word,
index expression and predecessor comparison symbolically as well.

Fresh canonical examples evaluate the actual new prefix and the restored
old prefix, not only the formal source substitution. They cover944 halting
histories and2,318 source rows, all ten masks and the exact native index
valuation. Every new example checks twelve new and thirteen restored outer
comparisons. Both index parities occur and all944 indices are preserved.
Zero selected-marker words are explicitly tested: their restored F_M1 is
one. The three-formal-row example with a true halt after one step remains
admitted. The428 cutoff runs remain unclassified.

The huge Pell auxiliary values are not materialized; their existence and
exact preservation are justified by the reviewed predecessor theorem. This
result makes no claim that the remaining adapter count is optimal or that
the encoded-input contract has been replaced by an ordinary numerical query.
