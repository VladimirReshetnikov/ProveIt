# Exploratory forward cyclic-word transport

`CompactMarkedTransport.forward_marked_word` takes an existing old-table `ArithmeticWangPlane.MarkedWord a N s` in an arbitrary `IΣ₁` model and applies `rowLookup` pointwise. The resulting compact cyclic word has each row index <943, excludes row 1, preserves the marker, and satisfies the east and south cyclic matching relations supplied by the old word. The theorem uses the audited bounded local row/matching pair; it does not construct the original word or derive its neighbor/wrap hypotheses.

Author-only Lean session 11744 actually exited 0 with no warnings or `sorryAx`; its named axiom report was `[propext, Classical.choice, Quot.sound]`. The first attempt, preserved as `CompactMarkedFailed01.lean`, actually exited 1 in session 37798 on a zero numeral cast rewrite and printed `sorryAx`; the corrected source explicitly presents the zero as a cast. No objects or raw tool transcripts from these exploratory sessions were retained. A coherent paired replay and its independent review are still needed.

The proof does not establish the reverse compact-to-old direction, the definability of the transformed word, the existence of a compact or old word, compact checker calibration or a 12-variable iPRA endpoint. The paired provider and finite-table provenance boundaries still apply.
