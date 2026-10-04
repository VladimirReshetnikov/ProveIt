# Review and attribution

The coordinating root proposed the smooth-radix simplification and its
logarithmic input/constant threshold. The author independently checked
the periods, exact CRT conditions, new outer margins and every affected
dependency of the frozen factorial proof, and wrote SMOOTH_RADIX.md.

Root then read the complete addendum and approved its mathematical scope
and constants on2026-10-03. It specifically confirmed that the bound on
q is limited to the radix and is not a bound on all downstream Pell
witnesses. This is root/author review of a new optional corollary; it is
not attributed to the independent reviewer of the earlier factorial
proof.

The newly authored checker passed normal and optimized Python with
identical canonical bytes:625 smooth-period cases,27 height-selection
and literal CRT cases, and1009 exact margin cases. Its modular mock
constants are explicitly not claimed to be genuine compiler programs.
The infinite-domain result comes from the proof plus the original full
counterfamily, not from those tests.

The original factorial evidence remains byte-identical and separately
manifested. The preliminary strict-Pell-bound endpoint erratum is stated
explicitly in SOURCE_ERRATUM.md; it affects no range used in either full
construction and has not been silently patched into frozen source.
