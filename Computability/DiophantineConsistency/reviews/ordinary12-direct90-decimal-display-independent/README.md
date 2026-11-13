# Independent direct-90 decimal display audit

`observations/attempt01/` retains a separate finite audit, an exact-degree
recomputation, and replays of both captured author checks. All four exited
zero with empty stderr; both replayed author outputs were byte-identical to
the earlier captured outputs. The independent audit pins the earlier capture,
checks its logs and before/after input hashes, checks both retained build
receipts and outputs, and rechecks their pinned inputs after its computation.

The independent audit parses all 90 TeX and extracted PDF rows, compares
them to the pinned DAG, checks the matching text of the Lean graph definition
and its variable/port indices, and verifies 90 live operations: 50 products,
23 sums, and 17 differences. It checks the extracted fixed-coefficient pages
against the digest-pinned earlier 94-operation display, all 943 decimal
selectors against the ordered source data, and the 41 slots. It independently
reconstructs all four integers from those selector and slot values using
binary shifts and compares the entire little-endian payload integers. It also
checks all PDF word boxes are within the four pages (minimum reported margin
28.028 points). The independent degree computation gives an upper bound of
172 and a matching degree-172 modular specialization with nonzero leading
coefficient 960910299 modulo 1000000007.

I visually inspected pages 1 and 2 at 100 dpi. On page 2, the sentence that
the selector list is printed "on the following pages" is slightly inaccurate:
the list begins on that page and continues on later pages. This is a wording
issue; the 943 extracted entries and their order passed the checks.

The draft explicitly uses twelve distinct positive unknowns, integer
subtraction, decimal constants, and named intermediate abbreviations. The
maintained root equation is a different display and was not modified. These
checks bind the displayed text to source and coefficients externally; they
do not prove a theorem in Lean about a parsed PDF, independently reconstruct
the historical Lean object ancestry, or establish an iPRA proof of the
equivalence. The model theorem and its selected-provider qualifications remain
separate from this display audit.
