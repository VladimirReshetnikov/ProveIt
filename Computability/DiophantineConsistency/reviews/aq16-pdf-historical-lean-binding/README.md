# Finite binding between the historical AQ16 endpoint and its display

The guarded author-only standard-iPRA endpoint applies `nativeNoZero` to
`positiveShift (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)`.
The historical `positiveShift` substitutes each variable plus one. This
external checker compares the complete historical literal body with the
pinned AQ16 graph: all 16 variable indices, four port indices, 96 ordered
operations and final output agree. Six changes to the literal's indices,
gates or output are rejected. It checks the recorded endpoint and model
source hashes and follows recorded direct-import object hashes to the literal
and fixed-port provider.

The [earlier display audit](../equation32-16-independent-audit/README.md)
compared the graph with every displayed name and gate. The
[wording audit](../equation32-16-wording-independent-audit/README.md) checks
the current source and byte-reproduced PDF against that earlier presentation.
That separate wording audit has passed but is awaiting its own commit at the
time of this review.
This checker links those receipts to the current input hashes and verifies the
complete fixed-integer block agrees with the original `equation.tex`.

The AQ16 author overlay inherited the same audited AQ29 author parent and
`CurrentKernelData2011.olean` hash used in the independent
[four-port evaluation](../equation14-historical-literal-binding-independent/README.md).
The present checker independently recomputes the full integer comparison of
all four saved Lean `#eval` outputs, pinned coefficient bytes and recorded
printed-recipe output hashes. Four modified decimal strings are rejected.
The captured beta is exactly `2^94517 − 1`, hence meets the transport's
explicit beta ≥ 2 condition. The historical model source also contains a Lean
proof of that condition for the selected current port. The earlier probe and
printed-recipe reconstruction recorded actual exit zero; this checker does
not rerun either.

The AQ16 guarded author run itself recorded exit zero, but an independent
artifact audit and matched peer replay are separate tasks. This is an external
finite source/graph/display binding, not a Lean theorem interpreting a PDF.
The decoder, table, rank and port recipes remain **manually transcribed** in
the finite reconstruction; matching their displayed block does not provide a
general TeX parser. The selected consistency sentence is embedded and
Gödel–Gentzen translated. Historical parent, package-transitive, dynamic-load,
between-observation and Foundation-wrapper-exit limitations remain.

Run with ordinary Python from the repository root after removing only a copy
of this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/aq16-pdf-historical-lean-binding/audit.py
```

It requires the exact AQ29 parent state and source snapshot under
`/tmp/ipra-aq29-fresh-project-pair/author/` and
`/tmp/ipra-aq29-fresh-source-closure-v2/`; their hashes are in the receipt.
These temporary inputs may not persist. The checker refuses optimized Python
and refuses to overwrite its receipt. The recorded ordinary run exited zero;
the [terminal observation](terminal-observation.json) records the exact
receipt and PDF digests and optimized-mode exits.
