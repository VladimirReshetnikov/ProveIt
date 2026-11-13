# Independent audit of the AQ22 circuit display

This audit records the earlier PDF and status wording. The current wording
and refreshed PDF are checked in the
[independent wording refresh audit](../equation10-22-wording-independent-audit/README.md).

This is a finite audit of `../../research/adaptive-square-sums22-degree10/`
at the input hashes in `receipt.json`. The checked PDF prints the equation as
an arithmetic circuit, with 22 distinct positive integer unknowns and four
fixed integer ports. The checker explicitly binds each input and port, checks
all 114 numbered gate definitions and the output against the pinned graph,
and checks graph topology, liveness and the 13 output squares. The fixed
integers block, including its decimal text, is identical to the maintained
base-10 `../../equation.tex` block.

The degree-ten conclusion uses the separately recorded
`../aq22-degree10-independent-audit/` sparse polynomial check. That audit
finds an independent nonzero degree-five residual term and hence exact degree
ten even after specializing the fixed ports. At a circuit zero, the retained
`g72` residual forces `QComputed = (n*g)^2`, positive because `n` and `g` are
positive. The earlier audit discusses the remaining reconstructed positive
coordinates and the residual substitutions. The audit here checks the relevant
wiring; neither audit is a Lean proof of witness transport.

The checker also requires the display's explicit statement that Lean witness
transport and the internal intuitionistic PRA equivalence for this candidate
are unproved. These checks do not establish an iPRA derivation, the claimed
equivalence with `Con(ZFC)`, a lower bound or minimality. In particular,
matching the original fixed-integer text does not formalize the meaning of
its TeX decoder, table, or rank recipe: their connection to the graph remains
the manually transcribed finite-checker boundary described in the earlier
work, not a theorem about TeX semantics.

With Python, `pdflatex`, `pdfinfo`, and `pdftotext` installed, run from the
repository root:

```sh
python3 Computability/DiophantineConsistency/reviews/equation10-22-independent-audit/audit.py
```

It refuses to overwrite `receipt.json`; run in a copy after removing that
copy's receipt. The recorded ordinary-Python run exited zero. The checker
rejects five controlled changes: a gate operation, operand and target, a
decimal digit, and a repeated input name. It regenerates the displayed source
and PDF in an isolated tree, then separately compiles the TeX twice in clean
output directories. Both PDF hashes equal the checked PDF. Python `-O` and
`-OO` both exit nonzero intentionally, because assertions are required.
The receipt records absolute input paths from the audit environment; hashes,
not those path prefixes, identify the inputs.

`page-1.png` and `page-2.png` are 120 dpi `pdftoppm` renderings of the
checked PDF. Visual inspection found both pages legible at this resolution,
with no apparent clipping, overlapping text or missing circuit columns. This
is a human visual observation, not an automated layout proof.
