# Finite Lean-to-display binding for the two thirteen-variable equations

This independent finite audit compares both 13-variable Lean literals against
their pinned graphs and displayed circuits: all input and port positions,
all 87 sum-of-squares gates and all 86 product gates agree. The 86-gate
literal and both relevant bridges are in the independently audited historical
AQ29 parent. The 87-gate literal and its native client are source-frozen
additions, not part of that parent. The checker inspects the two new standard
clients' selected literal references but does not itself compile them.

An independent sparse integer-polynomial evaluator and small arithmetic TeX
parser compare all 24 sum-of-squares definitions and all 20 product-page
definitions with their graphs. The checker verifies the exact four-square
equation, the four product factors and product-equals-one form, as well as
all printed numbered rows. It rejects three Lean-source and two printed-gate
mutations per page, and changes to each captured port decimal. Its parser
handles this displayed polynomial subset; it is not general TeX semantics.

Both PDFs copy the original base-10 fixed-integer block. The parent author
and peer records have the same `CurrentKernelData2011` object used for the
previously independently repeated [four-port Lean evaluation](../equation14-historical-literal-binding-independent/README.md).
The checker compares all four complete captured decimals with the pinned
coefficient bytes and printed-recipe result hashes. The fixed decoder, tile
table, rank and port formulas remain **manually transcribed** in that earlier
finite reconstruction. External checks and identical text do not constitute
a Lean theorem interpreting a PDF.

Two clean TeX compilations reproduce each checked PDF byte-for-byte. Their
SHA-256 digests are `321e9d2714b7c40af7af20d5d28299346f10c5413f432ec32cceb59ccc775269`
for the sum-of-squares PDF and
`5bc36026033278cccb874cf55d334c516d902c50c848155f8f40e22c5b22cce5` for the
product PDF. Both are two Letter pages. The saved 100 dpi renderings show no
apparent clipping or overlap; small circuit text benefits from zooming. This
is a visual observation, not a formal layout proof.

The normal audit's actual exit was zero; `-O` and `-OO` were rejected. Three
earlier development invocations exited one while the product-page comparison
was corrected for command spacing and its printed factor aliases; see the
[terminal observation](terminal-observation.json). Run ordinary Python from
the repository root after preserving and removing only a copy of the receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/frontier13-pdf-historical-lean-binding/audit.py
```

The checker requires `pdflatex`, the historical AQ29 parent and source trees
under `/tmp`, and the recorded port artifacts; it refuses to overwrite its
receipt. This is not a new Lean replay, a current-source or matched
standard-theory claim, or a proof that a translated sentence is identical to
untranslated Con(ZFC). It retains the historical package-transitive,
dynamic-load, between-observation and Foundation-wrapper-exit limitations.
