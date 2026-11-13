# Independent review of the two 13-variable PDF bindings

This independent review passed with actual session 95388 exit 0, recorded in
[terminal-observation.json](terminal-observation.json). It independently
checks all 13 displayed input aliases, four port aliases, every one of the 87
sum-of-squares and 86 product circuit rows, the four-square equation and the
four-factor product-equals-one equation. It checks the unchanged base-10 fixed
block and compares all digits of all four saved historical Lean port outputs
with the complete pinned coefficient bytes. The two audited parent siblings
record the same kernel-data object used by the previous independent port
probe. The [receipt](receipt.json) pins these inputs.

An exact copy of the [original binding checker](../frontier13-pdf-historical-lean-binding/README.md)
was rerun in a temporary sibling directory without changing its packet. Its
stronger finite TeX-expression parser, all literal/gate/port mutation
controls, and two clean builds of each PDF passed. The rerun's actual exit,
output and receipt hash are recorded in this review's receipt. An initial
[review-development attempt](attempt-1-observation.json) failed because its
expected product text retained a space after whitespace normalization; the
[attempted script](attempt-1-script.py) is preserved and the comparison was
corrected before the successful run. Both scripts reject optimized Python.

I also inspected the four prior 100-dpi renderings: the formulas and tables are
readable with zoom, with no apparent clipping or overlap. This is visual
inspection, not an automated layout proof. The original checker interprets a
limited polynomial TeX subset, not general TeX or PDF semantics. Its fixed
decoder, tile table, rank and port formulas remain manually transcribed in the
prior finite reconstruction. The captured port calculations are external
Lean evaluations and byte comparisons, not a Lean theorem interpreting PDF.

The existing product PDF includes a **legacy claim about an HA derivation** and
its historical dependency scope. This review does not verify that claim; the
new standard-iPRA source packet and this finite display binding do not by
themselves establish it. Nor does this review claim a guarded 13-variable
extension, matched replay, current-source result, global minimality or an
identification of the selected translated sentence with untranslated Con(ZFC).
The historical package-transitive, dynamic-load, between-observation and
unobserved Foundation-wrapper-exit limitations remain.

Run with ordinary Python and TeX installed after preserving and moving aside
only this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/frontier13-pdf-historical-lean-binding-independent-audit/audit.py
```

The checker needs the pinned temporary parent snapshot and port evidence,
refuses to overwrite its receipt and rejects optimized Python.
