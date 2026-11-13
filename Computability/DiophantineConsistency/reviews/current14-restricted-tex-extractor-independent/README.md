# Independent review of the restricted TeX extractor

An independent shunting-yard parser reproduces all 23 prefix lines of the pinned historical Lean quote from the actual `equation.tex` arithmetic display. Its handling of exponent precedence, left-associated implicit multiplication, grouping, subtraction and earlier-declaration scope agrees with the reviewed parser on this input. The exact mapping of the 14 variable names and four port names to the corresponding Lean indices also agrees. This is external Python source evidence: it does not prove TeX semantics, port-recipe values, PDF rendering, a coherent Lean provider chain or an iPRA endpoint.

The extractor checker asserts only that the ordered variable/domain substring occurs somewhere in the TeX; it does not test the preceding words `The only unknowns are`, their immediate relationship to that display, or uniqueness. The extractor README has been corrected to state this scope after the independent review identified an overstatement. For the actual pinned page, this independent review **does** check that exact phrase occurs immediately before the displayed, correctly ordered `\mathbb Z_{>0}` declaration. A mutation replacing the phrase while retaining the substring leaves the original arithmetic extractor and substring check satisfied; it demonstrates the scope of the check, not an error in the actual page.

As already acknowledged by the extractor's README, its arithmetic extraction is not a TeX interpreter. This review confirms that adding a global `\renewcommand{\Delta}{X}` before the document leaves the extracted tokens unchanged. Thus equality of extracted strings alone does not rule out a changed TeX meaning under a modified macro environment. The actual pinned source, not arbitrary mutated TeX, is the target of the present check. Also, extracting the four port names does not prove that their separately printed recipes equal the values used by Lean.

The independent checker lexes the actual source using a separately written shunting-yard implementation, compares the resulting prefix lists to the Lean quote, checks the actual declaration context and core index mapping, and tests forward references, unknown identifiers and unsupported powers as well as the two scope limitations above. The original packet's checker separately exercises its listed operator, grouping, exponent, malformed-input and declaration-order mutations; these finite controls are not a general parser soundness proof. The receipt pins the exact source, quote, core and reviewed extractor files.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/current14-restricted-tex-extractor-independent/check.py | cmp - reviews/current14-restricted-tex-extractor-independent/receipt.json
```

No Lean, build, staging, PDF, port-recipe or provider validation was run.
