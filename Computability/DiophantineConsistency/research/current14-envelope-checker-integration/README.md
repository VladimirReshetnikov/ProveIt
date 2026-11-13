# Connecting the exact-wrapper regions to the existing checks

This external Python integration takes the six **actual returned strings** from `current14-restricted-document-envelope/envelope.py`. It feeds the abbreviation and boxed-equation strings directly into the existing restricted arithmetic parser and compares the resulting 23 prefix lines to the staged Lean quote parsed by that parser's existing `lean_quote` routine. It then reassembles the complete document from the frozen envelope fragments and **all six returned regions**, and supplies those bytes to the existing printed-port recipe checker through an in-memory virtual read of `equation.tex`. The original checker code, exact pinned-page hash, printed-recipe snapshot check, source/data pins and payload comparisons all remain in force. No source file or historical packet is changed and no expected token lists or port values are hard-coded here.

On the pinned page, both consumers pass and the recipe result matches its previously recorded receipt. The controls demonstrate that a changed arithmetic expression is extracted as changed and fails the staged quote comparison; an altered recipe and an altered seed remain acceptable envelope data but are rejected by the existing recipe checker at its pinned-document boundary; and a macro redefinition is rejected by the envelope. The current recipe checker manually interprets its exact fixed recipe and **does not parse arbitrary recipe expressions**. Its rejection of recipe mutations is therefore a byte-pin check, not a proof that its evaluator understood and rejected those expressions. Domain order and selected macros are fixed by the envelope wrapper, not inferred from these consumers.

The one-process recipe adapter temporarily overrides `Path.read_text` and `Path.read_bytes` only for the relative path `equation.tex`, restoring both methods in a `finally` clause. The caller must not run the adapter concurrently with other code in the same Python process. Other files are read normally and the recipe checker's own pinned exact-source and data checks are retained. This is not a trusted general filesystem sandbox or a robust proof against an adversarial Python program.

This is an external, fixed-page Python join, not a Lean proof, general TeX/macro interpreter, `linePorts` provider authentication or PDF semantics. Existing historical endpoint/port theorems and their source/object ancestry are unchanged. A source-level next step is to define a real typed recipe parser and an independently specified Lean accepted-document relation before treating any extracted recipe result as a theorem. No Lean/build/staging or axiom report was performed.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current14-envelope-checker-integration/check.py | cmp - research/current14-envelope-checker-integration/receipt.json
```
