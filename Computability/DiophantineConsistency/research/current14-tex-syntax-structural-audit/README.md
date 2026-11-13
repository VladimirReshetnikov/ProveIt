# Displayed arithmetic core and Lean source: structural comparison

`check.py` parses the 14 displayed positive variable names, all 22 arithmetic
abbreviations and the boxed zero equation in `equation.tex`. It independently
extracts the corresponding declarations of `expressionAt` from
`Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean`. Both sides are
normalized using the same small expression parser, explicit fixed-port and
coordinate mappings, and recursively hashed expression trees. It checks every
abbreviation, the complete final tree, and the Lean `.var` coordinate indexes.
The result passes, including six negative controls that alter the displayed
coordinate order, a port, a power, the final sign, a Lean index, or a Lean power.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current14-tex-syntax-structural-audit/check.py
```

`result.json` records the output and source hashes. This is a deterministic
external source comparison, not a Lean theorem or a formal interpretation of
TeX/PDF. It assumes ordinary arithmetic conventions for the accepted limited
TeX grammar and the SHA-256 structural hashing; both sides share parser code.
It checks that the display declares the expected positive-integer domain, but
it does not check the rendered PDF, the coefficient definitions, the tile
decoder, the operation count, the degree, or the interpretation of `Con(ZFC)`.
The four port identities and decimal seed are handled by separate existing
results; this check does not re-prove their connection to printed text.
