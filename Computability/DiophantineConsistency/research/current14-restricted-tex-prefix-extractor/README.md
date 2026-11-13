# A restricted TeX-to-prefix extraction for the displayed arithmetic

A small Python parser now extracts the **22 displayed arithmetic abbreviations and the final equation** from the pinned `equation.tex` and obtains exactly the 23 normalized prefix-token lists used by the historically checked Carrier65 quote. It parses the page's arithmetic text rather than supplying a manually transcribed list. A separate source comparison checks the order of the 14 printed positive unknowns and the indices assigned to them, as well as the four port names and indices in the historical Lean environment. The deterministic receipt reproduces.

This is an external, restricted source check. The Python parser has no machine-checked soundness theorem and is not itself a Lean proof or a general TeX interpreter. The port **recipes** are not parsed, and no semantics of physical PDF rendering is established. The historical checked endpoint, its provider ancestry and the separate coherent-rebuild issue retain their existing qualifications. The result does not prove consistency of ZFC.

## Accepted arithmetic fragment

The extractor anchors on the unique prose introducing the abbreviation display, reads its first `gathered` block, requires its terminating period, and separately reads the boxed equation after the unique final-equation marker. Its small grammar uses:

* single-letter Latin identifiers and the explicitly listed Greek commands, with an exact whitelist and printed declaration order;
* literals 1, 2, 3 and 4, round or square grouping, binary `+` and `-`, left-associated implicit multiplication, and exponents `^2` and `^3`;
* ignored source whitespace, `\quad` and TeX row breaks; comma-separated declarations followed by the literal `=0.` final form.

Identifiers in a right-hand side must be one of the 14 variables, four ports, four small numerals, or an earlier declaration. Unknown commands, malformed grouping, duplicate/out-of-order declarations, unknown identifiers and unconsumed tokens fail the extractor. The parser turns operations into prefix trees, preserving left association, subtraction grouping and the `sq`/`cube` token conventions of the quoted Lean source. For the actual pinned fragment, all 23 lists match the historical quote byte-for-byte as lists of strings.

The receipt includes mutations of an operator, subtraction grouping and an exponent, all of which produce different tokens, plus malformed or unsupported inputs that reject. These are useful controls, not a completeness or soundness proof for all possible inputs. A trailing letter that remains syntactically a multiplication is accepted with **different tokens**, as expected; the assertion is equality against the fixed quote, not blanket rejection of altered formulas.

## What remains for a formal binding

The parser is a practical candidate for the `extract bytes = some quoted` premise isolated in the separate [conditional source client](../current14-tex-token-boundary-client-draft/README.md), but a Python result cannot discharge that Lean premise. A fully formal route would define the same restricted grammar and extraction in Lean, prove its accepted token trees denote the displayed arithmetic under an explicitly chosen interpretation, and prove its result on an explicitly associated TeX byte sequence. The soundness statement must specify its treatment of macros, implicit multiplication, grouping and declaration scope; byte identity alone does not establish TeX meaning. The actual general TeX engine allows macro redefinitions and other constructs this script neither interprets nor rules out globally.

In addition, `linePorts` in the existing quote supplies four previously formalized values; the source script here does not establish that the extensive `beta`, `K`, `mu` and `omega` recipes printed elsewhere on the page denote those values. The phrase declaring strictly positive unknowns is checked as source text and the existing quote's index mapping is inspected, but their TeX rendering is not formalized. A physical-PDF claim needs a separate PDF/rendering connection. A Lean implementation would also need a coherent, authenticated provider route and guarded elaboration; the pinned source files do not supply those automatically.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/current14-restricted-tex-prefix-extractor/check.py | cmp - research/current14-restricted-tex-prefix-extractor/receipt.json
```

The checker hashes the current TeX, the historical quote and compiler, and the independent Python extractor. No Lean, build, model transfer, provider audit, axiom report or PDF rendering check was run.
