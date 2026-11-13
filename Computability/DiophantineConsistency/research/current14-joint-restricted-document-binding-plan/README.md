# A joint restricted-document binding for the original 14-variable endpoint

This is a proposed source-only proof plan, not a parser implementation, Lean proof, provider audit, PDF interpretation or iPRA derivation. It concerns the existing `equation.tex` and the historical 14-variable Carrier65 endpoint, not a reduced or relaxed graph. The exact source bytes and interfaces used here are pinned by `check.py` and `pins.json`.

## Existing pieces and where they stop

* `research/current14-restricted-tex-prefix-extractor/extract.py` recognizes the abbreviation `gathered` block and boxed equation using a restricted parser; it extracts 22 named lines and one result line. The independently written shunting-yard review matches these to the actual staged `Current14QuotedPrefixQuote.lean` token list and checks the actual 14-variable declaration. Both are Python/source comparisons. The extractor ignores global macro changes; an independent negative control shows why its result is not TeX semantics.
* `research/current14-printed-port-recipe-semantic-check/check.py` and its independent review manually interpret the four printed recipe families. They compute the 715-digit decimal seed, 430 actions, 942 tiles, 941 non-start ranks and all four exact integer payloads. They are not parsers or proofs of TeX semantics.
* `Sign17LiteralPorts.lean` defines the MF structured recipes, including K in `ℚ`. Its `all_ports` gives three `ℤ` equalities and one `ℚ` equality. The historical `Sign17LinesCurrent14Endpoint.lean` states `linePorts_recipes`, `linePorts_eq`, and `line_endpoint_translated` at the same four-entry `linePorts`. The staged `quotedExpr_eq` is **uniform in an arbitrary port function**; its final endpoint uses that particular `linePorts`. The separately reviewed historical runs establish their reported scope and retain their inherited provider limits. None parses the page.

## A non-vacuous output object

A candidate Lean `DocSpec` should contain all of:

1. The exact positive-domain ordered variable list and all 23 parsed prefix lines, using the same `String` token conventions and variable/port map as `Current14QuotedPrefix`.
2. A **typed recipe AST**, not four predeclared opaque values: literals and named references; arithmetic over `ℤ`/`ℚ`; finite sums and products with explicit bound-variable scope; powers, Euclidean floor/mod, digit selection, finite sets, cardinality and indexed tuple/table cases. Types must record that `K` is rational until integrality is proved. A decoder program must cover the full decimal seed, mask/flag and mixed-radix action formulas, every tile case including tile 0 and the actual first target, selector and physical-rank formulas, Phi, all masks, and the fourth-port beta shift exactly once.
3. Explicit accepted document wrapper/macro policy and section boundaries. The actual source contains `\let\bigsum\sum`, `\renewcommand{\sum}{\bigsum\nolimits}`, and the definitions of `\fl` and `\rg`. A first fixed-document checker can require byte-exact inert wrapper regions and these exact macro definitions, rejecting any other command or unscanned math-bearing content; alternatively a genuinely defined whitelist may be parsed. It must reject an added `\renewcommand{\Delta}{X}` anywhere, rather than merely ignore text outside extracted blocks. Such an exact-envelope policy proves only a specified restricted source interpretation; it is not general TeX engine semantics.

`parseDocument : ByteArray → Option DocSpec` must be deterministic, total and reject malformed, duplicate, out-of-order, unknown or trailing material. It must actually consume and parse all mathematically relevant recipe and core text; accepting a document hash and returning a preselected `quoted` or hard-coded port tuple does not meet this plan. It is acceptable to use separately checked finite intermediate certificates for efficiency, but their contents must be constrained by the parsed recipe AST and validated, not trusted as conclusions. The embedded document bytes may be generated from the file, but associating those bytes with the physical workspace path remains an explicit external step; Lean cannot observe a file without a specified trusted input mechanism.

## Proposed meaningful Lean statements

Define a separate inductive `AcceptedDocument bytes spec` with the exact closed wrapper/macro policy and compositional expression/recipe grammar and scoping rules. Its interpretation must be defined independently of the parser implementation; in particular it cannot say merely `parseDocument bytes = some spec`. Prove parser soundness:

```
parseDocument bytes = some spec → AcceptedDocument bytes spec
```

Prove the concrete, deterministic output equation, evaluating the parser on the retained exact bytes rather than filling `spec` by hand:

```
parseDocument equationTexBytes = some equationSpec
```

Then prove that **the parsed result** has (a) the prescribed 14 positive unknowns and prefix lines equal to the existing `quoted` list, and (b) recipes whose compositional meanings are the MF `beta`, `K`, `mu`, `omega` definitions (the signed and rational types explicitly preserved). For the rational K entry use the already stated `(linePorts 1 : ℚ) = K` rather than silently floor a possibly nonintegral rational. The other three equalities are in `ℤ`; `linePorts_recipes` supplies the port connection. Nonnegativity, uniqueness of table slots, valid divisors, digit bounds, rational integrality and rank equalities must be established where required by the actual AST interpretation. A finite checker may certify those equalities, but its validation theorem needs to match the parsed expressions.

Define the document sentence from the **parsed** arithmetic prefix lines and `linePorts`: compile the lines using the existing staged quote compiler, positive-shift the 14 variables, and build the same no-zero sentence. A proposed substantive final theorem is:

```
∃ spec φ,
  parseDocument equationTexBytes = some spec ∧
  AcceptedDocument equationTexBytes spec ∧
  ParsedRecipesAgreeWithLinePorts spec linePorts ∧
  parsedNoZero spec linePorts = some φ ∧
  standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ
```

Its proof should compose parser evaluation, soundness, all recipe denotation equalities, uniform `quotedExpr_eq` and the selected historical translated endpoint. In particular, every recipe equality must be a conclusion backed by parsed syntax and the existing port theorems, not a free premise in this final statement. A preliminary theorem explicitly conditional on any of these obligations can be useful, but must not be called this result. This states derivability for the selected iPRA coding and translated source sentence. The separately recorded HA result is a different theorem and provider chain; no equivalence between those two proof objects is assumed here.

## Delivery and remaining trust

First formalize the closed wrapper, 23-line arithmetic grammar and typed recipe AST; add rejection controls for macro redefinition, reordered port declarations, altered tile arithmetic, dropped fourth-port beta, modified seed digits and K denominator/rounding. Then implement the parser, prove its independent grammar soundness, establish the fixed-byte parse in small staged certificates, and prove semantic equality to the current MF recipes and the final sentence. Resource-bound any future Lean run; proof-term elaboration at this size and the earlier concrete-ports kernel memory failures are real unresolved risks. A parser-generated certificate alone does not remove the parser/specification trust boundary, and source headers do not authenticate objects. Finally, separately establish the desired TeX-engine/PDF rendering relationship if a physical-PDF theorem is required, and use a coherent source/provider replay for any new combined Lean theorem.

`check.py` checks source shapes, exact macro occurrences and selected pin hashes; it does not implement any of the proposed formal statements. No Lean/build/staging is performed. Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current14-joint-restricted-document-binding-plan/check.py | cmp - research/current14-joint-restricted-document-binding-plan/receipt.json
```
