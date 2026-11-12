# Four-rule iPRA with reusable clauses

Prepared for Vladimir Reshetnikov, 11 November 2026.

## Result

The package gives an explicit presentation of full first-order intuitionistic primitive recursive arithmetic using four inference schemes (Use, Step, Open, Close) and the fixed universal-reflexivity clause `[ ; y.(y=y)]`.

The written proof establishes exact proof translations with the pinned five-pattern zero-normal clause calculus. Its ordinary realization is therefore equiconsistent and bi-interpretable with iPRA. Both numerical domains are whole, equality is actual equality, and both numerical composite isomorphisms have graph `x=y`. The paper also gives the logical formula composites, the arithmetic compiler, and inherited detailed foundations.

This is an **incremental presentation and checker simplification**. Universal reflexivity remains a counted axiom clause. It is not a new arithmetic strength result, an absolute minimality theorem, or a new minimum over the repository's compressed checkers.

## Start here

- `report.pdf`: the complete paper, including the full selected checker and inherited arithmetic/logical appendices.
- `report.tex`: self-contained LaTeX source for that PDF, with no external input or listing dependency.
- `code/packet/checker.py`: selected standalone checker; only the Python standard library is required.
- `code/packet/FORMAT.md`: complete numerical, formula, packet, and acceptance format with worked examples.
- `code/packet/translate.py`: checked bidirectional translations between packets and explicit proof trees, plus a readable formatter.
- `code/packet/examples/`: 86 accepted packet certificates and a readable induction trace.
- `evidence/metrics.json`: measured source sizes, gzip-9 sizes, and hashes.
- `CLAIMS.json`: precise claims and limitations.
- `SHA256SUMS`: delivered-file checksums, excluding the manifest itself.

## Complete-checker measurements

Measurements use CPython 3.12.14. Remove documentation strings, apply `ast.unparse`, and append one LF. All acceptance code is counted, including parsing, syntax and scope validation, hereditary opening/zero normalization, all rules, and final acceptance. Gzip-9 uses timestamp zero and is informational.

| Complete checker | Normalized bytes | Significant tokens | AST nodes | Gzip-9 bytes |
|---|---:|---:|---:|---:|
| Pinned five-pattern tagged source | 2,950 | 829 | 902 | 1,005 |
| Five-pattern arity/scope control | 2,730 | 753 | 828 | 939 |
| Four-pattern explicit tree checker | 2,677 | 751 | 823 | 947 |
| Four-pattern ranked tree checker | 2,692 | 781 | 853 | 964 |
| Four-pattern empty-antecedent packets | 2,308 | 665 | 770 | 778 |
| **Selected four-pattern packets** | **2,282** | **666** | **770** | **774** |

The selected complete checker is 668 normalized bytes (22.64%), 163 tokens (19.66%), and 132 AST nodes (14.63%) below the pinned transparent checker. Against the stronger five-pattern arity/scope control, the savings are 448 bytes (16.41%), 87 tokens (11.55%), and 58 AST nodes (7.00%).

Clause factorization alone saves only 53 bytes, two tokens, and five AST nodes in the strongest matched tree control; its gzip size increases by eight bytes. The larger improvement comes from the goal-directed proof protocol and shared validation. Empty-antecedent packets use one fewer token than the selected neutral-antecedent version, but require 26 more bytes and the same AST count; both are supplied.

The selected readable source is 3,359 bytes, or 1,311 bytes with gzip-9. Its normalized source is 2,282 bytes, or 774 bytes with gzip-9. Exact normalized sources and gzip files are under `evidence/normalized/`.

The repository's 516-byte compact profile and 788-byte public-goal validated profile are **not beaten**. Their different, fused certificate encodings should not be confused with the transparent matched family above.

`experiments/` preserves the unselected support-derived-rank implementation discussed in Section 9. It is an exploratory size comparison, outside the verified checker suite. Its measurements are reproduced separately under `unselected_experiments` in `evidence/metrics.json`; the selected result does not depend on it.

## Run the selected checker

From this directory:

```bash
python3 code/packet/checker.py < code/packet/examples/induction_uses_hypothesis.json
```

Acceptance is exit status zero with exactly `ACCEPT` on standard output. Invalid input must not meet that contract. The selected program raises an exception on rejection; it does not promise a particular standard-error message. It does not use `assert`, so optimized Python retains its checks.

Read a certificate as a proof trace:

```bash
python3 code/packet/translate.py format < code/packet/examples/induction_uses_hypothesis.json
```

Decode a packet certificate to an independently checked explicit proof tree:

```bash
python3 code/packet/translate.py backward < code/packet/examples/induction_uses_hypothesis.json
```

`translate.py forward` performs the reverse direction. The initial fixed clause has index zero in the explicit tree format; packet indices omit it because reflexive goals close automatically.

## Reproduction

```bash
python3 reproduce.py
python3 reproduce.py --pdf
```

The first command runs the source-to-Horn, representation, fair-control, and packet checks, then regenerates measurements and the self-contained source. The second also compiles the PDF using pdfLaTeX. A complete TeX Live installation with the packages named in the source is sufficient; the build script requires no network.

To rebuild only the delivered paper:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`paper_main.tex` and `reference/*.tex` are editing/build sources. `build_report.py` embeds the selected measured checker and all five inherited foundation fragments into `report.tex`. The standalone source can be compiled without the build script.

## Verification evidence

The selected packet checker passed 620 standalone process checks, in normal Python and `python -O`:

- 86 accepted source certificates and 86 exact packet round trips;
- 52 rejection cases covering malformed syntax, eigenvariable and witness escape, forged Step premises, incorrect clauses, and unused input;
- 2,101 additional semantic opening checks against an independent finite numerical interpreter;
- zero failures.

See `code/packet/results/verification.json`. Separate reports under `code/horn/` and `code/ranked/` record checks of the intermediate translations and stronger controls. These counts are not combined into an inflated count of distinct mathematical examples.

The universal correctness and bi-interpretation arguments are written proofs. Finite tests are not proofs of consistency or universal checker correctness. The inherited Lean bridge sources were inspected at the pinned commit; the Lean project was not rebuilt during this run. No new Lean or Rocq formalization is claimed.

## Provenance

All repository comparisons are pinned to:

`443cff49563457a48ee0f663012d56c4bdb58fa0`

https://github.com/VladimirReshetnikov/ProveIt/tree/443cff49563457a48ee0f663012d56c4bdb58fa0/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The frozen source checker is `Research/uniform_step/code/checker.py`, SHA-256:

`17d116f7a6cbccaca169f76124aed5a9b20d45818747f96fba1c6f36668ad296`

The selected checker SHA-256 is:

`2962ccd1a8d9cd7edb3b6830048dea31e43c253888a15f07af7914a19a614a4a`

The scalar iterator basis, paired logical binder, witness-selected introduction, Step arithmetic, predecessor bootstrap, equality reflection, PR compiler, and established whole-domain bridge are inherited. The new work is the clause factorization, fair representation/implementation comparison, packet protocol and its proof translations, accompanying validation, and the explicitly separated support-quotient observation. See `evidence/provenance.json` and the paper for attribution.

Inherited code and mathematical material use the upstream MIT No Attribution license, reproduced in `LICENSE.txt`. Reference Lean files are excerpts requiring the full upstream project; they are not a standalone Lean project.
