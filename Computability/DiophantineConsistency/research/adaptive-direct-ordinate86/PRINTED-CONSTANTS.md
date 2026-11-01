# Printed fixed constants and PDF rendering

The 86-operation literal fixes its ports to `CurrentWindowCarry2011.ports`, which is definitionally `CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)`. The four entries are `beta`, `K`, `lowPort`, and `beta + highPort`. The printed names are respectively `beta`, `K`, `mu`, and `omega`; the high mask receives the beta shift once.

The corresponding source-level Lean bridge is explicit:

- [CurrentMaskRecipes2011.lean](../../Lean/DiophantineConsistency/CurrentMaskRecipes2011.lean) has `lowPort_printed_recipe` and `highPort_printed_recipe`, including justification of the low mask's natural-to-integer subtraction.
- [CurrentKernel2011.lean](../../Lean/DiophantineConsistency/CurrentKernel2011.lean) has `phi_printed`, `rawWord_printed` and `K_printed`; the latter proves the rational formula's cancellation to the actual natural-number kernel.
- [WangTiles942.lean](../../Lean/DiophantineConsistency/WangTiles942.lean) and its table/decoder dependencies connect the finite tiles, selector weights and floor positions used in `phi` to the actual decoded action data. `physicalPosition_eq_printed` is in [WangTiles942Core.lean](../../Lean/DiophantineConsistency/WangTiles942Core.lean).

These are Lean theorems about Lean expressions, not an automatic interpretation of TeX. Earlier independent reviews [checked the masks](../../reviews/current-masks2011-lean-peer.md), [decoder and tile/rank formulas](../../reviews/wang-tiles942-lean-peer.md), and [complete Phi/kernel recipe](../../reviews/current-kernel2011-lean-root.md), with their exact historical source hashes and inherited prerequisites recorded there. Current files have subsequently been split or refactored and have different source hashes; those historical object replays are not represented here as fresh current-source rebuilds.

## Whole-integer cross-check

Run from the repository root:

```sh
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_printed_constants86.py > /tmp/constants86.json
python3 -O Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_printed_constants86.py > /tmp/constants86-O.json
cmp /tmp/constants86.json /tmp/constants86-O.json
cmp /tmp/constants86.json Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/PRINTED-CONSTANTS-AUDIT.json
```

Both invocations passed with byte-identical output, saved in [PRINTED-CONSTANTS-AUDIT.json](PRINTED-CONSTANTS-AUDIT.json). The script adapts the standard-library numerical review preserved in the [Wang tile peer receipt](../../reviews/wang-tiles942-lean-peer.md). It verifies that the actual fixed-constant blocks in `equation86.tex`, `equation.tex`, and the historic reviewed page are byte-identical, with SHA-256 `e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6`. It reads the complete 715-digit base-10 numeral from the 86 TeX and compares it with the literal numeral in current `DecimalMachine215.lean`. Independent prefix and successive-division decodings agree; all 430 current Lean cached actions, both target lists, and 432 cached rail values match. The script reconstructs 942 tiles and all 885,481 non-Start floor comparisons from a manual transcription of the pinned displayed formulas. It then reconstructs every term of `K`, the two masks, beta and the shifted high port, and compares the complete big-endian bytes of each integer to the four preserved coefficient files. The complete K is 11,868 bytes with SHA-256 `64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`, matching the earlier independent full-K review. The remaining exact port hashes and current source hashes appear in the JSON.

This is an exact finite Python calculation, not Lean evaluation of the current `ports`, not a parser for Lean tile constructors, and not a general TeX parser. Its mathematical transcription relies on the pinned block and the cited human/source reviews. The result does not by itself prove either Diophantine equivalence or equality of current source and historical compiled objects. The separate [equation display checker](verify_equation86.py) checks the 86-row circuit and the 24 algebraic identities against its pinned displayed block and candidate JSON; it too is not a TeX-to-Lean proof.

The additional [TeX display parser](verify_display_tex86.py) reads the actual
86-page unknown declaration, all 20 displayed polynomial abbreviations and
the four boxed factors directly from `equation86.tex`, interprets the exact
polynomial subset used there, and compares each result to the pinned circuit
JSON using integer sparse polynomials. It checks that the 13 displayed
unknowns are distinct positive integers and that the final product is wired
as in the circuit. Two altered-display negative controls must be rejected.
This independently removes the manual transcription step for the boxed
equation and its abbreviations. It does not parse the fixed-constant recipes,
establish the JSON-to-Lean bridge, or verify PDF rendering.

The companion [14-variable TeX display parser](verify_display_tex14.py) uses
the same arithmetic parser to read the 14 positive unknowns, all 22 displayed
abbreviations, and the final factor product directly from `equation.tex`. It
compares each abbreviation and the final factor wiring with the pinned
65-operation candidate JSON and rejects two altered-display controls. Like the
86 checker, it is a finite external check of the polynomial display, not a
parser for the fixed-constant recipes or a Lean proof of the JSON binding.

```sh
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_display_tex86.py
python3 -O Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_display_tex86.py
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_display_tex14.py
python3 -O Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_display_tex14.py
```

## Reproducible PDF bytes and decimal display

On the installed `pdfTeX 3.141592653-2.6-1.40.22` (TeX Live 2022/dev/Debian), isolated builds of each current TeX file were byte-identical to its committed PDF:

```sh
mkdir -p /tmp/equation-render-audit /tmp/equation86-render-audit
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/equation-render-audit Computability/DiophantineConsistency/equation.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/equation86-render-audit Computability/DiophantineConsistency/equation86.tex
cmp /tmp/equation-render-audit/equation.pdf Computability/DiophantineConsistency/equation.pdf
cmp /tmp/equation86-render-audit/equation86.pdf Computability/DiophantineConsistency/equation86.pdf
```

Current `equation.tex` SHA-256 is `94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635`; its one-page PDF is `23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6`. Current `equation86.tex` is `d6f8eb15583d35c6f7a88e1cf51c62723525239f4420914ff5097ff794e9b437`; its two-page PDF is `7ed2b46a1caf6b1b11413a2ed3ab0b345eb5593fe56ffeae153bd2ef3ee5c860`. Both PDFs have letter-size pages. Text extraction shows the constant heading says base 10 in both. The actual digits and the exact displayed unknown lists are checked in the TeX; this is not a general PDF semantic parser. The logs show font-size substitutions and no overfull-box warnings. Identical bytes are established for this installed toolchain, not every TeX installation.
