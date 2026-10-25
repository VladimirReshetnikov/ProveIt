# Round 19 assembled report review

**Verdict: PASS for the assembled 26-page report, at its stated ordinary-mathematics proof boundary.** No unresolved mathematical transcription, metric, reference, or visual defect was found. No canonical file was edited and no external communication or publication was performed.

Reviewed PDF: `round19/render/main.pdf`, 444,103 bytes, SHA256
`5bc1bd1f791907ca3be4a1019629d942e6d7c64199d93a9965d18e0de0d7b9f9`.
The staged `round19/package/ConZFC_Cofinal_Witnesses_Centered_Carriers/report/main.pdf` is byte-identical and has this same hash. Review date: 2026-10-25. This signoff applies to these exact bytes and the identical staged report sources, not to a subsequently changed PDF.

## 1. Every-page visual inspection

Read the PDF skill, rendered all 26 pages with Poppler at 110 dpi to `report_pages/page-01.png` through `page-26.png`, and opened and visually inspected every individual image. All pages passed. Equations, fractional indices, long fixed-coefficient formulas, command blocks, tables, page numbers, and the two-page table of contents are legible and inside the page. No overlap, clipped material, missing glyph, broken equation number, unresolved reference, or visibly overflowing table was found.

Page coverage:

- 1–2: title, abstract, complete TOC, objective and comparison scope.
- 3–5: result tables, integer equations, affine elimination, scoped rank obstruction.
- 6–9: natural-domain metrics, equations (N1)–(N7), soundness/completeness and pre-basis controls.
- 10–14: positive polynomial definitions, equations (1)–(7), divisibility order and degree witnesses.
- 15–17: commands, whole radix67 coefficient recipe, tile table and complete seed.
- 17–21: centered-root definitions, equations (8)–(10), all-zero maps, polynomial shear and proof boundary.
- 21–24: separately scoped whole radix47 specialization, controller facts and fresh-source bridge.
- 24–26: complete radix47 coefficient recipe, tile table, decoder and seed.

Optional polish only: the radix67 seed's verbatim block continues across pages 16–17. Its characters are all visible and complete; this is not a defect or signoff blocker. The final radix47 seed occupies only the top of page 26, which is also acceptable.

## 2. Last-pass reference stability

Copied the report sources and current `.aux`, `.toc`, and `.out` to the disposable `report_rebuild/` directory and ran another LaTeX pass with the retained format and font map. This produced 26 pages, with **byte-identical `.aux`, `.toc`, and `.out`**, and byte-identical layout-preserving extracted text to the reviewed build4 PDF. The successful review pass and build4 contain no LaTeX warning, overfull/underfull box warning, unresolved reference, or rerun request. The initial disposable build lacked the local font map; copying the existing map resolved it without changing canonical sources. Nothing remains blocked.

Evidence: `report_layout_evidence.json`; successful log: `report_rebuild/build_review.log`.

## 3. Independent literal metrics

The new `report_metric_audit.py` imports no equation producer or supplied checker. It reads literal residuals, expands and recollects **every sum-of-squares coefficient** for 13 direct equations, and verifies each stored expansion. It independently counts every live binary arithmetic gate, input and coefficient port of 18 displayed/new/comparator circuits.

For those circuits it also substitutes each variable by a distinct nonzero scalar times a single indeterminate over the prime field F_10007, using the actual complete fixed-integer payloads reduced modulo 10007. Every resulting nonzero leading coefficient occurs at the structural upper-bound degree. Thus these are exact degree proofs for the actual fixed integer specializations, not merely checks of degree metadata or numerical witness tests. NumPy integer convolution is exact here: each coefficient accumulation is far below the signed 64-bit limit before reduction.

Normal and `python3 -B -O` executions pass with byte-identical receipts. **65 exact source/stage byte bindings** cover the selected equations, expansions, DAGs, all coefficient payloads, report sources, final PDF, natural raw counts and row-shear lists.

### Selected direct equations

| Profile | Variables | Rows | Terms | Height | Degree |
|---|---:|---:|---:|---:|---:|
| Integer dimension | 246 | 178 | 12,541 | 12,227 | 4 |
| Integer sparse | 247 | 179 | 4,352 | 23,316 | 4 |
| Integer balanced | 247 | 179 | 4,432 | 17,235 | 4 |
| Integer lower height | 247 | 179 | 5,648 | 6,144 | 4 |
| Natural cofinal dimension | 219 | 171 | 8,267 | 130,686,428 | 4 |
| Natural cofinal sparse | 221 | 173 | 5,253 | 65,867,916 | 4 |
| Natural noncofinal balanced | 221 | 172 | 5,586 | 65,892,620 | 4 |

All displayed incoming and pre-basis direct comparisons also match literal SOS expansions:

- Incoming integer: 252 / 182 / 5,340 / 128,446.
- Incoming natural positive-center: 221 / 172 / 9,536 / 83,954,186.
- Round18 natural balanced: 229 / 179 / 5,607 / 65,892,965.
- Natural pre-basis controls: 219 / 171 / 9,253 / 560,710,452; 221 / 173 / 6,269 / 83,847,181; 221 / 172 / 6,561 / 83,878,986.
- The natural raw dimensions/rows are 325/276 and 324/276; final elementary row-shear list lengths are 32, 44, 41 as printed. The rejected common-denominator trial's 323 raw and 231 contracted variables agree with its literal artifacts/summary and retained proof; no improvement is claimed for it.

### Small-variable equations and comparisons

- Positive ten-input charts, both whole coefficient specializations: 78 operations / degree 516; **79 / 382**; 79 / 456; **80 / 338**. The square-weight controls are correctly called dominated.
- Incoming centered positive charts: 75 / 626, 76 / 464, 77 / 460; incoming partially normalized chart: 80 / 382.
- Centered root charts: **14 inputs / degree 88 / 110 operations**, with multiplication/addition/subtraction counts 64/23/23; **13 / 156 / 117**, counts 70/23/24.
- Root comparisons: 14/88/115, 14/86/112, 14/94/110, and 13/156/125 all match their literal graphs and exact degrees.

### Whole fixed tuples

- Canonical positive radix67: **295,388 raw bytes**, maximum **592,884 bits**.
- Separate incoming radix47 specialization: **207,214 raw bytes**, maximum **415,904 bits**, saving exactly **88,174 bytes**. All four port payloads are replaced coherently; the canonical67 branch remains unchanged.
- Root tuple: **615,883 raw bytes** across all six payloads. The printed exact constants `beta=2^1064921-1`, `cone_A=2^1113`, and `cone_B=2^666104` agree with the actual integers.

Machine evidence, including all source paths, coefficient hashes, literal equation hashes, exact circuit witnesses and bindings: `report_metric_evidence.json` and identical `report_metric_evidence_optimized.json`.

## 4. Mathematical transcription and comparison boundaries

- **Source +2 versus reduction +1:** the positive reduction defines `A=Y(X+1)+1` and `Delta=A^2-1`. Its source reconstruction explicitly uses the distinct `A_source=Y(X+1)+2`. Appendix A defines `a_s=Y(X+1)`, `A_s=a_s+2`, `H_s=4a_s+3`, so `Delta_s=A_s^2-1=a_s^2+H_s`, exactly matching the literal incoming P66 source. No same-base identification is made.
- **Raw T:** the report prints `T=(V+c+R f^2)/(c f^2)` and, separately, `T_s=(V_s+c_s+R f_s^2)/(c_s f_s^2)`. These rearrange the actual raw equations `V=f^2(cT-R)-c`; no missing factor of `f^2` or silent inverse shift is present.
- **Natural cofinal theorem:** the new `t=2t_0+4`, `y+1=V` choice is explicitly **not a natural-coordinate bijection**. Its acyclic soundness and constructive cofinal completeness are supplied separately. Section 7 reiterates this boundary; the unrestricted integer-shear language is not transferred to natural domains.
- **Root coordinate change:** Section 6.4 explicitly states `n_old=n_new-(2L+k)`, with `L,k` independent of `n`, as a polynomial triangular lattice automorphism. The selected-equation summary expressly denies identical-polynomial recompilation in the old coordinates. The root-dependent maps to the fifteen-coordinate parent are kept distinct.
- The `178(246+1)=43,966` column claim is scoped to affine-polynomial residual multipliers and matches the retained rank certificate; it is not advertised as a global lower bound.
- The entire incoming47 native theorem/controller is retained and separated from the old67 calibration. The coefficient saving is attributed to the incoming encoding; the current contribution is its checked composition with the new charts.
- The ordinary mathematical proof boundary, inherited calibration dependencies, no consistency decision, no new end-to-end kernel certificate, no upstream modification and no global-minimality claim are all explicit.

This review crosschecked the existing ordinary reviews and finite receipts in `round19/review/` and the root-level round19 source/composition reviews; it does not replace them with finite testing of an unbounded theorem.

## 5. Assembly difference, not a defect

All six positive/natural/root/alternate component section/recipe files are copied byte-for-byte into the assembled report. The integer section is exactly the main prefix of the current release section, but omits its newly appended 16-line **optional lower-horizon companion** paragraph (`t=4+h^2`, 144-case certificate, `P4-P16=24t-24h^2-240`, coefficient L1 saving 288). This does not alter any reported main profile, formula or metric. The parent confirmed this is a **deliberate article-scope omission**: all four recommended main quartics retain horizon 16; the optional proof, certificate and companion builder remain supplied separately under packaged `quartic/horizon4/` and described in the README. The main article is intentionally unchanged. This source supplement versus integrated scope distinction is resolved, not pending.

## 6. Reproduction of this review

From the workspace root:

```sh
python3 -B round19/review/report_metric_audit.py > /tmp/report-metrics.json
python3 -B -O round19/review/report_metric_audit.py > /tmp/report-metrics-O.json
cmp /tmp/report-metrics.json /tmp/report-metrics-O.json
```

The commands printed in the report itself name existing positive-component scripts and supported `--check`/`--output` flags; they are to be run from that component directory. The release's top-level replay remains the package-wide entry point.

**Blocking findings: none. Required canonical corrections: none.** If the parent elects to add the optional integer paragraph or otherwise changes the article, the newly rendered PDF needs a new page/reference pass before this exact-byte signoff can be transferred.
