# Round 20 integrated article review

**Verdict: PASS for the integrated 24-page report, its stated ordinary-proof boundary, and the selected literal metrics. No blocking mathematical, transcription, or layout defect found.**

Reviewed 25 October 2026. This is a separate AI-assisted article/artifact review, not outside human peer review, repository acceptance, a fresh end-to-end Lean/Rocq certificate, or a decision of consistency. No canonical component or report file was edited.

## Exact reviewed article and visual review

- PDF: `round20/render/main.pdf`, 24 letter-size pages, 437,410 bytes.
- PDF SHA-256: `28d1dda4ed907c45031483c0b9813adfab9db084a7574be7231a6f98950edc4e` (the exact authoritative value is also recorded in `report_layout_evidence.json`).
- All eight canonical `.tex` inputs in `package/ConZFC_Unsquared_Factors_Linear_Selectors/report/` were compared byte-for-byte with the render inputs. The four mathematical sections and both coefficient appendices also equal their staged component versions.
- **Every page, 1–24, was rendered to PNG at 110 dpi and visually inspected individually.** No clipping, overlapping text, broken symbols, cropped equations, table overflow, or footer/page-number defect was found. Both 436-character constant seeds and both tile tables are legible. The contents, section transitions, equation numbers, and appendix headings are coherent.
- A fresh four-pass TeX rebuild was performed in `review/article_tex_replay/`, without altering the canonical report. The final pass had **zero overfull boxes, zero underfull boxes, zero unresolved references, and no rerun request**. `.aux`, `.toc`, and `.out` were unchanged between passes 3 and 4. All 24 page content streams exactly match the visually inspected PDF; extracted layout text is identical too.
- There are 23 unique labels and 17 explicit references; every reference resolves. The C1–C3 tagged displays are consistently cited as literal tags. All ordinary numbered equations (1)–(17) were checked in context.

The local system's bare `pdflatex` has no installed format lookup. This was safely resolved for review with the already available `round18/tex_runtime/pdflatex.fmt`, font map, and explicit system font paths. No permission escalation or package installation was necessary. A normally configured TeX Live installation is sufficient for the release's build script.

## Literal selected metrics, independently collected

`check_report_metrics.py` is a new standard-library-only census. It independently squares and fully collects **every residual**, checks the supplied complete expansion coefficient-for-coefficient, verifies exact degree and coordinate liveness, and compares the final files with their staged counterparts. Its normal and `python3 -O` receipts agree byte-for-byte.

| Domain/profile | Variables | Rows | Exact degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Natural, dimension (`natural206`) | 206 | 158 | 4 | 8210 | 130686376 |
| Natural, balanced (`balanced207`) | 207 | 159 | 4 | 5278 | 69238087 |
| Natural, sparse (`sparse208`) | 208 | 160 | 4 | 5198 | 65866712 |
| Integer, dimension (`integer239`) | 239 | 175 | 4 | 12658 | 6144 |
| Integer, balanced (`integer240_balanced`) | 240 | 176 | 4 | 5232 | 4096 |
| Integer, sparse (`integer240_sparse`) | 240 | 176 | 4 | 4927 | 7596 |

All three integer endpoints have maximum residual coefficient 64, as stated. The natural row-shear counts 25/30/33 and pre-basis contraction counts are correctly distinguished from the selected post-basis metrics. The older ordinary-review tables describe frozen pre-basis controls, not the final points, and explicitly reserve later row-basis census; the integrated article correctly uses the actual final points.

Independent live-DAG traversal confirms:

| Circuit | Variables | Exact degree | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|---:|---:|
| Positive radix67 principal | 10 | 304 | 51 | 18 | 16 | 85 |
| Positive whole47 principal | 10 | 304 | 51 | 18 | 16 | 85 |
| Integer root certificate | 13 | 152 | 71 | 24 | 24 | 119 |

Exact degrees are supported by the complete checked leading forms/cancellation cuts, not by a naive DAG degree bound; the root DAG's naive bound 172 is correctly disclosed. The 84/410 positive control is correctly described as dominated. The 13/152/119 point is correctly compared with 13/152/126 and identified as a tradeoff against 13/156/117.

The matched predecessor quartic figures agree with the retained incoming baseline census and actual predecessor equations, including natural 219/171/8267/130686428 and 221/173/5253/65867916, shared-factorial 240/177/21482/6144, and factorial-free 242/178/5018/7968. No comparison silently switches domains or implies a global variable record.

Every staged component file matched its canonical source at inspection: natural **274**, integer **253**, positive **206**, roots **212** files, **945 total**, no missing source and no changed bytes. Exact per-equation hashes and coefficient counts are in `report_metric_evidence.json`.

## Ordinary proof and equation review

The report's displayed polynomial definitions and proof order agree with the corresponding ordinary reviews and inspected literal components.

1. **Natural branch:** `Z²+T²=R` preserves the entire local source, including evaluation quotient and beta squares. Soundness restores old natural gates pointwise. Completeness is correctly restricted to canonical CRT lifts, not falsely asserted for every old witness. The ordering fixes `N` before arbitrary `N²` lifts, makes every oriented factor positive, and chooses the anchor/base afterward without a sign/size cycle. The unchanged anchor dominance and pooled carry bounds are stated. Later monic restorations and row operations are kept conceptually distinct from this semantic change.
2. **Integer branch:** the lcm proof and `F>Λ_t²` bound justify `R=F` using the correct two-sided selector interface. The report excludes `q=0,-1` by the literal mod-four condition, excludes `q=1` before binomial decoding, authenticates the binomial at either radix sign, and only then concludes positivity. It handles `y=F` explicitly, preserves all-primes completeness, and states the correct stored-radix restoration `stored_q=4z+2`. Semantic zero-existence arguments are not mislabeled as predecessor witness bijections.
3. **Positive branch:** the inverse cubic is integral only after rank parity. The prime-3 obstruction is explicitly exhibited; `q^4` authentication precedes projection, and full `q^6` recovery is correctly delayed until `q` is dyadic. The negative corrected quotient is handled by the direct positive bound, not a stale nonnegative-quotient claim. The native source base `Y(X+1)+2` is distinguished from the auxiliary base `A`. Every printed definition and the main carrier match the literal checked graph.
4. **Root branch:** the exact relation is the whole-polynomial shear `P_new(n)=P_incoming(n-k)`, with inverse `n_new=n_old+k`; it is not an identity at unchanged coordinate names. Both leading cancellations are retained. The norm proof handles negative/zero/shared square classes, all signed roots, unit-factor alternatives, and rational-root integrality. The direct fifteen-variable maps and thirteen-variable bijection have appropriately different stated strengths.

The principal new arithmetic is not represented as a fresh proof of the inherited native/C222/ZF/ZFC calibration. Scope statements consistently exclude a consistency decision, global minimum, claimed literature-wide priority, new encoding theorem, new end-to-end formal kernel endpoint, or external human endorsement.

## Whole complemented-label radix47 binding

This sidecar is not just arbitrary free-port substitution. The report explicitly identifies the whole incoming complemented-label tuple, distinguishes it from conditional47, retains the actual whole47 decoder/controller, and matches the native interface with `W_native=w`, source transport `t+1`, and fresh source Pell witnesses at `Y(X+1)+2`.

All four raw numeral payloads were independently decompressed and digest/bit-length checked. Their aggregate sizes are **295,388 bytes** for radix67 and **207,214 bytes** for whole47; maximum port sizes are **592,884** and **415,904** bits. The sidecar's free-port rows are identical to the canonical new rows and its ports exactly match the retained incoming whole47 binding. Its source pins include the complete retained native bridge and dependencies. The article correctly credits prior encoding and does not import an old67 decoder into whole47.

Both complete coefficient appendices were diffed against their exact retained source recipes. The only changes to the constant specifications are the advertised `K` → `K_0` renaming, typesetting/layout, and removal of standalone document wrappers; both entire 436-character seeds, all finite ranges, tile tables, and formulas are unchanged. The article independently retains the omitted standalone formalization caveat in its main scope discussion.

## Commands and citation

All five printed commands were executed successfully **from the staged release root**:

```
python3 -B positive/build.py --check
python3 -B positive/verify.py
python3 -O -B positive/verify.py
python3 -B positive/radix47/build.py --check
python3 -B positive/radix47/verify.py
```

The two main verifier stdout receipts agree byte-for-byte and include the whole47 check. They confirm 37 exact cuts per positive graph, 274/3750 complete leading-form terms, and 171/169 actual rejected corruptions. These finite checks are correctly distinguished from unbounded arithmetic arguments. The top-level replay implementation was inspected and matches the report's stated disposable-copy/normal-and-optimized plan; sealing and final ZIP replay remain the release integrator's separate responsibility, not an assertion of this article-only review.

The Chan–Norrish citation was checked against the authors' primary hosted journal PDF: [Proof Pearl: Bounding Least Common Multiples with Triangles](https://trustworthy.systems/publications/full_text/Chan_Norrish_19.pdf), *Journal of Automated Reasoning* 62 (2019), 171–192, DOI `10.1007/s10817-017-9438-0`. Its Theorem 3 indeed gives the claimed `LCM(1,...,n)≤4^n`; author names, title, volume, pages, year, DOI and theorem number are correct. The initially inaccessible DOI resolver was not treated as a bad citation.

## Nonblocking polish notes

1. The final TeX pass has one amsmath warning, `Foreign command \\over`, caused by three uses of `\\over` in the positive section (lines 114, 265, 266), including `{|b|\\over q^6}`. It renders correctly and is neither an overfull box nor a reference defect. Optional conversion of the three uses to `\\frac{...}{q^6}` would silence it; it is not required for the present zero-overfull/stable-pass acceptance.
2. Some positive-section/appendix source paths are component-relative (`inherited_lucas/...`, `SOURCE_PINS.json`, `radix47/inherited/...`) whereas executable examples are release-root-relative. Their targets exist under `positive/` and are unambiguous in context. Optional explicit `positive/` prefixes would improve integrated-report navigation. No printed command is broken.

## Evidence and stopping condition

Evidence files: `report_metric_evidence.json`, its identical normal-mode copy, `report_layout_evidence.json`, `check_report_metrics.py`, normal/optimized metric logs, five command replay logs, all 24 `report_page-*.png` files, and `article_tex_replay/` logs/auxiliaries. The requested integrated report review is complete. There is no unresolved blocker; final sealing/ZIP production and any subsequent text changes must be bound to their own final receipts.
