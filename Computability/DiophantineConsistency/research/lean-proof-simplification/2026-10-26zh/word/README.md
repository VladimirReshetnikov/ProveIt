# W1 — exact marker-only terminal kernel response (optional semantic extension)

## Result first

The two old terminal coefficient calculations can be factored through a **new exact twenty-field theorem**, valid for every `1991 ≤ h < 2011`:

\[
 (K*c)(\operatorname{base}(j)+h)
 = [h=2008]m(j)
   +\sum_{e:\mathrm{Entry}}[h+\operatorname{position}(e)=2009]\,2w(e)m(j).
\]

Here `c` is the actual assembled word, `m` its marker map, and brackets denote an indicator. Both marker and dummy maps remain arbitrary **natural-valued** maps. No Boolean-marker, tile-matching, carry, temporal-rotation, high-mask, or positive-transport premise is added.

**This is not a net source deletion.** With all helpers and public compatibility theorems included, the candidate costs **+19 physical lines, +11 nonblank noncomment code lines, and +353 tokenizer tokens**. The old endpoint clients become simpler, but the stronger interface costs more than those savings. Recommend only as an optional semantic factorization if the full terminal band is wanted; do not include these changes in a claimed deletion total.

## Exact artifact and source contract

- Pin: `09d65a93c9df8684c1a226341d6a5120623d1cdb`.
- Source: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordTopBounds2011.lean`.
- Full standalone replacement: `candidates/CurrentWordTopBounds2011.lean`.
- Unified patch: `patches/marker_tail.patch`.
- All 16 original public theorem signatures, all existing imports, and the `omit [NeZero N]` scope are preserved.
- The existing `top_bare_zero` theorem is retained. Its axiom-check client therefore need not be deleted or edited.
- Upstream files were not modified. No Lean installation, Lean compilation, incoming-code execution, push, or network mutation occurred.

## Why the formula is correct

1. For `986 ≤ e < 2011`, the assembled cell has no tile-data block and no dummy slot. Its exact digit is `if e = 1004 then marker j else 0` (`word_marker_tail`).
2. In the terminal band, the bare displacement18 reads residues1973..1992, and displacement2020 reads residues1982..2001. Both intervals are outside `lowSupport`, including across the predecessor-cell wrap and when `N = 1` (`tail_outer_bare_zero`).
3. The bare displacement1004 reads the same-cell interval987..1006. Its sole possible supported digit is marker1004, precisely at target `h = 2008`. **This collision must not be dropped.**
4. Every reflected source is exactly `h - 1005 + position e`. Since `position e ≤ 985`, its local coordinate lies in986..1990. It contributes exactly when that coordinate is1004, equivalently `h + position e = 2009`. Thus all surviving contributions factor through the *same cell's* marker, not a shifted marker.
5. At2009, `position e = 0`, and the existing `position_injective` together with `physicalPosition_zero` selects only the Start entry. At2010, no natural position can satisfy the equality. These recover both old public coefficient theorems.

The interval is sharp for the **actual constructed word**, not merely for a hypothetical supported array: take `N = 1`, tile0 (Start), dummy0, and marker0. Start has west color2; its complementary west bit at985 is `253 / 128 % 2 = 1`. At target1990, reflected coefficient position0 reads this bit. Every other kernel source vanishes. The actual coefficient is `2 * selectorWeight(start) = 69,752,854,530`, whereas the proposed marker-only formula extended to1990 would give0. No matching premise is required by either the original or proposed theorem, so this is an in-domain counterexample.

## Full accounting

The changed source section grows from **87 to106 physical lines**, **78 to89 code lines**, and **997 to1350 tokenizer tokens**. The whole module grows from259 to278 physical lines and219 to230 code lines.

| Declaration | Old code lines | New code lines | Difference |
|---|---:|---:|---:|
| `word_zero_high` | 8 | 4 | -4 |
| `top_bare_zero` | 16 | 14 | -2 |
| `top_reflected_source` | 6 | 6 | 0 |
| `convolution_2009` | 30 | 15 | -15 |
| `convolution_2010` | 18 | 7 | -11 |
| new `word_marker_tail` | 0 | 9 | +9 |
| new `tail_outer_bare_zero` | 0 | 12 | +12 |
| new `convolution_marker_tail` | 0 | 22 | +22 |
| **All declarations** | **78** | **89** | **+11** |

All helper signatures, proof terms, and compatibility wrappers are charged. No new imports or shared-context costs are hidden. The tokenizer is explicitly the regex in `build_candidate.py`, **not Lean's parser token count**. Physical-line accounting includes comments and blank lines. The checker and research notes are supporting artifacts, not proposed production Lean code; their sizes are not silently included in the Lean delta.

## Novelty boundary and exclusions

The baseline reviewer searched both exclusion directories, including fresh incoming reports. No earlier exact1991..2010 marker-only response or2009/2010 terminal-factorization proposal was found. The new module names likewise were not named in prior textual proposals. This absence is evidence from the reviewed corpus, not a universal literature claim.

Nearest assumed-applied contracts:

- **E17** already supplies aligned cyclic residue arithmetic and support-zero interfaces. Sources: `research/lean-proof-simplification/2026-10-26a/source_notes/digits-review.md`, lines166–202, and `2026-10-26b/report.tex`, lines583–616. Their clause/marker offset elimination is not counted as new here.
- **E54** weighted finite-fiber pushforward and **LE21** sparse-placement interfaces are also already assumed. No new abstraction credit is assigned to rewriting a finite sum or preserving collisions.
- **E16/E53** equation-side carry/reset/quotient interfaces, **LE20** origin decrement, and **LE27** word-representation boundaries are not re-proposed.

The marginal conclusion here is the concrete exact *whole twenty-field response* with the exceptional bare collision and a sharp lower threshold. It is not a new generic modular helper, a carry reset, a global high-mask theorem, or a whole-word completeness result.

The inspected `CurrentWordConstruction2011`, `CurrentWordCopies2011`, `CurrentWordLowMask2011`, and `CurrentCarryConstruction2011` routes did not yield a separate recommendation after charging helpers and respecting the assumed baseline. In particular, merely sharing carry facts, reusing origin decrement, or moving whole-cell translation was excluded rather than advertised as new.

## Verification and limitations

`verify_word.py` is a **read-only checker written for this research task**. Its stdout is captured in `validation.json`. It checks:

- all16 old theorem signatures, unchanged imports, preserved domain omissions, and unchanged source outside the priced section;
- exact binding of the new theorem statement to the finite-model specification;
- 19,720 reflected geometry cases and60 bare geometry cases;
- 256,360 cyclic reflected cases for `N ∈ {1,2,3,7}`, all cell positions including the final cell;
- 1,040 full weighted convolution cases with arbitrary numeric marker values, including values greater than1;
- a counterexample to deleting the bare2008 term (77 versus76 in the model);
- the actual Start-tile counterexample at1990, using the independently inspected literal Start data and selector-weight recipe.

Finite full sums use arbitrary small coefficient weights, not an authenticated expansion of the942-tile weight table. The Start counterexample needs only the actual Start coefficient, because all other terms vanish. Neither finite arithmetic nor text checks establish universal quantifiers or Lean elaboration.

**Lean compilation and axiom checks were not run.** Existing source theorem names and argument shapes were inspected, and independent source review checked proof domains and arithmetic. These are still *uncompiled Lean candidates*. In particular, native numeral-cast rewrite matching and elaboration of the finite-sum simplifications remain subject to the ordinary Lean build gate.

Reproduce local evidence without executing repository scripts:

```sh
python lean_simplification_round4/word/build_candidate.py
python lean_simplification_round4/word/verify_word.py
```

Both scripts default to the sibling `baseline/` tree in the extracted release package. In the research workspace, where the pin is named `upstream/`, pass `--baseline-tree lean_simplification_round4/upstream`. All text files are read as UTF-8. Both scripts reject any source `CurrentWordTopBounds2011.lean` whose SHA-256 differs from the reviewed pin.

`build_candidate.py` writes only this candidate directory and associated local accounting/patch artifacts. The checker itself performs no writes. Neither script installs dependencies, invokes Lean, imports incoming programs, or touches upstream.
