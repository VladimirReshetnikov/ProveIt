# Independent static review of the kernel display-delimiter correction

Reviewer: `/root/intake_e13`. Date: 2026-10-24. **Static delta approval; no unresolved finding.** This supplements the complete original toolchain review and layout delta reviews, most recently the v5 zero-gap review `5b842371c52ddf155e47866fa2b854cb26e5fb846047e1998e5843d71aa4d2da`. I read the entire new code/prose/pin diff, full v5 snapshot and actual-auditor failure, and authenticated the current closure by read-only JSON/file/hash inspection. I did not execute/import/compile the corrected auditor, a renderer, a parent program, TeX/PDF tools or Lean.

The valid displayed D0/D1 polynomials end with commas. The first actual auditor correctly rejected those unconsumed tokens because the previous wrapper removed only a period. I missed that wrapper/parser mismatch in the original static review. It was an implementation acceptance bug, not a changed displayed polynomial or failed coefficient equality. The archived traceback records the failure before any successful mathematical audit; no such success is inferred from the fit result.

The final auditor is `43aa371e2d8594f459b1eb707ab4839e398e471fe6750352b69da7eaaa67c372` (759lines). I verified exact whole-file equality to reviewed v5 after replacing only

    text = clean_math(sections[pos+1]).strip().removesuffix('.')

with

    text = clean_math(sections[pos+1]).strip()
    if text.endswith(('.', ',')):
        text = text[:-1]

This removes exactly one terminal display punctuation character, outside the complete kernel polynomial. It does not remove internal finite-list commas, skip an operand, truncate a polynomial substring or accept arbitrary trailing input. The unchanged `Parser.parse()` must still consume every remaining token; duplicate trailing punctuation or other trailing syntax remains unconsumed/rejected. The complete parsed coefficient dictionary must still equal the whole expected kernel over all four free native ports. Direct actual-TeX control calls bypassing outer pins still enter this same full mathematical audit, so the correction is not a pin-based or coefficient-check bypass.

No other executable byte changed. The renderer remains `e710f96fdddc1c994af56036c9651bb9dd1cc01af5d059f43bb1e6d0b8bf30ed`. Actual TeX remains `e8a590cd71859fdddbd749ddc656b2507187cdae49990fa40de5db0875f8abef`; graph/map and all five live derived rendering artifacts are byte-identical to archived v5. In particular the actual PDF remains `4ae1bdee9aa57c074f14f0790823791724c6032baca42e4b724245476ea554d7`. No formula, kernel coefficient, tuple/seed, font, graph cut, grammar rule, control, subprocess option or deterministic-artifact algorithm changed.

I read all changed README/MAPPING/proof/toolchain wording. It accurately records the successful guarded one-Letter-page9pt/8pt render and the subsequent failed mathematical audit, preserves both evidence sets and leaves corrected auditor/rebuild success pending. The five unchanged live rendering files can be byte-compared by the released renderer; the old receipt/stdout were preserved in the historical snapshot rather than overwritten as if they described new tool pins. Root's preliminary visual inspection is reported as root's result, not my own visual acceptance.

Current TOOL_PINS `5a9587eefbfb45a56cc514f1b9780fda5e055fd2124de6be87c97896613a5cc4` passes all56 external/97 preparation-history-render/four core records with exact hashes and byte counts. SOURCE_PINS `545000fb823bb9eb8f87baf76c1aa15b579628a100e88d32bcec9d0a02c41291` passes all51 external/five core records. Final proof hash is `cc4bf185e1d06c4a28434d5075e9560567531628ad03bfac448fc72a8ec61a8d`; toolchain hash is `dd3879d9f96edb7bbdc77011dad9788006ce44b479820d49c3184df32edc1ddb`.

All five historical inventories pass exact member names/hashes/bytes. The first four retain their thirteen payloads each. The new v5 manifest `f50deea96794c22fd8b2e9b6f6009c7063c8ffa920de7616a8dd77207cddb76f` closes exactly21payloads, including exact old core/pins/renderer, seven successful render files, empty failed-auditor stdout, full failure traceback and notes. The live mathematical/rendering files equal their archived counterparts in full.

Root may decide whether to release the five unchanged commands against this final checkpoint. Actual universal block/coefficient reconstruction, all29 malformed actual-TeX controls, both auditor modes, both byte-exact rebuilds and fresh independent replays remain required; the independent visual obligation remains separate. No source/calibration/canonical/Lean change or mathematical-audit success is supplied by this static approval.
