# Source-only current-base closure survey for ordinary 67/94

The existing `ModelCarrier94` source imports `ModelCarrierCurrent`, the 94 value/syntax and extraction chain, and the generic no-zero bridge. Its complete source-declared project closure has **1,144 modules**: 995 in the 1,000-module current14 base, all 16 of the subsequent 106 extension, and 133 additional modules. This is a source inventory, not a proposed 133-module build.

A smaller **proposed local client** can reuse the already checked `FreshModel106` object for `evalRing_expressionAt65`, `beta_pos` and `shifted_pos`, and use the existing `HACurrentEquation2011.polynomialBridge` for the maintained no-zero/machine bridge. In source terms it needs the closure of `Carrier94Value` and `ArithmeticCarrier94Extraction`, plus an inline copy/adaptation of the small `HAExpressionNoZeroEquiv.bridge` argument. That closure has 129 project modules: 114 already in the current14 base, nine in the 16-module extension, and these **six additional source modules**, in dependency order:

1. `DiophantineConsistency.Carrier94Syntax`
2. `DiophantineConsistency.Carrier94Value`
3. `DiophantineConsistency.ArithmeticPellResidueAux`
4. `DiophantineConsistency.ArithmeticCarrier94Indices`
5. `DiophantineConsistency.ArithmeticCarrier94Soundness`
6. `DiophantineConsistency.ArithmeticCarrier94Extraction`

These six source files have 1,351 physical lines in total. `result.json` records each exact workspace source path, SHA-256 and declared import list, as well as every additional full-closure module and the 180 candidate-object/companion absences checked across the selected overlay, package and toolchain roots. It finds no new *declared external module names* relative to the base-plus-106 inventory. This does not verify every package-transitive provider, dynamic import, or future import compatibility.

The proposed adaptation of `ModelCarrier94` must retain the asymmetry: a maintained zero yields a 94 zero by changing the strong multiplier, while a 94 zero is sent through `ArithmeticCarrier94Extraction.current94_equations` and `ArithmeticCarrier94Soundness.ordinary_halts`; the existing current14 bridge then establishes the no-zero equivalence. It is an existential no-zero transfer, **not** a same-valuation iff. The local source would need to compose this bridge with `IPRAExpressionNative.equivalence_of_bridge` and `IPRAStandardTheory.provable_iff`. A rough estimate is 100–200 new Lean lines after the six modules compile, plus any fixes exposed by a coherent build; this is not a proof-size or success guarantee.

Run the read-only survey with `python3 -I -S -B research/current2011-ordinary94-source-closure-survey/survey.py` from this task directory. The actual observed survey session 6225 exited 0. The survey rechecks the independently audited fresh 106 provider, shared source hashes/imports, source snapshots and candidate absences. It **does not launch Lean**, freeze a new immutable source tree, authenticate the whole package-transitive/dynamic closure, or authorize a build. The existing 16-module producer failed at its final client before its own final pass; the separately successful corrected client and its recorded direct rechecks are the inherited provider evidence.

SHA-256: `survey.py` `8cad29cbe4f09153c7ccff3f630df6a12a52780380051886713ca9bab8fe2583`; `result.json` `d923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821`.

The original survey checked current source bytes across the full closure and compared shared base/106 source hashes and imports for the compact closure. A separately retained follow-up [`survey-full-recheck.py`](survey-full-recheck.py) additionally compared those hashes and imports for **all** 995 base and 16 extension modules in the full `ModelCarrier94` closure. Observed session 47471 exited 0; [`full-source-recheck.json`](full-source-recheck.json) is byte-identical to the original result. The original survey and result remain unchanged. Follow-up SHA-256: `survey-full-recheck.py` `cc25e0dab06503ef3cac7b5bd995e8cbe8fbbe283acc182a4a020ac6b7025c9f`; `full-source-recheck.json` `d923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821`. This strengthens source comparison only and has the same no-build/provider limits.
