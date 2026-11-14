# PA194H6

PA194H6 is a new 194-working-state binary single-tape blank-start machine. It combines coefficient-six formula encoding, no-push modus ponens, and cached-only Shift. No machine below 194 states was obtained. This release supplies the requested materially different 194-state fallback.

The ordinary mathematical proof of

    PA proves: not Halt(PA194H6, blank) iff Con(PA)

uses the explicitly retained numerical-calculus/PA calibration and adds exact source and physical composition checks. It is not a newly kernel-checked end-to-end Lean/Rocq theorem or iPRA equivalence.

## Read first

- `report/main.pdf`: complete report, all 194 table rows, full 34-class frontier, and 51-packet comparison.
- `report/main.tex`: editable LaTeX source.
- `machine/machine.tm`: definitive machine.
- `comparison/`: exact offline graph novelty verifier, independent source/table audit, and complete census data.
- `research/`: the scanner counterexample and bounded unsuccessful reduction searches.

Run `python3 -B verify_all.py` for release integrity, complete positive machine verification, independent source audit, exact novelty comparison, and scanner witness. The optional heuristic searches are not required.

## Files and conventions

`machine/machine.tm` is definitive: states 0 through 193, start 0, separate terminal label 194. Every row is `state read write L-or-R next`. The two-way infinite tape is initially all zero; head position 0. There are 388 rows. Native numbering starts 74 and halts 254; labels.json is the exact dense-to-native bijection.

Dense SHA-256:

    4bae5b0a698583d97ae8527472dfb627c1cecbba9babd88159fe94c1e3e7dc17

Native SHA-256:

    9c1daeb54c6e2e402bc5a0405925c1137c19e26280bcf455efe4c91d9a61111d

The main mathematical contribution is documented in `proof/pa194h6_preservation.tex`. All inherited logical proofs are retained as source under `references/logical/`. Complete machine, source, fold, and independent symbolic artifacts are under `machine/`.

## Fresh checks

- 135 fixed controls + 67 AX readers - 8 folds = 194.
- 3,775 primitive source sites; 4,876 universally checked outcomes.
- 32 local history/read-bit cases establish the simultaneous quotient.
- Construction checker: 1,567,458 symbolic operations; maximum 508.
- Independent literal checker: 1,139,739 operations; maximum 403; minimum positive-duration constant 3. Four list lemmas are rederived from literal rows, without compiler imports or arithmetic-box oracles.
- Whole blank startup: 58,088 transitions, complete tape equality.
- Exact source check: restoring the coefficient-four multiplier yields the supplied PA194H graph. Exactly 61 blocks change from four increments to six; all 3,409 other sites and every successor relocate exactly, with no outside entry into a replaced block's interior.

## Reproduce

Python 3.10+ and its standard library, with assertions enabled:

    python3 -B verify.py

This checks input pins, command identities, exact source binding, a complete rebuild, all construction contracts, dense/native identity, all folds, full startup, and the independent literal-tape contracts. Fresh evidence is written to a temporary directory; release files remain unchanged. Use `--receipt /absolute/path/result.json` to retain the result. `--quick` skips the independent literal replay only.

The theorem is supported by ordinary proof and universal symbolic certificates. Finite startup simulation is used only to establish the exact initial frame, not to infer infinite nonhalting.

## Material difference

PA194N6's Shift tests `t+h=1`; PA194H6 tests `h=1`. Hence on `(1,0,0,0)` the former halts, while the latter proceeds to `(0,0,0,0)`. The proof compiler must finish a refutation with Pop, not plain Shift. PA194H/HS use coefficient four, whereas this machine uses coefficient six in both generated formulas and MP matching. The recurring source semantics therefore differ from each predecessor.

The symmetric-comparison controller cannot be combined by blindly reusing its state 330: coefficient six already uses 330 for its three-increment block, and both supplied folds consume state 41. The delivered H6 uses the ordinary cached-only comparator, with the verified existing eightfold allocation.

## Provenance

Source snapshot: `VladimirReshetnikov/ProveIt@3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.

Inputs come from `docs/incoming/pa194n6_research_2026-11-13.zip` and `docs/incoming/pa194hs_conpa_2026-11-13.zip`. Existing compiler, symbolic engines, generic constructor mathematics, and PA calibration retain the supplied attribution and licenses. The new work is the H6 composition, its source-binding certificate, fresh universal checks, and proof specialization.

## Audit and reduction scope

The pinned corpus contains 51 research deliveries: 47 placed packets and four incoming archives. The complete numeric-table census recognizes 2,049 occurrences, 683 byte forms and 487 graph classes with a spanning root. Its 194-state frontier has 208 occurrences, 62 byte forms and 34 classes, including auxiliary and rejected tables. The novel H6 graph matches none even allowing state renaming, any spanning root, tape reflection and global bit exchange; complete tuples decide equality. The byte-identical duplicates HS/NS, CSZ/X and the two N6 deliveries are recorded.

Five time-bounded decoder searches used 36,567,758 proposal slots (not distinct machines) without reaching a state-count score below 194. Fresh H6 screens tested 62,073 row-choice merges and two different bounded local contraction rules, with no survivor. The six-zero scanner deletion fails its old contract on a context actually reached by the parent from blank: its exit head is -1 rather than -2 on the same tape. These negative findings do not establish minimality.

## Report build

With a standard TeX Live installation, run twice from `report/`:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The PDF was compiled from this source and visually inspected. All fonts are embedded.
