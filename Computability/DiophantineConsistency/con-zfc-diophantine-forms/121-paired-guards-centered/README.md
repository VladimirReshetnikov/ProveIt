# Paired guards and centered carriers for Con(ZFC)

This research release supplies 18 explicit Diophantine-polynomial evaluators,
ordinary arithmetic proofs, exact finite checkers, complete literal coefficients,
and the retained source/calibration dependencies. It does **not** prove Con(ZFC),
find a zero, prove a global optimum, or claim a new end-to-end proof-assistant
certificate. The Con(ZFC) interpretation is conditional on the imported ordinary
native/C222/signed-Pell/calculus dependencies, whose full transitive binding
is not independently re-established by this round. The equivalence statements use the inherited calibrated source
and the precise integer/positive-integer domain stated for each family.

## Read first

- `report/report.pdf` and `report/report.tex`: combined research report, when included in the final release.
- `RESULTS.json`: machine-readable endpoint inventory and scope.
- `integer/PROOF.md`: eleven-integer paired/fused-norm reductions and evaluator improvements.
- `lowdegree/PROOF.md`: fifteen-integer degree-48 centered carrier; `lowdegree/twelve/PROOF.md`: credited degree-500 evaluator optimization.
- `positive/PROOF.md`: six ten-positive-integer transport/centering tradeoffs.
- `alternative/PROOF.md` and `alternative/CALIBRATION.md`: direct quartics with 493 and 489 unrestricted integer variables.
- `review/`: independently written audits and proof reviews, with corruption controls.
- `DEPENDENCIES.md`, `LICENSES.md`, and `CODE_REVIEW.md`: source closure, licensing, execution boundary.

The integer packet includes three dominated diagnostic evaluators as well as its
five count/degree tradeoff points. Fixed coefficient ports are **not variables**.
Every live binary addition, subtraction, and multiplication is counted, including
multiplications by fixed numerals. Exact total degree is distinguished from a
syntactic upper bound and from operation count.

## Reproduce offline

Tested with Python 3.12.14 and SymPy 1.14.0. Python 3.11 or newer is recommended.
Install the pinned dependency in your chosen environment if it is not available:

    python -m pip install -r requirements.txt
    python -B reproduce.py

The replay itself performs no installs, network requests, shell execution, or
proof search. It first validates every distributed static byte against
`MANIFEST.json`, checks all four producer manifests and the original inherited release manifest,
and validates
ZIP CRC and a byte-for-byte local archive roundtrip. It then makes **separate
isolated temporary copies** for normal Python and `python -O`.

For each mode it deletes and rebuilds all 39 deterministic generated
JSON equations/specifications/metrics/projection certificates, then compares
**every byte** to the distributed versions. It runs producer and independent
audits, regenerates and compares deterministic receipts, reconstructs all six
integer/lowdegree numeral payloads, checks the unchanged coherent positive tuple,
runs semantic and integrity corruption controls, and independently compares
72 report display blocks plus seven new twelve-variable prefix formulas. Inherited prior programs
are not run or altered. Generated receipts and logs are written **outside the release**, by default to
a sibling `ConZFC_Paired_Guards_Centered_Carriers_replay/` directory. Select an
external destination with `--receipt /path/to/replay.json`. No release file,
producer or dependency file is modified. The frozen `REPLAY_SUMMARY.json`
records the completed pre-distribution replay and is covered by the manifest.

The exact executed commands, return codes, durations, output hashes, byte
comparisons, and log paths are in the external replay receipt. A failed stage aborts the run;
there is no silent skipped audit. Finite checks supplement the unbounded proofs.

To check the final ZIP after downloading or creating it:

    python -B reproduce.py --verify-only --archive ../ConZFC_Paired_Guards_Centered_Carriers.zip

Without `--archive`, the replay validates a fresh local ZIP roundtrip, not an
unseen final download. `--verify-only` does not rerun mathematical checks.
A manifest is a local integrity inventory, not an authenticated signature.

## Release-maintainer notes

`seal_release.py` intentionally regenerates the static manifest. Do **not** run
it to make an unexpected integrity failure disappear. After an intentional,
reviewed report or source update, run it, then rerun `reproduce.py` and check the
final ZIP. The manifest excludes itself, and Python cache files. All static files, including the frozen replay summary,
are covered. TeX/PDF bytes are integrity-checked; TeX is not executed
by the Python replay. PDF compilation and visual QA are separately documented.

The larger research baseline is not distributed wholesale. `baseline/` retains
the dated review, authenticated snapshot index, selected cited source evidence,
and the late-head attribution evidence. `SELECTED_EVIDENCE.json` identifies
exactly which baseline files are included. Attribution and novelty are bounded
to the inspected snapshots, not asserted literature-wide.

To create the release ZIP deterministically after a successful replay:

    python -B make_release_zip.py --output ../ConZFC_Paired_Guards_Centered_Carriers_2026-10-24.zip

This builds the archive independently twice, requires byte identity, validates
CRC, and writes a SHA-256/CRC receipt next to the ZIP. Fixed timestamps and
permissions prevent machine metadata from changing the archive.
