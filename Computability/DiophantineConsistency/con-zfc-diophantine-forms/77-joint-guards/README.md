# Joint sign guards and Pell descent for smaller consistency equations

This packet gives explicit new polynomial reductions toward a fixed equation whose lack of solutions is equivalent to syntactic Con(ZFC), with each variable domain stated separately. The arguments are ordinary mathematics composed with named inherited Pell, native compiler and literal K215/refutation-calibration results. They are not a new end-to-end Lean/Rocq or encoded internal-ZFC proof, a consistency decision, or a global simplicity minimum.

## Main results

Unrestricted-integer family:

- 37 variables, degree 4; 31 variables, degree 6.
- 25 variables, degree 8; 23 variables, degree 12; 22 variables, degree 16.
- Further monic projections provide 21 variables at degree 20, 20 at degree 32, and 19 at degree 88. See the exact projection packets and separate independent checks.
- The 26-variable octic and 24-variable degree 12 polynomial are retained as useful restoration/checkpoint forms.

Strictly positive-integer family:

- Eleven variables, exact degree 277, 111 live binary operations.
- Eleven variables, exact degree 257, 114 live binary operations.

The eleven-variable endpoints are a degree/cost tradeoff. They use the same complete compact44 tuple, 295,388 raw coefficient bytes. The integer family uses the coherent source34 tuple and calibrated guard constants instead; ports are not interchanged between tuples. Operations count every live binary addition, subtraction and multiplication, including scalar products and squaring; fixed numeral leaves and reuse are free. The shared literal circuits use 127 operations for 25/8, 121 for 23/12, 118 for 22/16, 115 for 21/20, 112 for 20/32, and 109 for 19/88. The 121-operation count refers to the V-elimination 23-variable form, not the separate I-elimination form with 2,968 expanded monomials. These are reproducible live-DAG counts, not globally minimal circuits.

The direct proof-checker work supplies smaller exact local graphs for pairing, unpairing, projections, conditionals and list heads. The inert-prime CRT closure removes an encoded index and one variable-power graph. These are reusable interfaces, not additional completed small consistency equations; factorial/binomial/power compilation and the global checker remain explicit work.

## What to read

- `report.pdf` is the integrated report; `report.tex` and component `section.tex` files are its sources.
- `guards/PROOF.md` and the eight literal guard packets explain residue-oriented cone/determinant compositions.
- `joint/PROOF.md` and the projection proof explain simultaneous positivity and exact integer-polynomial restoration.
- `circuits/README.md` describes the six shared literal DAGs and their exact residual binding.
- `pell/PROOF.md` and `pell/CENTERED_PROOF.md` prove the denominator-guard deletion and centered sign bootstrap.
- `certificates/INDEX_FREE_CRT.md` and `certificates/LOCAL_GADGET_PROOFS.md` state the direct-route interface gains and their limits.
- `review/` contains separate mathematical and algebraic checks; `baseline/BASELINE_REVIEW.md` records the fresh input comparison and formal boundary.
- `DEPENDENCIES.md` identifies inherited results and fixed-coefficient conventions.

The eight original wave-ten ZIPs are retained unchanged under `incoming/`, pinned to arrival commit 9513bd88cefb762dc07e1872be3078d14aca63fe. The repository checkpoint is 2605669a532342f153b13eb6b4a0af4b54f5fa37. Immutable URLs, Git blobs, SHA256 values and byte lengths are recorded in `INCOMING_PINS.json`. The original extracted trees are not duplicated in this archive; the verifier authenticates and expands them into its temporary working copy.

## Reproduce

Use Python 3.12 with SymPy installed (the audit used SymPy 1.14.0). There is no network use or automatic dependency installation in the verification commands.

    python verify.py --manifest-only
    python verify.py
    python negative_controls.py

The root replay checks the sealed release, authenticates and extracts all eight original inputs, rebuilds the new polynomial packets and fixed numerals, runs author and independent checks including optimized Python phases, and compares the rebuilt artifacts with the delivered bytes. It leaves the delivered source tree unchanged. `REPLAY_COMMANDS.json`, `REBUILD_FILES.json` and `REBUILD_NUMERALS.json` make its exact scope explicit. Gzip container headers are not part of the mathematical integer identity; regenerated coefficient payloads are compared after decompression.

To rerun the original eight package roots as well, including their seven supported optimized roots:

    python verify.py --replay-originals

This additional replay can take longer. Its scope is still finite algebra/data verification. The original signed-bootstrap root intentionally rejects a global `-O` invocation and runs selected optimized checks internally. The new root driver is also run normally and dispatches its own explicit optimized phases.

To rebuild the report, run `bash build_report.sh` with a standard PDFLaTeX installation. Report reconstruction is separate from arithmetic verification; proof-assistant compilation is not part of either command.

## Proof boundary and comparison

All source-zero transformations have ordinary unbounded proofs; finite diagnostic searches are not used as substitutes for them. The repository now checks a complete external numeric sealed-ZFC refutation checker, many native arithmetic steps, and internal local quartic semantics. Whole native payload/phase/global calibration and the complete checker interpretation over nonstandard internal proof codes remain open, as does the final encoded object-language biconditional.

The current nine-positive lower-cost repository target remains 443 operations at degree 1,845,940, with a different degree 1,379,730/478 alternative. Older unrestricted 10-, 13-, 14- and 16-variable high-degree forms also remain relevant. Positive 20-variable octics are not unrestricted 20-integer equations. No scalar size metric makes this packet uniquely simplest.
