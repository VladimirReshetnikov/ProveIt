# Reproducible code and certificates

This directory accompanies the polylogarithm continuation article. All input paths are resolved relative to the scripts. The package can be moved or extracted elsewhere, and the verification commands can be invoked from any working directory.

## Run the exact verification

Python 3.12.14 was used for the recorded verification. Install the matrix-check dependency and run:

```bash
python -m pip install -r code/requirements.txt
python code/run_verification.py
```

The default command is read-only with respect to all reference JSON files. It regenerates the two polylogarithm identity certificates, repeats an independently implemented word replay, checks the zero-expansion coefficient table, verifies rational endpoint signs for the angular zeros, checks the universal Euler evaluator, and runs the finite matrix/normal-form comparisons. It exits with a nonzero status on any failure. Do not use `python -O`: assertions are part of the exact verifiers, and the combined runner rejects optimization mode.

The identity, rational-interval, Euler, and coefficient checks require only the Python standard library. To run that subset without the SymPy matrix comparisons:

```bash
python code/run_verification.py --certificates-only
```

To write a new receipt and detailed log at chosen locations:

```bash
python code/run_verification.py --receipt verification.json --log verification.log
```

An existing file with different content is never silently replaced. The supplied `data/verification_receipt.json` and `data/verification.log` record the packaged run, including hashes of the reference data and executable Python sources.

## What each exact check establishes

| Script | Check and scope |
|---|---|
| `verify_s4_certificate.py` | Rebuilds all 854 double-shuffle and 15 octahedral rows and exactly sums their rational coefficients to the weight-five target. |
| `prove_s2.py` | Replays the 23 double-shuffle and 2 octahedral rows proving the weight-three companion. The default invocation verifies only. `--rebuild` repeats the small exact search and compares its result. |
| `independent_s4_replay.py` | Rebuilds both targets and all certificate rows without importing `octet.py` or either original verifier. Shuffles use position subsets; stuffles use positive Li merges followed by the depth-sign conversion. |
| `octet.py` | Defines the iterated-integral word conventions and generators. Inputs are checked for endpoint admissibility; regularized rows allow exactly one divergent singleton factor. Generating the optional large search matrix requires an explicit `--dump PATH`. |
| `kernel_normal_form.py` | Gives exact normal forms and separating integer witnesses for the odd-weight, level-four product-only row module in quadratic arithmetic operations. It does not decide all analytic polylogarithm relations. |
| `verify_rank_parametrization.py` | Checks the explicit integral kernel generators and ranks against the pinned upstream matrix in odd weights 3 through 13. |
| `verify_normal_form.py` | Reduces every upstream row in odd weights 3 through 15, checks deterministic test targets/witnesses, and checks the even full ranks in weights 2 through 12. |
| `check_general_level.py` | Independently constructs coefficient-only matrices and checks exact ranks for levels 3 through 9 and weights 3, 4, 5. The all-level theorem itself is proved in the article. |
| `all_order_zeros.py` | Generates the exact rational mode coefficients. Verification compares every supplied table entry and substitutes the expansion into its equation through all scales below the supplied cutoff. This checks finite truncations; analytic remainder bounds are in the article. |
| `certify_zeros.py` | Replays the saved rational endpoint sign certificates with exact Taylor and Fourier-tail bounds. It does not call the floating-point root proposer during replay. Existence follows from opposite signs and continuity; uniqueness is proved in the article. |
| `universal_euler.py` | Computes rational Gaussian Euler enclosures and checks them against an independent exact weight-two reference, including the two Euler-sum implementations and the tail bound. |

Finite rank checks support reproducibility and catch implementation mistakes. They are not the proof of a formula at all weights or levels. The article contains the complete polynomial and character proofs. Similarly, numerical agreement is never used to accept either polylogarithm identity certificate.

## Numerical diagnostics and new proposals

Floating-point work is optional and separately labelled. To install its dependencies and run it:

```bash
python -m pip install -r code/requirements-numerical.txt
python code/run_verification.py --diagnostics
```

`diagnostics.py` checks 360 angular roots and sampled monotonicity/log-concavity inequalities using mpmath, NumPy, and SciPy. These are numerical diagnostics, not formal or interval certificates. The recorded exploratory data are in `data/diagnostics.json`. Regenerating them across library versions can change final floating-point digits; the exact verification does not assert byte-for-byte equality of regenerated numerical diagnostics.

`certify_zeros.py` uses mpmath only to propose new brackets. Acceptance of a proposed bracket is still determined entirely by rational arithmetic. For example:

```bash
python code/certify_zeros.py --quick --output new_brackets.json
python code/all_order_zeros.py --cutoff 12 --output zero_coefficients_to_12.json
```

Both commands require a fresh destination or identical existing content. The all-order generator checks its requested cutoff in addition to the fixed comparison cutoffs. The supplied older coefficient JSON contains its original checks at 4 and 8; the portable verifier also checks its actual table cutoff, 9.

## Reference data and provenance

`../data/` contains the two exact word certificates, the rational zero brackets, the coefficient table, the universal Euler self-test receipt, the finite matrix comparison receipts, and the optional numerical diagnostics. The runner compares or reads these inputs without rewriting them.

`upstream/full_ds.py` and `upstream/gaussian.py` are unchanged copies from ProveIt commit `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`; see `upstream/README.md` for their original repository paths and SHA-256 hashes. These copies ensure that the rank checks test the same precise matrix family as the source manuscript.
