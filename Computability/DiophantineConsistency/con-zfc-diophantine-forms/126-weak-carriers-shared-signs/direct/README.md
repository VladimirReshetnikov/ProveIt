# A direct 478-integer quartic

The selected final equation is exactly the sum of the squares of the 305
quadratic residuals in `equation.json`. Every one of its 478 variables ranges
over all integers. `expanded_polynomial.json` gives every one of the 5,484
collected monomials with its literal integer coefficient. The exact degree
is four and maximum absolute coefficient is 511,326.

The mathematical proof in `PROOF.md`, also presented in `section.tex`, composes
with the retained direct C222/refutation calibration to establish in ZFC
that absence of integer zeros is equivalent to Con(ZFC). No consistency
assumption is made. This is not a new end-to-end Lean/Rocq certification.

## Measured improvement

| Matched direct source | Integer variables | Quadratic rows | Terms | Height |
|---|---:|---:|---:|---:|
| Incoming derived-label factorial source | 517 | 310 | 6,774 | 3,904,267 |
| New deferred-sign and shared-frame source | **478** | **305** | **5,484** | **511,326** |

This improves the four displayed metrics of that direct branch. Other
repository equations have fewer variables with different degree/coefficient
costs. There is no global-minimality or worldwide-priority claim.

## What changes

1. Strengthen the proposed factorial's sign guard to `F>=1`. Its first power
   `V=(Ft²+1)^t` can then be interpreted at a base at least two before the
   radix is known. The exact ceiling identity and `V>F` recover two
   factorial remainder signs from one product predicate.
2. Recover the radix and then the powers before restoring twelve further
   remainder/slack pairs. One additional output/slack pair is restored at
   the intermediate radix stage. Fourteen product predicates replace 28
   scalar sign predicates with a complete noncircular dependency argument.
3. The joint guard `(A-1)(v+1)²>=1` gives `A>=2` and a nonzero shared Pell
   ordinate. One square gate plus three witnesses suffice. Signed comparison
   bases are licensed by an explicitly retained earlier theorem.
4. Use 18 proved-nonnegative power atoms linearly and square the remaining
   23. The frame still exceeds the absolute value of every atom. Its 163
   elementary sign deductions use only 31 retained scalar predicates.

The resulting full quadratic source has 690 coordinates and 515 rows.
There are 210 integral monic restorations, two unused coordinates with zero
restoration, and a final integral coordinate translation. The finite source
to final-equation certificates are all supplied.

## Rebuild and verify offline

Only Python 3's standard library is needed. From the archive root:

```sh
python3 -B direct/build.py --check
python3 -B direct/verify.py
python3 -B -O direct/verify.py
python3 -B direct/independent_guard_audit.py direct
python3 -B -O direct/independent_guard_audit.py direct
```

The builder's `--check` creates a temporary tree and requires exact equality
of all ten normative data files. It does not modify the release files.
Without `--check`, supply `--output DIRECTORY` to generate a separate copy.

`verify.py` imports neither the producer nor the optimizer. It checks every
source hash in the ledger, reconstructs every altered source row, checks all
ordered sign deductions and frame coefficients, replays all monic inverse
substitutions, reconstructs every translated row, and independently expands
every coefficient of the final quartic. The separately authored
`independent_guard_audit.py` checks the guard and frame transformations with
its own polynomial implementation. Both retain their checks under Python
optimization. Their finite arithmetic controls are diagnostics rather than
proofs by finite sampling.

## Exact format

A residual consists of `[coefficient, [indices...]]` terms. For example,
`[-3,[2,4]]` means `-3*z2*z4`, `[1,[7,7]]` means `z7²`, and `[1,[]]` is
the constant one. Indices are zero based. Variable order is literal in
`equation.json`; no coefficient ports or unstated parameters remain.

`residuals.txt` prints every final row for inspection. `evaluate.py` reads a
JSON array of exactly 478 integer coordinates and evaluates the residuals,
their sum of squares and the independent expanded polynomial. It performs
no solution search.

## Files and scope

- `equation.json`, `expanded_polynomial.json`, `METRICS.json`: normative final equation.
- `source/parent.json`, `source/domain.json`: immutable, byte-bound source inputs.
- `fused_source.json`, `fusion_certificate.json`, `budget_certificate.json`: complete new source and changes.
- `uncentered_equation.json`, `projection_certificate.json`, `translation_certificate.json`: exact integral projection and translation.
- `build.py`, `transform.py`, `terminal_elimination.py`, `translate_coordinates.py`: portable deterministic construction.
- `verify.py`, `independent_guard_audit.py`: independently implemented checks.
- `PROOF.md`, `section.tex`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`: ordinary proofs and separate review.
- `source/`: immediate upstream arithmetic proofs, signed-comparison proofs, endpoint source copies and original notices.
- `SOURCE_LEDGER.json`: exact archive/snapshot/file identities.

The transitive imports of the copied Lean interface files are not supplied
as a new standalone build. The logical calibration is an inherited ordinary
mathematical dependency. None of the finite scripts decides Con(ZFC), proves
unsolvability, or replaces the unbounded arithmetic and calculus proofs.

### Preserved source references

The source documents retain their original wording and hashes. Commands or
paths in those historical documents, such as `diophantine_zfc_round14/`,
`intake/`, `upstream/`, or older `natural/equation.json` endpoints, refer to
their original archives. They are not dependencies of the replay commands
above. `SOURCE_LEDGER.json` maps every preserved source file to its local
path and supplies both original archive hashes, member prefixes and pinned
repository URLs. `source/PROVENANCE_README.md` maps the mathematical proof
dependencies and states the boundary of the portable reconstruction.
