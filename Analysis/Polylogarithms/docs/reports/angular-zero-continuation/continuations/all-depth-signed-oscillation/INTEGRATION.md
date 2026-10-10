# Integration into ProveIt

## Suggested additive report

Place the package in:

`Analysis/Polylogarithms/docs/reports/all-depth-signed-oscillation/`

Keep its full article, proofs, exact evaluator, frozen certificates, audit, and
claim-status ledger together. The package is self-contained and does not require
other incoming ZIP archives to run.

## Manuscript synopsis

Copy `integration/all_depth_synopsis.tex` to a new chapter fragment such as:

`Analysis/Polylogarithms/docs/manuscript/chapters/05-all-depth-signed-oscillation.tex`

Add an input after the existing signed-kernel / real-order / subcritical sequence.
All added labels and macros are prefixed `ado:integration:` or `ADO`. The synopsis
provides theorem statements and proof structure, not a substitute for the full
report. When integrating full proofs into the book, transfer sections 2--5 and
resolve the report's macros and bibliography keys explicitly.

Preserve the stronger all-positive-real depth-two results already in the book.
The new theorem extends depth, but it does not subsume every fractional-order
parameter domain already treated at depth two.

## Optional notation-only patch

The expected source blob is:

`044d3825b90dce437ac9007733e6447cf9563098`

The patch affects only the transport proof in `05-real-positive-kernel.tex`:
line 102, `q=n` to `x=n`; line 104, boundedness of `h` to boundedness of `q`.
It does not change a theorem or formula. The read-only checker rejects a changed
source snapshot:

```sh
python code/check_source_patch.py /path/to/ProveIt
```

After review, the repository maintainer may apply the patch from the checkout root:

```sh
git apply --check /path/to/package/integration/notation_corrections.patch
git apply /path/to/package/integration/notation_corrections.patch
```

These commands have not been executed against the user's remote repository.
A temporary local fixture of the reviewed source hunk was used only for patch
syntax/context replay, not for a full-source hash check or a canonical-book build.

## Status ledger entries

Record the signed-kernel and angular results as ordinary analytic proofs with a
finite exact replay. Retain S6 and the new S8 as conjectural; retain the existing
normalized-radius conjecture. “Minimal compensator degree” must not be shortened
to a claim of minimal arithmetic depth. The all-ones logarithm identity, beta
identity, and positive Hausdorff theory are background ingredients, not claimed
first discoveries.
