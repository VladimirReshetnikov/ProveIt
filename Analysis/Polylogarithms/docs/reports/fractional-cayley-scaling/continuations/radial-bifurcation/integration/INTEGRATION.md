# Proposed integration

## Baseline and placement

Audited commit: `0707425e155707e53d2892e30c72e54d06c00e5f`.
The canonical manuscript is `Analysis/Polylogarithms/docs/manuscript/`.
Preserve this package as a new report at
`Analysis/Polylogarithms/docs/reports/radial-boundary-bifurcation/`.
This archive does not modify the repository or delete any historical report.
Use the repository's current intake procedure when placing it.

## Canonical manuscript additions

Copy `05-radial-bifurcation.tex` from this directory into the manuscript's
`chapters/` directory. Include it immediately after the existing
`05-real-turning.tex` input, wherever that input is wired into the book.
The new labels use `rbif:int:*`. Add `bibliography-entry.tex` inside the
existing `thebibliography` environment. The excerpt assumes the book's
existing `theorem`, `corollary`, `proof`, and standard AMS environments.
It has no custom macro dependencies. The excerpt was separately compiled
as a compatibility smoke test, not in the complete 375-page book.

Preview the guarded status replacement with:

```sh
python integration/update_quartic_status.py /path/to/ProveIt
```

The default only prints a diff. Adding `--apply` writes the change after
verifying the exact Git blob and old paragraph. The utility was not run
against a local checkout during this session; it fails closed if the
baseline differs. It updates the concluding open-status paragraph of
`05-real-turning.tex`; it does not overwrite the old numerical diagnostic
or alter its historical certificates. The new proof and the old diagnostic
have distinct evidentiary roles. If the source has changed, inspect it rather than forcing the replacement.

## Editorial ledger entry

**Global quartic transition / radial-boundary-bifurcation:** exact
computer-assisted proof that `q(b)=Q(A(b),b)` has one interior zero on
`0<b<1`; the sixth-order coefficient is negative there and `D(K,Q)` is
invertible. Analytic proofs give a complete local two-parameter fold,
a fourth-root radius law, an open two-extremum region, and constant-curve
rigidity for `a>=1,b>0`. A separate explicit rational witness has at least
two small-radius extrema. New universal coefficient and Möbius identities
are proved symbolically in the report. Three decisive replay programs
pass; optional symbolic and arithmetic-kernel regressions also pass.

Preserve attribution of the quadratic threshold and earlier maximum/minimum
certificates to the previous manuscript. Update the book's source inventory,
validation report, worklog, and receipts according to its established
process. A source update requires a new book build and rendered review;
the report PDF review is not a review of the changed collective manuscript.

## Correction audit

No algebraic error was found in the audited formulas for `K` or `Q`.
The requested changes are proof-status advances, not retrospective claims
that a careful earlier conjectural statement was wrong. In particular,
replace neither “local” by “global” nor “at least two” by “exactly two” for
the explicit witness. The older statement that there is no proved unique
quartic transition becomes obsolete once the new proof is integrated.

The full-radius conjecture for integer outer orders `a>=2`, the stated
`a=1` alternatives, S6/S8 identities, and the `0<a<1` constant-curve question
retain their previous unresolved status. No finite arithmetic replay is a
proof of period independence or a Lean formalization.
