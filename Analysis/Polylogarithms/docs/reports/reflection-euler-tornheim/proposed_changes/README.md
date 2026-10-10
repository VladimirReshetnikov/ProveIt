# Proposed manuscript corrections

Baseline: 78f9e5df05eb0abb16c89fb00b9e89403598bd17.

## Checked local patch

**manuscript-corrections.patch** changes four files beneath
Analysis/Polylogarithms/docs/manuscript:

- chapters/04-depth.tex: supplies the two exact weight-five shuffle rows, derives the sporadic row, sharpens the spanning claim to two coordinates, and gives an equivalent S4 conjecture.
- chapters/07-integration.tex: replaces the stale named-atom open problem by the classical Tornheim derivative evaluation and fixes the sixth-point coefficient label.
- chapters/10-discovery.tex: narrows the cubic discovery target to a smaller prescribed basket.
- references.tex: adds the Bailey–Borwein–Borwein 2015 reference.

The patch was generated from source bytes whose Git blob hashes match the pinned commit, and git apply --check passed. Its old cubic label is retained for cross-reference compatibility.

From the repository root, review applicability with:

    git apply --check /path/to/manuscript-corrections.patch

To apply the reviewed proposal:

    git apply /path/to/manuscript-corrections.patch
    git diff -- Analysis/Polylogarithms/docs/manuscript

## Mixed survivor reconciliation

**mixed_survivor_insertion.tex** is a manuscript-compatible insertion containing the exact inverse-argument endpoint identity, a proof, and both weight-six corrections.

After incorporating it, reconcile the following Chapter 4 locations:

| Source location | Required change |
|---|---|
| mixed:sec:eisdim, weight-six row | The imaginary weight-six mixed survivor reduces; change the current survivor entry to zero or retain it only in an explicitly historical table. |
| Paragraph claiming exactly two new mixed constants | Remove the imaginary weight-six claim. Any real weight-five survivor remains a candidate, without an independence theorem. |
| mixed:sec:gauss, dimension paragraph | Remove the imaginary Li51(i,-i) direction from the present survivor count, using the displayed depth-one evaluation. |
| mixed:thm:parallel and its concluding paragraph | Replace the purported common weight-five/weight-six pattern with the correction: the regularized endpoint identity eliminates both imaginary weight-six entries. |
| Historical numerical search narrative | It may remain as history, with a clear statement that the later regularized reduction supersedes the candidate count. |

This correction is already supported by the inverse-argument coefficient mechanism in report 10. It is an integration correction to the consolidated manuscript, not a claim that no prior continuation addressed mixed doubles.

The new article's formal dimension theorems concern only imaginary symbols and their explicitly specified row family. Do not use them to infer a dimension for a combined real-and-imaginary period space.

## Additional source caution

The auxiliary sign correction to equations (63) and (65) of the June 2012 Bailey–Borwein–Borwein author preprint is explained and proved in the article. It is not an assertion about uninspected final journal typesetting.

## Conjecture ledger

S4 remains conjectural. Add S6 as a new conjecture with its frozen ordered basket and primitive integer vector. The exact certificate proves that its integer-normalized residual is below 10^-260; it does not prove equality.

The source and claim manifests in the package provide the provenance and status distinctions for integration.

