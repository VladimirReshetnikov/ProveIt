# Local repository integration

The full deliverable is an additive research contribution. No remote branch,
commit, pull request or file has been created or modified by this package.

## Target

`Analysis/Polylogarithms/docs/manuscript/chapters/05-signed-kernels.tex`
at commit `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`, Git blob
`e61ff32263722d7575ca0202fba4dd7dad534861`.

Its final subsection begins:

```tex
\subsection{An exact-rank conjecture in all odd weights}
```

The helper replaces that final subsection with

```tex
\input{chapters/05-level4-rank}
```

and copies `05-level4-rank.tex` into the same chapter directory. The fragment
contains the uniform rank proof, the complete nullspace, Gaussian saturation,
the all-weight S-family obstruction, the affine compiler and two mixed-color
identity families. The old rank labels are preserved as aliases, with theorem
rather than conjecture status. New labels use `l4rank:`.

## Guarded helper

```sh
python integration/apply_integration.py /path/to/ProveIt
python integration/apply_integration.py /path/to/ProveIt --apply
```

The first command is a dry run. The second explicitly writes local files.
Both refuse a changed canonical source or an already existing destination
fragment. A refused hash match is a signal to reconcile manually, not to
bypass the check. The helper does not run Git, build the main manuscript,
update editorial ledgers, or copy the whole research report.

After local review, put the full package in a distinct research-report
subdirectory, retain the historical arrival materials, and update the current
editorial ledger and validation navigation. Rebuild the main manuscript using
its existing LuaLaTeX workflow. The companion article itself builds with
pdfLaTeX. The integrated full manuscript has not been rebuilt in this delivery;
the fragment has been compiled in a representative book wrapper.

## Manual reconciliation on a later commit

Check whether `signed:conj:rank` has already been promoted, whether the matrix
row vocabulary has changed, and whether the final-subsection assumption still
holds. Apply only content not already present. Preserve the distinction
between the complete solution of this restricted row system and the larger,
still incomplete space of analytic period relations.
