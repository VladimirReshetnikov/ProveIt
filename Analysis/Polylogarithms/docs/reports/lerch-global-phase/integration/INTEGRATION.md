# Suggested integration

## Preserve the research article and certificate together

Copy this package under a new report directory, for example:

```
Analysis/Polylogarithms/docs/reports/lerch-global-phase/
```

The exact interval verification is a dependency of the global outer exclusion. Keep the article, verifier, and `certificates/exact.json` together. Treat `diagnostics.json` as numerical exploration, not proof-bearing enclosures.

## Insert the manuscript fragment

Copy `09-lerch-global-phase.tex` from this directory to:

```
Analysis/Polylogarithms/docs/manuscript/chapters/09-lerch-global-phase.tex
```

Add the following at the end of the existing `chapters/09-zero-geometry.tex`, or at another editorially suitable point inside that chapter:

```tex
\input{chapters/09-lerch-global-phase}
```

The fragment uses the manuscript's existing theorem environments and the label prefix `globalphase:`. It states the results, their finite-certificate dependency, and the central proofs. The full report supplies the detailed elementary barrier, Euler--Maclaurin remainder, interval construction, all-index extension, and diagnostics. No automatic main-manuscript insertion is performed by this package.

Update the discovery chapter or editorial ledger to mark the companion report's **Conjecture 12.1 (no additional outer pair at index three)** as proved by the global outer-exclusion theorem in this report. Preserve the historical distinction: the earlier localized fold theorem by itself did not settle the global question.

Do not relabel the proposed strict span unimodality as proved. The proved statement is the sharp global maximum, its uniqueness, and its nondegeneracy; those facts do not exclude other smaller local extrema.

## Two local corrections to the inspected source

The baseline chapter has Git blob SHA `7f41eb87ed5e0bf90a2dffa489a8e2cd552056be`.

1. Replace “The root of $P_1$ is $-\gamma$” with “The root of $Q_1$ is $-\gamma$” in the half-unit proof. In the chapter, `P_1(t)=1+t`, whereas `Q_1(x)=x+gamma`. This correction was already proposed by the previous companion and remains unapplied in the inspected baseline.
2. Remove the duplicated wording “The endpoint signs in the endpoint signs ...” at the beginning of that proof.

Show the proposed diff without changing files:

```sh
python3 code/propose_corrections.py --repo /path/to/ProveIt
```

Apply the two replacements to a local checkout only after review:

```sh
python3 code/propose_corrections.py --repo /path/to/ProveIt --apply
```

The helper checks the full baseline blob hash and the uniqueness of the exact replacement contexts. If the manuscript has changed, it stops rather than applying a fuzzy patch. Review `corrections.json` and port the changes manually to the revised source. It does not access GitHub or make commits, pushes, pull requests, or any remote changes.

## Validation after integration

Run the standalone exact verifier and tests before compiling the manuscript. Compile the manuscript according to its own build process, check references, and inspect the inserted pages. The standalone package was validated independently; no claim is made that the entire repository or its Lean development was built in this session.
