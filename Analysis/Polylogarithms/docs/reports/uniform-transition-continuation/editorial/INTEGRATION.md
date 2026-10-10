# Proposed integration into ProveIt

Baseline: `cc34f73596336f2466d9754cb0f3635bd2bedade`.
Contribution paths are relative to the unpacked bundle. Repository source
paths are relative to `Analysis/Polylogarithms/docs/manuscript` unless they
begin with `docs/incoming`.

| Contribution | Suggested location | Status and dependencies |
|---|---|---|
| `sections/02-uniform-harmonic.tex` | After `chapters/04-proportional-depth.tex` | Proved for `p -> infinity`, uniformly for all `h >= 1`, `a > 0`; resolves the unbounded-ratio saddle question. |
| `sections/03-inverse-harmonic.tex` | After the harmonic transition compiler | Uses the existing forward all-orders theorem; proves the inverse with two explicit coefficients and an all-orders recursion. |
| `sections/04-joint-moments.tex` | After the reflected and sharp moment chapters | Proves the `n/m ~ log m` transition; preserve compact transition-parameter assumptions. |
| `sections/04b-proportional-moments.tex` | Immediately after the joint transition | New exact computer-assisted monotonicity proof; proportional moment theorem and full analytic corollaries. Keep the small certificate beside the source. |
| `sections/05-integral-distribution.tex` | Beside `08-distribution` and `08-conductor-jets` | Classical freeness/resolution methods are credited; explicit integral cokernels, torsion and sharp denominators are the main additions. |
| `sections/06-gaussian-equivalence.tex` | Beside `cycloquot:conj:S6` | Two convergent shuffles prove coordinate equivalence only. Keep one S6 conjecture label. |

All `us:`, `joint:`, `gs:`, `intdist:` and `s6audit:` labels are local to this
contribution, except where a literal baseline label is explicitly quoted.
Rename the occasional local coefficient letters if a neighboring chapter's
notation would make them ambiguous. The standalone preamble uses `article`;
the section text can be inserted into the repository's book class with its
existing theorem environments. The bibliography key `gaussian:ACEMKM` already
exists and should be reused instead of duplicated. DLMF and Ouyang references
may also be merged with existing equivalent bibliography entries.

## Two minimal corrections supplied as a patch

`proposed_corrections.patch` is prepared against the pinned source and covers:

1. The rank-difference logical implication in `05-signed-kernels.tex`.
   The two ranks imply the Gaussian-supported dimension; the dimension alone
   does not determine both ranks. This issue was also recognized by incoming
   rank work, which is credited in the article.
2. A duplicated DLMF citation in `04-proportional-depth.tex`.

From the ProveIt repository root, check before applying. Replace the example
absolute path below with the location of the unpacked bundle:

```sh
git apply --check /path/to/unpacked-bundle/editorial/proposed_corrections.patch
git apply /path/to/unpacked-bundle/editorial/proposed_corrections.patch
```

No remote mutation has been made. The patch deliberately does not upgrade the
rank conjecture itself: that editorial action should be performed while
integrating the already supplied full proof and its certificate from
`docs/incoming/polylogarithms_level4_rank_2026-10-09.zip` or the corresponding
formal-reductions archive, rather than relying on this article's summary.

## Research-status reconciliation

- S4 is already proved in the canonical manuscript. Retain that status.
- The signed odd-weight rank pattern is already proved in incoming packages.
  Integrate one complete proof rather than count a new experiment as progress.
- S6 remains open. Its two stored forms are exactly equivalent, as proved here.
- The growing-ratio harmonic saddle question is resolved, with bounded `p`
  still handled separately by the existing endpoint theorem.
- Both the compact proportional moment regime and the compact joint transition
  are resolved by this contribution. Uniform bridges between them, moving
  transition parameters, and growing-exponent optimal truncation remain open.
- Existing complex distribution ranks remain correct. The new torsion and
  finite-characteristic primitive ranks concern an integral coordinate inclusion.

The broad universal-distribution freeness/resolution principles must retain
their classical attribution to Kubert, Anderson and Ouyang. No global priority
claim is made for the additional concrete formulas or gamma-ratio inequality.
