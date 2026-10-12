# Proposed source cross-reference correction

## Target

ProveIt commit `7bd1ce58abe522b83cd3368bbafa1be97837b75d`:

`Analysis/Transseries/docs/series-and-transseries/Mellin_Borel_Completion_q_Gamma_Critical_Reversion/critical_stokes_q_reversion.tex`

Locate the paragraph near the internal labels `eq:FR60a` and `eq:FR60b`:

```tex
These are precisely
(60a)--(60b), labeled Conjecture~5 in arXiv:2506.08265v2
```

Proposed replacement:

```tex
These are precisely
(3.36a)--(3.36b), labeled Conjecture~5 in arXiv:2506.08265v2
```

## Evidence and scope

The directly inspected PDF `https://arxiv.org/pdf/2506.08265v2`, dated
1 April 2026, displays Conjecture 5 on printed page 17 (zero-based PDF page
17), with equation labels (3.36a) and (3.36b). The page image was checked in
addition to the parsed text.

This changes an external equation-number reference only. It does not change
any mathematical identity, prove or disprove that conjecture, or require
renaming the repository's internal labels. Other versions of the external
paper may have different numbering; preserve the cited version explicitly.

No patch has been applied to the repository. Reconfirm the target sentence
against the current file before making the editorial change.
