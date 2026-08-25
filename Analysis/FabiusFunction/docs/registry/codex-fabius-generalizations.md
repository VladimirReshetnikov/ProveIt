# `codex/fabius-generalizations` status

SYNC Fabius

branch / worktree / machine:
`codex/fabius-generalizations` / `/home/codex/.codex/worktrees/042c/Proofs` / `codexbox`

fetched main SHA:
`bc92ae3a36b7a844dbf4a9685d917e21b3ed0aab`

HEAD and dirty paths:
Branch HEAD before this final registry refresh:
`eb29e3cb2af3f82334f7795daacd50fa60bc98a4`; the source checkpoint remains
`269a57d7b7d667aba83e584172fb978b777127ac`.
The source worktree was clean.  This registry file is the only subsequent path
written.  `origin/main` has now integrated all five source commits and the
original registry checkpoint.  Before this refresh, the branch and fetched
`main` have common base `3619ad3a708c3c8c2ca43b642930f0306cdcfb34`
and are respectively one commit ahead / sixteen commits behind by graph count;
no merge was attempted.

writing (exact paths):
The thirteen-path preservation tranche is source-complete and frozen:

- `Lean/FabiusFunction/BromwichSaddle.lean`
- `Lean/FabiusFunction/DyadicAnalytic.lean`
- `Lean/FabiusFunction/DyadicCorrectness.lean`
- `Lean/FabiusFunction/EarlyApproximants.lean`
- `Lean/FabiusFunction/FabiusSaddleCentralRadiusAsymptotics.lean`
- `Lean/FabiusFunction/FabiusSaddleReduction.lean`
- `Lean/FabiusFunction/FabiusSaddleTail.lean`
- `Lean/FabiusFunction/FabiusSaddleTailAllOrders.lean`
- `Lean/FabiusFunction/FabiusSharpAsymptotic.lean`
- `Lean/FabiusFunction/FabiusSharpExactReduction.lean`
- `Lean/FabiusFunction/FabiusSharpLambertTransfer.lean`
- `Lean/FabiusFunction/TaylorReduction.lean`
- `Lean/FabiusFunction/ThueMorseBinomialLog.lean`

Only `docs/registry/codex-fabius-generalizations.md` is being updated for this
coordination reply.  No additional source or documentation lease is requested.

expected declarations or document claims:

- exact central saddle-kernel normalization, the norm-level real/complex
  saddle-mass bridge, the `b = 1` and `N = 0` central-radius boundaries, and
  arbitrary-filter central-radius limit/eventual wrappers;
- public lower-Lambert tail control, an exact multiplicative sharp reduction,
  a filter-generic log-error-to-exponential-equivalence lemma, both corrected
  logarithmic-error limits, and compact/literal exponential equivalents;
- order-bound-only Horner table independence, natural/signed dyadic evaluator
  bridges, arbitrary equal-presentation invariance, reduction-polynomial
  constant terms, total natural/negative-index reduction wrappers, and the
  exact unit-grid endpoint;
- positivity of both Thue--Morse logarithm arguments and the all-index
  zero-one bit bound;
- the order-free `[0,1]` range of the half-endpoint indicator and the exact
  base step-approximant value at zero.

completed commits:

- `5bf954537109a4e7896b7121ac5ee33eb3f39f13` — Complete saddle-kernel and
  central-radius boundary APIs; integrated on `origin/main` by
  `eabf440e8`.
- `ef38522c89a6ae1fd82632de682bed83e692e1af` — Expose corrected sharp
  asymptotics as exact equivalents; integrated on `origin/main` by
  `eabf440e8`.
- `8124078231e5e5b1a645c198a751a6883bb08c2f` — Generalize dyadic Taylor
  representation invariance; integrated on `origin/main` by `bc92ae3a3`.
- `b13690159e34200ea542d1151c0f5ac8061b910d` — Complete the Thue--Morse
  logarithm boundary API; integrated on `origin/main` by `bc92ae3a3`.
- `269a57d7b7d667aba83e584172fb978b777127ac` — Expose exact endpoint bounds
  for early step approximants; integrated on `origin/main` by `bc92ae3a3`.

validated (exact command, SHA/state, exit code):
All commands below exited `0`.  They were deliberately serialized with
`LAKE_JOBS=1`, but they ran against frozen dirty source rather than an
immutable commit, so they are pre-commit evidence only.

- At HEAD `3d6cc72721129ba1fee040215c5cafa8adedbe0c` with all thirteen leased
  source paths dirty: focused builds of
  `+FabiusFunction.BromwichSaddle`,
  `+FabiusFunction.FabiusSaddleReduction`,
  `+FabiusFunction.FabiusSaddleTail`,
  `+FabiusFunction.FabiusSaddleTailAllOrders`,
  `+FabiusFunction.FabiusSaddleCentralRadiusAsymptotics`,
  `+FabiusFunction.FabiusSharpExactReduction`,
  `+FabiusFunction.FabiusSharpLambertTransfer`,
  `+FabiusFunction.ThueMorseBinomialLog`,
  `+FabiusFunction.TaylorReduction`,
  `+FabiusFunction.DyadicCorrectness`,
  `+FabiusFunction.DyadicAnalytic`, and
  `+FabiusFunction.EarlyApproximants`.
- Same HEAD/state:
  `LAKE_JOBS=1 lake build +FabiusFunction.FabiusSharpAsymptotic`
  (3,891 jobs),
  `LAKE_JOBS=1 lake build +FabiusFunction.FabiusFullAsymptoticExpansion`
  (3,557 jobs), and
  `LAKE_JOBS=1 lake build +FabiusFunction.PaperStatements`
  (3,242 jobs).
- At HEAD `ef38522c89a6ae1fd82632de682bed83e692e1af` with only the five
  dyadic/Taylor source paths dirty:
  `LAKE_JOBS=1 lake build +FabiusFunction.FabiusQBinomialTaylor`
  (3,320 jobs).
- `git diff --check` and path-scoped cached-diff checks passed before each
  commit.
- Independent read-only reviews reported clean for the saddle-tail,
  sharp-transfer, and dyadic/Taylor batches, including the stated boundary,
  filter-orientation, import, named-binder, documentation, and simp checks.

not yet validated:
No Lean/Lake target has been run at immutable source tip
`269a57d7b7d667aba83e584172fb978b777127ac`; the board currently withholds the
`codexbox` build token.  No aggregate-build or axiom audit is claimed for that
immutable SHA.  No LaTeX or PDF path is part of this tranche.

requested integration or lease:
All five source commits are integrated.  No further integration and no new
write lease are requested.  Please release this preservation lease when the
combined immutable-main validation is complete, or assign an exact next path
set and build token explicitly.

conflicts / dependencies:
Immediately after fetching `bc92ae3a3`, `git cherry -v origin/main HEAD` listed
only the registry refresh `eb29e3cb2`; every source commit and the original
registry checkpoint were absent, confirming patch-equivalent integration.
Per the board, this branch did not merge, rebase, stash, reset, or push to
`main`.

next bounded step:
Push this final registry refresh to `codex/fabius-generalizations`, then remain
read-only and wait for coordinator release/synchronization instructions or an
explicit build/source lease.
