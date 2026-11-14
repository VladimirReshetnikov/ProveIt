# Search that permits changes to protected arithmetic controls

This experiment extends the supplied PA194HS/PA194NS quotient searches by
allowing rows of the 23 protected arithmetic controls to change. It found
no accepted 193-state machine. It proves no state-count lower bound.

The exact input is the 194-state PA194HS/PA194NS machine, native SHA-256
`0b72fc7decfe10ffe30c967f59ddfc570bc7f92177f67b72735b82a0d2fe9fb8`.
It comes from `docs/incoming/pa194hs_conpa_2026-11-13.zip` in the pinned
ProveIt corpus. The imported source and verification engine retain their
original attribution and licenses under `reference/`.

Run from any directory with ordinary Python 3.10+, assertions enabled:

    python3 search.py pp
    python3 search.py mixed

Fresh result files replace the recorded files under `results/`; elapsed
times will vary. The source and native machine remain unchanged.

## Candidate family

A quotient deletes one control, redirects every target of that control to
its survivor, and independently selects each survivor row from the two old
rows for that same read bit. Every other row remains unchanged.

- `pp`: every pair among the 23 protected controls, all four row choices:
  4 times binomial(23,2) = 1,012 candidates.
- `mixed`: each of 170 unprotected controls other than native control 84,
  paired with each protected control, with the three row choices that do
  not keep both protected rows unchanged: 170 times 23 times 3 = 11,730.

Native control 84 is the stipulated source-frame boundary. This experiment
keeps that interface fixed. The previous protected-row-preserving searches
cover the omitted fourth row choice; their outcomes are external evidence,
not rerun by this script.

## Verification filter and limitation

The independent literal-tape symbolic engine rederives four generic
register-list lemmas after normalizing their entry and exit labels by the
proposed quotient. A candidate must preserve their exact block effects and
`v+2` durations. The checker then tests one source site for every primitive
opcode/argument/outcome combination (32 representatives). A survivor is
checked on the entire source contract collection (4,750 outcomes).

The per-source-contract limit is 700 symbolic operations (the unchanged
baseline's recorded maximum is 403); each list lemma has a 50-operation
limit. A rejected symbolic execution may fail through an unknown run length,
a missing generic list traversal, or exhaustion of this bound. Such failure
means the candidate has not passed this proof method. It is not necessarily
a semantic counterexample, and it does not prove that the candidate diverges
or has a different blank-tape halting condition.

## Observed result

| Candidate family | Candidates | Pass list lemmas | Pass representatives | Pass all source contracts |
|---|---:|---:|---:|---:|
| Protected/protected | 1,012 | 629 | 0 | 0 |
| Mixed, changed protected row | 11,730 | 8,334 | 2 | 0 |
| Total | 12,742 | 8,963 | 2 | 0 |

No candidate reached a blank-start validation stage. The full failure
histograms and timings are in `results/`. The two candidates passing the
representatives still failed the full contract collection.
