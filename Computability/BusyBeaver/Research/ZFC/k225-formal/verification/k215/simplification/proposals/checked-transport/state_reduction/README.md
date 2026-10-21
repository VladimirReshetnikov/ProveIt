# Two-branch state folding and a concrete 214-state obstruction

**No verified 214-state machine is supplied.** The only 214-state table in this component is explicitly rejected by an independently replayed counterexample to the inherited uniform primitive-runtime contract. The counterexample makes no assertion about the trial's blank run or its consistency strength.

This component is pinned to ProveIt commit `aa66d0a33f1f8237a348899eb8095b045a502832` (21 October 2026). It supplies an ordinary mathematical proof template and an independently implemented restricted search for folding states when **both read branches differ**, a complete specified search over 22 byte-distinct current 215-state tables, and a useful failed attempt whose intended local selector blocks all pass while a borrowed helper's existing use fails.

The later predecessor-specific elimination packet at commit `b0663213602b3635258150c58ffe105a2e0ba44f` was reviewed before packaging. Its incoming-row rewrite grammar is complementary to this component; the 21 input tables overlap exactly by hash, and FM215 is the additional input here. See `UPSTREAM_REFRESH.md` for the precise distinction. No claim of historical priority is made.

## Results

| Investigation | Checked result | Precise limit |
|---|---:|---|
| Exact three-transition two-branch folds, radius-three invariant | 468,218 ordered keep/delete choices; 458,714 have both mapped target branches different; no fold | Same write/move on each original branch; frozen strict interiors; specified direct/three-step template |
| Two-branch helper walks, radius-five invariant, at most 64 transitions | Same 468,218 pair choices; no fold | Shared literal first action, exact literal endpoint profiles, no access outside the known 11-cell window, strict interiors exclude the two merged controls |
| History-return table plus inherited helper resynthesis | 3,143 specifications; 1,435 prefix passes; 480 delivery-class passes; no accepted trial | All 480 fail the symbolic prover; this alone is **not** a semantic counterexample for every trial |
| Positive control | A synthetic 216-state split requiring both rows to change folds to 215; four literal blocks checked independently | Algorithm test only, without ZFC calibration |
| Naive 52/154 fold with borrowed 117/1 | Four intended blocks pass, but CB1 at ordinal 4724 fails on a concrete valid frame | A counterexample to uniform primitive simulation, not a statement about the blank run |

The two broad search counts overlap and must not be added. Their no-result outcomes are not a lower bound on machines realizing Con(ZFC).

## The concrete failed attempt

Redirect every target 154 to 52, delete state 154, and set:

```
52  0  0 L 211
52  1  1 L 117
117 1  1 R 176
```

Old state 52 is entered with predecessor bit one, and old state 154 with predecessor bit zero. The proposed two selector blocks therefore simulate both roles in three transitions. However, row 117/1 previously implemented a live CB1 entry (`0 L 302`). At source address `11011`, zero-based ordinal 4724, with all nine registers zero, one zero spare and gap zero, the parent redispatches correctly after 163 steps with head -1. The trial redispatches after 588 steps with head 0 and an incorrect address. Exact complete traces and tapes are retained.

`evidence/partial-two-branch-targets.json` catalogs 19 primary-K215 pairs with both target branches different for which one branch already has an exact three-step helper. These are concrete synthesis targets, not accepted machines. The missing work is a coordinated implementation that also preserves every borrowed helper use.

## Reproduce

Python 3.10+ and the standard library suffice. Run from any directory, using a fresh output path:

```
python3 -B code/reproduce.py --output /tmp/two-branch-replay
```

This checks all input hashes, the independent 52/154 counterexample, the nontrivial positive control, and four literal positive-control blocks. To repeat both complete 22-table searches, add `--full-search`. To repeat the separate 480-trial inherited symbolic filter, add `--context-search`. Both optional flags can be combined. Search failures caused by window exits or an exhausted proof procedure remain unresolved, not inferred semantic errors.

`state_reduction_section.tex` is an editable report section containing the proof, finite scopes, concrete counterexample and proposed next work. `inputs/source-index.json` records exact repository paths and hashes; inherited tables and checker modules retain their attribution in `licenses/` and `NOTICE.md`.
