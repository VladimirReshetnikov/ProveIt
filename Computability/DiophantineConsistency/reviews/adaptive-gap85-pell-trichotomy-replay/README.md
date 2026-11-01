# Pell index trichotomy in IΣ₁ models

The two focused runs PASS, matching both source/object/full-log records. The checked theorems use the existing positive Pell-solution classification and monotonicity in every model of IΣ₁. For positive k and x² = 1 + Q(Q+1)k² with positive Q, the index is 2, 8Q+4, or at least 32Q²+32Q+6. The theorem with Q=q+1 does not need the extra positivity assumption. Checks show only standard Lean axioms.

The source and replay driver are `research/adaptive-gap85-normalization/AdaptiveGap85PellTrichotomy.lean` and `replay_pell_trichotomy.py`. The direct imported object and companion files are pinned; the historical inherited project-object transitive ancestry and external package ancestry are not source-authenticated. The failed initial attempts before overlay repair are retained at `/tmp/gap85-pell-trichotomy-replay-8xuaysok` and `/tmp/gap85-pell-trichotomy-replay-2vbsxmct` and did not compile due to Lean namespace resolution.

This model theorem supplies the exact index cases needed by the separately checked integer special-template bound, but the latter has not been lifted to arbitrary models. No representative for an arbitrary 85 zero and no 85 equivalence is claimed.
