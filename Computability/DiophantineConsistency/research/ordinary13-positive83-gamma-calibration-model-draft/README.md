# Proposed gamma calibration from a positive 83 zero

This source draft proposes discharging the `CalibrationCut` in the conditional
83→84 transport. It is **not Lean-elaborated**, provider-validated, or an
end-to-end iPRA proof. The separate 84-side `q | X` cut and the exact parent
bridge remain open. Every imported source, model theorem, cast and axiom
obligation remains subject to actual Lean and provider verification.

`calibration_of_root` accepts a positive 83 zero together with an explicit
positive replacement for coordinate r that makes the positive-81 first
residual zero. The existing source transport keeps the other three residuals
and every non-r coordinate, producing a positive 81 zero and then its 85
prototype image. This route does not use the 83→84 transfer under study.

The proposed client invokes the prototype's early first-index witness `(n,w)`
and `Positive81ExactMainDraft.exact_and_main` on the **same** n and w. That
source returns the actual oriented main root at the exact natural rank R,
including both Pell coordinates and the no-extra-term main balance. The
client translates those facts back to the unchanged 83 coordinates and uses

```
Y = q³*s,   U = Y*q²,   W = 4*X*q*s*w,
4*(X*Y*Y)*w = U*W.
```

This supplies the k decomposition required by the separate fact-level
`gamma_gt_from_modified_balance` client. The source records the natural
83 rank formula and its proposed equality with the prototype rank; this is a
model-natural expression after the relevant gap, not by itself an independently
proved signed graph-rank representation. No r preservation is claimed: r is
allowed to change and does not appear in the remaining first-index, main,
strong, or auxiliary coordinates used here.

`calibrationCut` proposes to obtain the replacement from the independently
drafted compact 83→81 reverse-root theorem. Its statement has no explicit
cut, but depends on that entire unelaborated source chain and the positive-81
exact-index/strong-auxiliary chain. The conclusion is a source-level proposal,
not evidence that the cuts have been verified or that an equation's no-zero
statement is provably equivalent to consistency.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive83-gamma-calibration-model-draft/check.py
```

The read-only checker pins the direct sources and graph JSON, checks the exact
shared non-first 83/81 rows, and tests bounded mappings, rank and W-factor
identities. These controls do not validate Lean scripts or prove the model
claims.
