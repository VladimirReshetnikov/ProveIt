# Eta-natural conditional Pell growth

This source-only draft isolates the growth bound `2^R<Y` for the eta-natural
prototype. It is **not Lean-elaborated**, and does not establish any graph
zero, eta-zero contradiction, or iPRA endpoint.

The prototype has `X=q*w0` and `Y=q³*s`. The client explicitly assumes
`q≥16`, `w0>0`, and `s>0`; these yield `X≥16` and `Y≥1` without a factor-three
or Bézout argument. The compact-port fixed-beta lower bound and the proof that
the graph's own `n_w` is positive are separate inputs, not inferred from an
unrelated carrier.

The source calls the existing `ArithmeticPellPowerRecovery.power_bound` after
putting `r=n−1`. The **same** supplied first index n must satisfy `n≥13`,
`2n=R+1` and the doubled first ordinate equation; the actual main ordinate
must be `ycoord R (Y*(X+1))=c`. The inputs also explicitly state
`c=k*Y+eta`, `k=eta+zeta` and `zeta>0`. Eta is a natural with no positivity
assumption, so eta=0 is included in the proposed fact-level statement. The
source does not construct these recurrence coordinates from the graph.

A second client composes growth with the separately unelaborated
`EtaZeroDirectProjectionDraft.power_of_direct_carrier`. Its natural `w0` is
the graph input in `X=q*w0`, while `w` is the exact-index quotient in
`k=R+1+4*X*Y²*w`; both are explicitly retained. The main x/y coordinates
and the actual no-`E*q` oriented balance must use the **same** main root.
The fixed beta/model casts, positivity and graph-factor extraction,
first/main norm and index binding, rank window, compatible providers,
axiom reports, later contradiction and zero maps remain open.

Run `python3 -I -S -B research/ordinary13-eta-zero-growth-model-draft/check.py`
from `Computability/DiophantineConsistency` and compare to `receipt.json`.
It checks source signatures and finite arithmetic controls only; no Lean or
build is run.
