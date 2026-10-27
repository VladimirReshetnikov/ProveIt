# Actual C222 append execution: author record

26 October 2026. Root authored and fully read the155-line main,36-line
checks and complete replay driver before execution. Both first fresh leaf
builds pass:6.749s/1.741s, empty main and thirteen standard-only reports.
Independent mathematical review and replay are recorded separately.

The actual internal IΣ1 evaluator now satisfies
`eval(append(left,right),w) = if eval(left,w)=0 then 0 else
 eval(right,eval(left,w)-1)` for every internal word/state, including empty
words and raw command0. Positive completion and halt0 remain distinct.
`extendValue` appends a fixed continuation to a live evaluator. An active
head tick commutes with extension by the actual raw-tail replacement laws.
The pointwise Σ1 time induction retains a bounded stopped-pair witness,
keeping left/right/work fixed. After left halts the combined run halts;
a positive completed left starts the right evaluator at its resulting
working state. Semigroup and terminal uniqueness identify the complete
run without a numerical lower bound on the append code or a minimal
stopping-time operator. Explicit halt and positive-success clients follow.

This uses actual AppendPerm222 and WordEvaluationPerm222, with their accepted
Run/Replace prerequisites. Historical254 execution was read as a guide;
no old254 execution theorem is imported. The theorem is internal arithmetic
runtime composition, not a proof compiler, proof-state invariant, exact215
machine calibration, consistency theorem or HA equivalence.

Source main1e277495b4f9975ae642879a04e68f4bf906f033c02185d8007f88924d75ec2b;
checks2494607a25aaa7b029628bd9e10636c2f3815e1a58dd4d97f4403483741c2719.
Outputs6e629ca4e067de5179cdfaa201cdbbbda9fd1cb0e8b6e5efb60e39d6779dbfe2
and72b8eb7088809260001f584d729949c19e3b733ed5e69629c81fd58646d90c90.
[Replay packet](arithmetic-command-compositionperm222-replay.json) SHA
030dd9838e7d5d15546f6184922cd7fa543bb4f9ed2bc38ae01049cc967ad957;
[nine-file evidence manifest](arithmetic-command-compositionperm222-replay/FILES.json)
SHA d550aa7e65141345e1a7e5bbfd6a6d3a664230467d4d8e89dcd9dc282740b56c.
No failed author source/check attempts occurred.

The private closure authenticates121 cached current-source custom modules,
95 Foundation modules,406 cached artifacts,38 explicit external boundaries
and1814 inherited/explicit observations, before and after execution.
Only the two new leaves are fresh. Lean4.32 -M6000 -j1 -DElab.async=false
uses regular nonsymlink outputs with512MiB reserve, no dependency build or
shared cache overwrite. Private primary:
`/tmp/arithmetic-command-compositionperm222-root-author-9rlqzan9/lib`.
