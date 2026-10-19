# Exact 240-state decoder tree and startup frame

Lean now checks the rotated source's complete decoder tree and identifies the
240-state machine's initialized tape with the calibrated logical seed. The two
units pass **16 theorem probes and 19 typed callers**, with zero warnings.

[`TreeRotation240`](../../Lean/BusyBeaver/ZFC/TreeRotation240.lean) proves that
the literal tree equals `SourceRotation240.program`'s tree for every sufficient
fuel. Its walk and step equations quantify over arbitrary paths and register
files. The tree has 6,455 leaves, 6,454 internal nodes, depth 51 and one halt
leaf. All 203 stored source rows are checked, including the changed row 169
and its four reachable occurrences. This establishes the decoder's identity;
the [complete coverage proof](rotation240_coverage_complete.md) separately
checks the concrete binary instruction sites.

[`BootstrapFrameRotation240`](../../Lean/BusyBeaver/ZFC/BootstrapFrameRotation240.lean)
composes the [exact 409,691-step blank startup](rotation240_bootstrap.md) with
a complete tape-shape proof.
The result is a `DispatchFrame64` at dispatcher 84 and head −5, with gap 181
and 167 spare registers of value one. Its nine physical primary registers are
`[0,0,0,3,0,0,3,0,0]`, matching `LogicalSeed246.initial`. The checkpoint has
351 one-cells, left padding 9 and right padding 0. The equality includes the
entire tape and its zero exterior, and proves the spare suffix is nonempty.

| Unit | Probes / callers | Source / audit seconds |
| --- | ---: | ---: |
| Exact tree | 8 / 10 | 4.714 / 0.294 |
| Startup frame | 8 / 9 | 1.054 / 0.480 |

The [tree result](results/tree-rotation240-verification.json),
[frame result](results/bootstrap-frame-rotation240-verification.json) and
[publication record](results/rotation240-tree-frame-publication.json) retain
the actual successful checks. Each source/audit pair used one thread,
4,096 MiB, default proof limits and a shared 120-second deadline. The selected
project-provider counts were 10 and 124 respectively. The only reported axioms
are `propext` and `Quot.sound`; the finite tape equality itself uses neither.

The [original guards, audits and raw logs](rotation240-tree-frame/) and
[lossless text history](rotation240-tree-frame/history.json.gz) preserve
preparations, source templates and review records. Installed sources are exact
copies of the successful runs. The guards retain historical scratch/provider
paths; this packet does not provide a clean-checkout dependency build.

These results discharge the initial tape-frame obligation for the
[general runtime proof](rotation240_runtime.md). The
[external binary endpoint](rotation240_binary.md) now composes that runtime,
the complete decoder coverage and the register-source calibration from this
exact frame. The internal PA theorem remains open.

The original calculus and machine are attributed to Mira-Cult,
upstream verification to Jeff Ketchersid, the register framework to Andrew
James Wade, and the subsequent source rotations and reductions to their
retained ProveIt and incoming-report attributions.
