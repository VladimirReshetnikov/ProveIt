# AQ22 historical matched-pair terminal observation

The separately observed launch session `59884` exited **0**. Its complete
tool-provided output is in `outer-terminal-observation.json`: the planner
reported 15 historical-parent source drifts, the freezer and preparer
reported success, both sibling rebuilds exited 0, and the coordinator printed
`MATCHED_SELECTIVE_PASS 37 affected modules`. The launch script is preserved
as evidence of what was run; this is not an instruction to overwrite run-02.

The captured coordinator observation separately records its actual exit 0,
stdout, and the pair-state hash. `pair-state.json` reports both sibling exits
0 and a matched comparison; its SHA-256 is
`236d033025c497f98805a14d2487e761b6e6a44f090d058a5a944684381bc845`.
The freezer and preparer process observations are copied without alteration.
The snapshot contains 1,210 frozen historical parent sources and 37 added
sources; the sibling runs reused only their own corresponding authenticated
parent seeds. The 37 additions include the AQ26 and standard-iPRA chain.

The subsequent [independent full artifact audit](../ipra-aq22-historical-pair-independent-audit/README.md)
passed, including both sibling states, outputs and guards. The complete run
remains at `/tmp/ipra-aq22-historical-paired-run-02` while that directory exists.
It proves nothing about current workspace sources differing from the frozen
parent, runtime/package-transitive ancestry, or temporary mutations between
guard checks. The Foundation wrapper's outer exit was not captured; its inner
Lake exit and the separate provider verifier's exit were observed as zero.
The mathematical interpretation of the selected translated consistency
sentence and the displayed equation remain separate proof obligations.
