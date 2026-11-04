# Beta-only cover check with one exact warning

The [independent prelaunch review](../../reviews/trace74-cover-bind-beta-exact-warning-prelaunch-independent/README.md) approved one check under a policy permitting only the previously observed source-location warning that exponent 8807 was not evaluated, followed by the exact `[propext]` report for `Trace74CoverBindBeta.cover`. The threshold was not changed; all other warnings, output, axioms and stderr remained rejected.

Attempt01 completed with actual outer exit 0 and child status PASS under that explicit policy. The [child result](observations/attempt01/result.json) SHA-256 is `4aabf2bba3e729a9d3e92bb8f13e342ad8f7168abfdb725d0205323f7b51e462`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `69bf2d41c543bab901d3bc511a992c961af3fbade8aab07f95b923aeb3af205e`; object SHA-256 is `d3770ef007c07da40a0d960cf079981700f1af511b0c40341d821fffc5e57467`. The [independent result audit](../../reviews/trace74-cover-bind-beta-exact-warning-result-independent/README.md) passed. The exact warning remains in captured output, and the earlier strict-policy rejections remain separate.

The theorem fixes beta only; low, defect and high and their hypotheses remain explicit. It does not establish concrete mask coverage or a graph guard. Capture-relative historical source, package and dynamic ancestry limitations remain.
