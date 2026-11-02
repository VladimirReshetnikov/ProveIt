# Independent corrected coefficient replay prelaunch review

The exact corrected driver at commit `4d588b060e`, SHA-256
`604bf5a6e45bc2852fbff3482684479b52517e814503a48617626ff28e0505bf`,
passes this no-Lean prelaunch review. The author’s corrected real no-Lean
preflight session 23392 exited 0 at its recorded HEAD; its observation is
committed at `99f636f35f`. Independently, session 60936 reran the driver’s
`verify()` directly and exited 0 with the full closure review and both parent
audits matching; it did not itself enforce a stable HEAD. Its output is
`parent-verify.json`, SHA-256
`0a41f82e7dec99b719096d2ba512291fd95ba2bd52c627fb4ad94fdbe67b39e6`.

The exact driver, closure and parent pins, source imports and three exact
report names/axiom sets were reviewed. The author's full fake loop was rerun
and matched its committed 41-line output. Three independent full-loop
regressions based on the earlier reproductions now all reject before a fake
compiler child: a seed companion injected after copying, a symlinked seed
directory (no seed written outside), and a symlinked frozen-source directory
(no source written outside). Each independently rerun regression exited 0;
all nine non-object output slots were also exercised. The corrected driver
checks source, seed and output locations and slot states at stated points,
including after parent callbacks. The original seed defects are preserved in
`../compact44-coefficient-decomposition-prelaunch-defects/`. These are
point-in-time checks, not atomic path traversal or continuous protection.

Static/fake review session 11834 exited 0 and produced `CHECK.json`, SHA-256
`e705b30ea466e2471f994d6516d0cf77dd2e2684cf4912a1a131ddfc7208bd56`.
Optimized execution was rejected. This is **not a paired build or artifact
audit**. A fresh protected stable-HEAD/sole-Lean window and trusted clean
initial loader are still required. Compiler RSS/disk limits are sampled;
`lean --deps` and audit subprocesses have distinct timeout/process limits.
The theorem remains a finite model identity for arbitrary selector/copy
functions, with graph-column equality, Boolean and `NoCarry` inputs, retained
K/ports, machine equivalence and internal iPRA all separate.
