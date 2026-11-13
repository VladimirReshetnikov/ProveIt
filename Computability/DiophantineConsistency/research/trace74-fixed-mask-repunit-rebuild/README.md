# Held fixed-mask repunit check

This one-stage check targeted the [source-reviewed](../../reviews/trace74-fixed-mask-repunit-source-independent/README.md) same-repunit radix and mask-population lemma against the audited fixed-mask saturation parent union. All six direct project imports were selected from the captured parent; read-only preflight, 25 policy controls, six supervisor controls and [independent prelaunch review](../../reviews/trace74-fixed-mask-repunit-prelaunch-independent/README.md) passed.

The attempt terminated with actual outer exit 1. Lean reported an unevaluated exponent warning for 590069 and recursion errors in the beta and mask-population simplifications; its `sorryAx` report is consequential and no theorem was accepted. The child SHA-256 is `c21a81c1e2ac5fd136a4b86c979404ebf51c7dfc748ec3aa71050ee5caa4370e`; the outer terminal SHA-256 is `c1e3ba28ec97adfbb3b3d6f36616ff9d6469d556c2ac896440d0d6605eaf0b14`. The [independent factual review](../../reviews/trace74-generic-repunit-population-draft-independent/README.md) checked that failure. A separate abstract factor is under preparation.

The positive repunit witness is explicit and is not derived from a 74 zero. Captured source/package/dynamic ancestry, inherited exact unevaluated-power warnings and external file binding remain limited as documented by the parent.
