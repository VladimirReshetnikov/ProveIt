# Actual 76Y-zero free-main gap positivity

[`FreeMainGraphForward.lean`](FreeMainGraphForward.lean) now has a successful
[guarded Lean check](observations/attempt03/result.json), with exit 0, no
warnings or `sorryAx`, two expected axiom reports, stable direct input guards,
and no monitor stop. The object hash is
`3ba1958eac1aabec050e1acc0017ef7cc4cf5722d61b1ab21dae90f70588b085`.
The source hash is
`eeb3d8314793b90e2d6a33d928fb983d5bed6b145c5f9e09d3e9766a7a14c3e5`.
The check used Lean `-M2400`, a 120-second bound, sampled group RSS stop at
3.5 GiB and host available memory stop at 10 GiB, nice 19, and idle I/O;
it did not stop the concurrent base build. It guards direct providers and
inherits their transitive and dynamic ancestry.

For every positive 76Y graph zero in a model of `IΣ₁`, the checked theorem
`actual_gap_positive` proves `U gamma−(k−R−1)>0` in its difference ring.
`exists_positive_main_gap` supplies a positive model-natural value represented
by that difference. The proof lifts the q-cube witnesses, extracts `M=Lt=0`,
uses transport for the root lemma's positivity and gap hypotheses, and applies
`P64Root.main_root` to recover both the oriented Pell root and carrier
alignment. It then applies the separately checked generic
[`FreeMainForward`](../p64-qcube72-forward-model-guarded/FreeMainForward.lean)
positivity result.

This is an actual-zero positivity theorem, not a checked 72-operation graph
binding, reverse witness map, zero-existence equivalence, or iPRA endpoint.
In particular the reverse map's divisibility condition remains unresolved.

The first [attempt](observations/attempt01/result.json) had Lean exit 0 but
the runner failed it for one unused simp-argument warning. The warning was
removed. The second [attempt](observations/attempt02/result.json) was safely
stopped when its monitor saw another non-base Lean process; it had no object.
Exact sources, logs, and receipts for all three attempts are preserved.
