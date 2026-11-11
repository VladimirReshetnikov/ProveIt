# Exploratory rewrites of two 87/26 output forms

No graph with fewer than 87 live binary operations was found in the bounded searches below. This is a search observation, not a global operation lower bound, a Lean theorem, a provider replay, or a PDF/file-semantics binding. The source is the pinned shifted-guard 87 graph; its separately reviewed standard-integer calibration and its source/provider limitations are in `../ordinary14-shifted-guard87-calibration/`.

The scripts screen two forms with identical coordinates and ports. The parent output is the five-square sum `A0²+A1²+(Fa−1)²+g72²+guard²`. The sphere form removes the `Fa−1` gate, squares Fa, and subtracts 1 after the final sum, giving `A0²+A1²+Fa²+g72²+guard²−1`. Both have 87 live operations and the same specialized degree 26. On strictly positive inputs they have the same zero set: the unbounded conditional-sphere proof reviewed in `../ordinary13-freej88-conditional-sphere/` gives `Fa²+g72²−1≥0`, and equality forces `Fa=1,g72=0`; the additional guard square is nonnegative and unchanged. Conversely the old zero plainly makes the sphere zero. This is a positive-domain argument, not a signed-integer pointwise equivalence. The exact difference is `P_sphere−P_parent=2*(Fa−1)`; since `deg(Fa−1)≤13`, it cannot alter the parent's nonzero degree-26 leading part. The sphere form is an equal-metric search form, not an improvement.

`local.py` pins the parent and existing search engine. For each form, it screens one-gate and the engine's enumerated two-gate replacements at each single target, using three deterministic finite-field samples both with independently sampled ports and with authenticated compact44 port bytes. It separately screens earlier aliases and square-only sign reversals **using port-uniform samples only**. Available leaves are earlier wires and integer literals 0–4; output liveness must fall below 87. Each one/two-gate pass tested 87 targets, 873,422 first gates and 22,881 second-gate queries. No target or nonconstant divisor sample was zero, and no strict survivor was found in either form or sample pass. The uniform-only alias/sign helper found none; a double-negation alias positive control was detected. A finite-field survivor would need an exact identity proof.

`beam.py` imports only the pinned existing structural search's node, liveness, local ring-rewrite and replacement functions. It searches the parent and `--sphere` form separately to ten depths with width 300 and an intermediate cap of 89 live gates. The common-factor positive control reduces three gates to two. Both beams remained at 87 gates. Beam pruning prevents an exhaustive conclusion; these rules search exact polynomial rewrites, not arbitrary zero-preserving changes or reparameterizations.

All three scripts were run twice with byte-identical output. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-87-local-rewrite-screen/local.py > /tmp/ordinary14-87-local.json
cmp /tmp/ordinary14-87-local.json research/ordinary14-87-local-rewrite-screen/local-result.json
python3 -I -S -B research/ordinary14-87-local-rewrite-screen/beam.py > /tmp/ordinary14-87-parent.txt
cmp /tmp/ordinary14-87-parent.txt research/ordinary14-87-local-rewrite-screen/beam-parent.txt
python3 -I -S -B research/ordinary14-87-local-rewrite-screen/beam.py --sphere > /tmp/ordinary14-87-sphere.txt
cmp /tmp/ordinary14-87-sphere.txt research/ordinary14-87-local-rewrite-screen/beam-sphere.txt
```

This packet does not cover arbitrary new integer leaves, arbitrary larger replacement subgraphs, all coordinated rewrites, positivity-based witness changes, other residual encodings or global minimality.

Independent external review is recorded in
`../../reviews/ordinary14-87-local-rewrite-screen-independent/`.
