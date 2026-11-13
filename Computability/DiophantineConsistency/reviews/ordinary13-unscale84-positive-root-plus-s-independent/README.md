# Independent source review: shifted positive unscaling root

This is a source/mathematical review of
`research/ordinary13-unscale84-positive-root-model-draft/`. No Lean, builds,
staging or provider replay was performed. The receipt pins both fact-level
source dependencies and reproduces the author's checker output.

The first helper assumes natural `P=b*t>0`, `t>0`, and `ell+s<tau`, and
chooses the fresh positive natural

```
r = k*(P−1)+t+(tau−(ell+s)).
```

The two subtractions here are natural subtractions, justified by `P>0` and
the strict margin. In the signed difference ring, the proposed target root
has the **essential plus s**:

```
b*(ell+k+r+s-k*P)-P = b*tau.
```

The receipt verifies this exact identity in a free integer polynomial ring
under `P=b*t`. Removing `+s` changes the root by `−b*s`; this is a formal
control, not an actual graph-zero example.

`shifted_root_of_source` calls the source first-root extraction with the
same b, ell, k, source carrier and source signed root, then uses the **same**
extracted tau and its norm in the explicitly assumed universal margin. It
constructs a fresh target r and does not assert that the original r minus s
is positive. `shifted_root_of_qcube` keeps its explicit `b>0`, `q≥1`, `X≥1`,
`s>0`, `Y=q³*s`, large-k, signed source-root and source-norm premises. Its
call to the separate `qcube_margin` draft matches those hypotheses and rewrites
the first norm by ring algebra. This review checks the interface and plus-s
identity; it does not independently validate the unelaborated margin proof or
the signed carrier-extraction proof.

No actual 84 or 87 graph, port representation, norm extraction, positive
carrier, graph zero map, compiled model provider, axiom report or iPRA/ZFC
endpoint follows from these fact-level source statements.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-unscale84-positive-root-plus-s-independent/check.py
```
