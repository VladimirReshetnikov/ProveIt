# Independent review: 87-to-86 w-coordinate transfer

The proposed source uses the correct coordinate-6 valuation maps and the
unconditional forward eta map to obtain its separate w-positivity premise.
The compact no-zero directions and parent-bridge argument order match the
pinned interfaces. No source-level direction or tuple mismatch was found.
The draft and its dependencies remain unelaborated; this is not a graph-zero
proof or an iPRA endpoint.

The 87 parent uses `w=n_w+1`; the 86 child uses coordinate 6 directly.
The generated literal rows match their pinned graph JSON, and substituting
`n_w` for the parent's w after deleting only the w-increment row yields the
86 rows. Thus the proposed evaluation compares parent v with child
`raiseW v`. A parent zero gives an 86 zero, yielding 86 no-zero implies 87
no-zero. For the converse, the client needs positive coordinate 6 at an
86 zero so that `raiseW(lowerW v)=v`.

To propose that positivity, `w_positive` maps the same 86 zero **forward**
through the earlier eta `zero_iff` to the 85 prototype with coordinate 9
raised. That eta map leaves coordinate 6 unchanged. It then applies the
prototype's separate `witness_positive` source with the same natural ports
and an explicit positive beta cast. This use does **not** assume the
all-model `ForcedEta` premise or the reverse eta zero map. Its correctness
still depends on the unelaborated forward evaluation, unit-factor, J/X
positivity and provider sources.

At compact symbolic `ports K`, the pinned `beta_at_least_46` source is used
to propose the positive beta cast before the 86→87 no-zero equivalence.
`SameNoZero` is ordered as 86 child then 87 parent, and the generic bridge
transports an **explicit** exact 87 `PolynomialBridge` assumption to 86.
The separate final 85-native client additionally requires `ForcedEta K`;
neither that all-model forcing nor the 87 parent bridge is established by
this packet. Both use the same K/tuple, whose physical-byte and PDF
associations remain open.

From this directory run

```
python3 -I -S -B check.py > /tmp/w86-to87-direction-independent.json
cmp result.json /tmp/w86-to87-direction-independent.json
```

The checker pins key source files, parses both exact parent literals, checks
the two row substitutions and runs 400 bounded valuation controls for
87→86→85, including that the eta raise leaves coordinate 6 unchanged.
Those controls do not establish all-model forcing, Lean elaboration, provider
closure, zero maps or the iPRA target. No reviewed source was modified.
