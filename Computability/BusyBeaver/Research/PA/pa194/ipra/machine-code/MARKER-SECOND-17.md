# PA194 marker path through dense 84 and back to dense 17

`PA194MarkerSecond17.markerToSecond17` extends the genuine marker path in
`MARKER-FROM-84.md` through dense 15, 16, and 17. It covers every non-first
marker position in every candidate PRA model, including nonstandard register
values and scan lengths. The exact initial `k=1` header and delimiter/file
shape, a positive selected value, and first physical register value `k+7`
remain assumptions. The first-value-six, selected-zero, state-42
zero-residual, and other header cases remain separate.

Write `2*r` for the exact updated file after the first physical block and
`s = 3 + 8*r`. The final right half is `1 + 4*ones(k+1,s)` and the left half
is the explicit header-derived value `a2` in the theorem. The complete clock
is model-valued. `PA194EightyFourTo17.returnedFileTo17` independently
connects the exact dense-84 returned-file shape to dense 17 via the dense-15
transition and the existing all-model dense-16 scan. This second dense-17
configuration has a different left layout from the earlier `k=1` header;
no particular subsequent branch or source frame follows automatically.

The theorem establishes an intermediate physical run. It does not prove
blank-tape reachability, a source-operation or source-frame correspondence,
or either PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-second-17.sh
```

An independent suffix replay rebuilt the two final modules against separately
checked marker and controller objects and preserved prerequisite/scratch
overlays. The reported theorem axioms did not include `sorryAx`. The redundant
full nested replay was stopped to reduce I/O; the shared comprehensive
`check-file-traversal.sh` replay subsequently passed.
