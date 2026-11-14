# PA194 genuine marker path to dense state 84

`PA194MarkerTo84.markerTo84` extends the genuine non-first marker path in
`MARKER-HEADER-RECURRENCE.md` through its next controller branch to dense
state 84. The exact returned header does **not** repeat the earlier
at-least-five branch: it follows the four-one path to state 61. From there
`PA194State61Return.state61To84` checks the ten pinned rows

```
61 → 76 → 87 → 46 → 65 → 49 → 69 → 94 → 50 → 70 → 84
```

in every candidate PRA model. For arbitrary model values `l,x`, the segment
starts with tape halves `(4*l+2,4*x)` and returns exactly those halves. The
packed stepper is run for exactly ten steps, including in nonstandard
models. `PA194LeftRows.leftZero` supplies a reusable checked left-moving row
contract.

The composed theorem covers all non-first physical marker positions, under
the exact `k=1` initial header and delimiter/file assumptions, selected
register value nonzero, and initial first physical register value `k+7`.
It derives the selected-register predecessor and the updated remaining file
`p=2*r`. At state 84 the right half is exactly
`zeros(2, zeros(k, 1+4*r))`, and the left half and complete clock are given
explicitly in the theorem. The initial first-value-six case, selected-zero
case, state-42 zero-residual case, and other header cases remain open here.

The packet metadata `docs/pa194_conpa_2026-11-13/construction/tables/pa194.labels.json`
(SHA-256 `b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964`)
maps dense 84 to native 35, and maps the native source-root control 84 to
dense 24. This is an external metadata lookup; full native/dense conjugacy
has not been verified in Lean. Dense state 84 is an exact physical endpoint.
This theorem does not identify it with a source root, establish a source-frame or source-operation
correspondence, or prove that its starting tape is reached from the blank
tape. It proves neither PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-to-84.sh
```

An independent suffix replay rebuilt all five new modules in order against
separately checked controller objects and preserved prerequisite/scratch
overlays. Their reported theorem dependencies did not include `sorryAx`.
The complete nested replay is running separately.
