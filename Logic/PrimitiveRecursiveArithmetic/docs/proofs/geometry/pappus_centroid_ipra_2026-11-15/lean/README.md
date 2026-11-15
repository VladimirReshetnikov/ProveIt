# Lean files

## `PappusFinite.lean`

A no-`sorry` semantic algebra scaffold over an arbitrary linear ordered field.
It proves:

- finite polygonal sweep = `tau * radialMoment`;
- the centroid quotient form under nonzero length;
- the one-cell annular-shell identity by `ring`;
- finite grid volume = `tau * radialMoment`;
- the centroid quotient form under nonzero area;
- the rational examples from the report.

The definition of one segment's `sweep` is the target value.  The substantial
next theorem is to derive that definition from the regular-polygon frustum
brackets.

## `PappusRoadmap.lean`

A type-directed outline against the current ConciseIPRA interfaces.  Every
`axiom` is an explicitly named remaining obligation.  The last two theorems
show the intended use of `FromPRA.interp.sound` after the ordinary `PRAAx`
derivations have been supplied.

## Suggested check in ProveIt

At the pinned commit, place the files in a source directory visible to Lake,
then run commands of the form:

```bash
lake env lean path/to/PappusFinite.lean
lake env lean path/to/PappusRoadmap.lean
```

Lean and Lake were not available in the artifact-building container, so no
local kernel-check transcript is included.
