# Source plan for a coherent printed-port extension

The active [fresh endpoint build](../current14-standard-fresh-rebuild-preflight/README.md)
contains the standard 14-variable endpoint but does not include the two
project modules imported by the existing
[`Current14LiteralPorts.lean`](../current14-literal-port-assembly/Current14LiteralPorts.lean)
printed-recipe assembly. To plan a later join without combining historical
object overlays, we froze the declared project-source closures of
`CurrentKernel2011` and `CurrentMaskRecipes2011` with the existing
`fresh-project-closure/prepare.py` tool, using the same workspace on
2026-11-04. Their manifests are retained here.

The [audit](result.json) finds 84 modules in the union: 23 already in the
active build's 1,000-module frozen manifest and **61 additional project
modules**, listed in a valid source-declared order. All 23 shared source
hashes match the active build snapshot; all 84 extension-source hashes match
the workspace at audit time. The two extension manifests also agree on all
shared modules. Three direct external module names are new relative to the
endpoint manifest: `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
`Mathlib.NumberTheory.Wilson`, and `Mathlib.Tactic`.

This is a **source plan only**. It does not claim the active build will pass,
that the 61 modules can be safely compiled atop its result, that direct or
transitive package objects are authenticated, or that a printed-port/iPRA
join exists. In particular, before attempting the extension, a successful
base build, stable source hashes, exact module resolution and the three new
external inputs need checking. The assembly itself and its research-level
client are additional modules beyond the 61. Its [previous author check](../current14-literal-port-assembly/README.md)
used a different mixed provider. A separate [syntax-join draft](../current14-printed-syntax-join/README.md)
has not passed Lean due to kernel memory exhaustion; this plan does not fix
that failure or establish TeX/PDF semantics.

Re-run the comparison from the repository root (ordinary Python only):

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-printed-port-extension-plan/audit.py
```

It hashes each current extension source, validates the pinned shared hashes and
source-declared order, and prints a deterministic result. The committed
`result.json` is the captured point-in-time observation; future source changes
can cause the script to refuse. Like the underlying source scanner, it is not
an authoritative account of dynamic loads or of every possible Lean import.

A separately [reviewed extension driver](../current14-printed-port-extension-driver/README.md)
now prepares this sequence and refuses the still-running base. Its successful
preflight and build paths remain untested; it has not been launched.
