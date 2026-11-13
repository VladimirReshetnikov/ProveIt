# Isolated sign-free model arithmetic replacement

This is an inert, unelaborated source alternative. It leaves the pinned
historical `ResidueSignFreePower.lean.src` and every existing provider and
receipt unchanged. No Lean build, staging, provider authentication or axiom
inspection occurred.

The original imports `Mathlib.Tactic.Omega`, absent from the currently
observed mathlib source tree, and uses `omega` at three points on abstract
model naturals. The replacement changes that import to the locally observed
`Mathlib.Tactic.NormNum` and `Mathlib.Tactic.Ring` sources and replaces the
three calls with explicit ordered-model arithmetic:

* `q | 3X`, `0<X`, and `46≤q` give `q≤3X`; assuming `X<16` gives
  `3X≤45`, contradicting `46≤q`.
* Set `r=n−1`. The existing predecessor identity `r+1=n` and `13≤n`
  give `2≤r` by addition cancellation.
* The same predecessor identity and `2n=R+1` give `R=2r+1` by adding
  one to both sides and cancelling it.

The three theorem signatures and namespace are byte-identical to the
original. The third theorem's entire body is byte-identical. The exact new
proof scripts are unelaborated; the source and import observations do not
establish that any new tactic or theorem elaborates in the selected model.

## Source-level rewire, not performed

The fixed85 local lexical manifest has one direct importer of logical module
`ResidueSignFreePower`: `ResidueQBalanceGraph`, which calls both the growth and
oriented-power declarations. A future isolated overlay could select this
alternative as the **sole source provider under that original logical module
name**, preserving its namespace and existing import signatures; it must not
also load the original provider in the same Lean environment. The alternative
file's current basename is intentionally different, so merely adding its
current directory to a search path does not perform that override.

The receipt records 38 reverse-reachable local modules including the
replacement and `Fixed85Endpoint`, in dependency-first order. Those modules
would need fresh consistent compilation after the override; all their other
transitive dependencies, local/external frontier and object search-path
collisions still need a fully selected, authenticated provider plan. The
original 1,354-module lexical inventory does not prove a runnable closure or
safe resource availability. No existing object, source or evidence is to be
silently overwritten, and these observations do not reserve disk space.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-signfree-omega-repair-draft/check.py
```

The checker pins the old and new sources and fixed85 manifest, compares all
three declaration signatures and the unmodified power body, recomputes the
bounded reverse import closure, and runs finite integer controls. It checks
only source presence for the named mathlib modules; it does not execute Lean,
validate the three replacement proofs, inspect compiled providers, or prove
any equation endpoint.
