# Complete symbolic high-mask fields for marked compact cells

`CompactMarkedHighFields.marked_high_fields` proves in every model of IΣ₁
both high-mask fields required by `PackingInput` for the actual zero-dummy
base cell family and for an arbitrary globally Boolean pulsed family. Its
assumptions are Σ₁-definable row and pulse functions, `CompactWord row N s`,
`1<N`, `0<s<N`, and `∀j, δ j ≤ 1`. In particular it proves:

* origin no-carry against the **decremented** symbolic high mask `highNat-1`;
* ordinary no-carry against `highNat` at every non-origin in-range cell;
* both assertions for the base family and the pulsed family.

The theorem first uses the complete ordinary all-index symbolic high-mask
safety theorem, then applies the separately proved marker-origin residue and
high-mask decrement transfer. It introduces **no high-mask assumptions**.
Its pulse has no support-away-from-origin assumption because these particular
high fields do not need one. This remains a model-level symbolic packing
component, not a proof of graph-zero construction, retained/document-byte
binding, an internal iPRA derivation or a consistency statement.

The first guarded author attempt failed on a missing namespace; its exact
source and compiler log are retained. The corrected session `7677` exited 0
without warnings or `sorryAx`; the named theorem's Lean axiom report lists
only `propext`, `Classical.choice`, and `Quot.sound`. Sampled direct-import,
companion, selected provider-root and mixed-overlay guards were unchanged.
Source/object hashes, command, dependency scans, logs and complete provider
overlap preflight are retained. Package, transitive, dynamic and
between-observation ancestry remains inherited; `/tmp` provider paths are
ephemeral. This is not an independently authenticated complete closure or a
paired replay.
