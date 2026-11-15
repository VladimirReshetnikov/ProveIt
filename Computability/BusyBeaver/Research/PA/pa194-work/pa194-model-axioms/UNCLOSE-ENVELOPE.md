# Bounded recovery of the source property

For each PRA plus IΣ₁ model and each internally valid arity-zero formula p, `uncloseOnce_closeOne` proves that stripping a newly introduced universal quantifier and opening its body recovers p. `uncloseMany_modelClose` extends this to any model-valued number of steps, including nonstandard counts, by internal Σ₁ induction. A fixed Σ₁ PR blueprint computes a reverse-opening sequence, and `uncloseHistoryGraph_iff` gives the parameter-free Σ₁ graph of the unique sequence of length n + 1.

Let q be `fullyClosedSeparation φ`, with φ an internally valid arity-one property. `fullyClosedSeparation_property_bound` proves `φ < uncloseHistory q q`. The argument uses the already checked bound on the number of closures, recovery of the separation root after that many steps, containment of φ in the root code, and the fact that entries are smaller than their HFS sequence code. This provides a model-level candidate witness envelope for a bounded classifier. Generic arithmetic-model interpretation of the envelope and an actual uniform Δ₁ classifier are not established by this replay; neither is a native iPRA derivation.

Run from the repository root, with a fresh final output path:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-unclose-envelope.sh "$PWD" \
  /dev/shm/pa194-fully-closed-replay \
  /dev/shm/pa194-unclose-envelope-replay
```

The two sources and six-declaration audit are rebuilt in one output, the source hashes and one selected imported object are checked before and after, and the checker rejects `sorryAx`. Other prerequisite objects and Foundation are prebuilt. The successful log is `/tmp/pa194-unclose-envelope-replay.log`.
