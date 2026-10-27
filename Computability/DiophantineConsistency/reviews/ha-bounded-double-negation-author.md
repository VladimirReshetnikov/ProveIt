# Finite bounded double-negation shift inside HA

26 October 2026. Author: `circuit_reduction`. This is the first approved
implementation from [the negative Σ1 calibration audit](../research/ha-negative-sigma-one-calibration-audit.md).
The preceding bounded-quantifier and DeltaZero/GG packets remain unchanged.

`HABoundedDoubleNegation.lean` proves the actual PAHF object-language result

```text
HA.Proves
  ((ball t (doubleNeg a) → doubleNeg (ball t a)) ∧
   (doubleNeg (ball t a) → ball t (doubleNeg a))).
```

The matrix `a` is arbitrary, including unbounded quantifiers. There is no
decidability, syntactic hierarchy, or stability premise on it. The term `t`
may contain any free parameters. `bounded_doubleNeg_relative` retains both
directions in every finite open context by actual HA weakening.

The forward shift uses the existing genuine HA formula-induction axiom on
`shiftBody a`. Its free induction variable is a new ambient parameter;
`plus a = rename (up succ) a` preserves the bounded witness at slot zero
and shifts the original ambient parameters. `shiftBody_inst` and
`shiftBody_succ` prove the exact capture-avoiding substitutions. Thus neither
the zero nor successor step silently changes the original matrix or bound.

The zero step uses the already proved empty bounded universal and logical
double-negation introduction. The successor step splits the literal bounded
universal into its preceding interval and final instance. The induction
hypothesis handles the preceding interval, while the new purely logical
`doubleNeg_pair` combines two double-negated formulas without any decisions.
The accepted bounded-successor reverse implication is then transported
under double negation. `doubleNeg_pair` retains an arbitrary finite theory
and context; it is not an arithmetic axiom.

The converse introduces a bounded witness and shifts the **whole** existing
assumption context. Bounded elimination gives an implication from the
shifted universal to its instance, using the ordinary strict-order witness
already in context. Mapping this implication under double negation proves
the required instance. No witness is extracted from a double negation.

The 56-line focused checks cover an entirely arbitrary matrix, zero and
successor bounds, a nested universal/existential matrix with sparse free
variables, a compound bound containing slots 0, 4 and 11, exact successor
substitution and bound instantiation, renaming under the bounded binder,
and arbitrary shifted finite contexts. All eight axiom reports contain
only `propext` and `Quot.sound`; the two substitution identities use only
`propext`. No classical proof rule, model semantics, `sorry`, or `native_decide`
was introduced.

I fully read both new files and the entire replay driver before execution,
then reread the final main and reports. The private cache was traversed from
current imports and reauthenticated: 101 cached modules, including 76
Foundation modules, 329 cached artifacts, and 34 explicit external
package/toolchain boundaries. No reused client imports either new leaf.
All 718 distinct inherited and explicit pins matched before and after the
fresh runs. Original author provenance is retained alongside the selected
accepted bounded-quantifier root record
`8a321ccb5e0f1860701fd8e1e5319027de7ccc8e15458aac09a286ead4b9808c`.
The primary actually imported is
`/tmp/ha-bounded-quantifiers-root-peer-gtq42hal/lib/DiophantineConsistency/HABoundedQuantifiers.olean`,
SHA `5aef4873ce228ef55ac107f2fb0c251da951552feee7d0acb92f0ca3061a992f`.

Only the two new leaves were freshly compiled with Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, separate regular private output paths, and
the 512MiB disk reserve. Final main/check PASS took 1.759s/1.532s. The main
log is empty; checks contain eight reports. Final private primary:
`/tmp/ha-bounded-double-negation-author-dk1jfmzz/lib`.
There was no Foundation/prerequisite compilation, shared-object overwrite,
or resource-limit increase.

Two earlier main failures are preserved with complete source snapshots,
commands, input pins, diagnostics and status. The first attempted to open
the filename `HANegativeStability` as a namespace; this caused cascading
unknown-identifier errors. The namespace is `HA`, so that extra name was
removed in both files. The second exposed an unavailable convenience-helper name
and an underspecified bounded-elimination hypothesis. The final proof uses
the public logical introduction theorem explicitly and types the bounded
hypothesis explicitly. These fixes changed no theorem statement or
mathematical assumption. No checks or prerequisite compilation failed.

Frozen pins:

- Main source: `5a2629d92e19051bbe18e77ded0a75c0e96457d55cf045410d0aaa1d747ea04f`.
- Checks source: `580f6b52c7a5eaa4d3bf72562b03cbc8c5ca037e7ef8c024963e11e18920459a`.
- Main object: `f0e760efed2f33d6b23e19b83266c479212d7a19cc51b011f8f26c3f4ea14344`.
- Checks object: `5d1521ac773295eaa1fe17a5ea4674a8ead35e81fbdef91cdc897b0e6704b7cd`.
- [Replay summary](ha-bounded-double-negation-replay.json): `8c0e5b8cba14cd11d17f4c85082f34f330bce09ca6f7fe19a42385c2711bdb8c`.
- [26-file manifest](ha-bounded-double-negation-replay/FILES.json): `b70e601335eb7fbf27d3e3c8edf4b9f4d0d133b3fa02aa2a3154a755cc9ad6de`.

This is finite bounded double-negation shift inside conventional HA. It
does not provide unbounded double-negation shift, positive Σ1 elimination,
Markov's principle, the proposed hierarchy-one comparison, normalization of
an actual proof checker, or the current equation's HA consistency
equivalence. No frozen source, vendor file, shared document, displayed
equation, or Git state was changed.
