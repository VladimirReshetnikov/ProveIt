# Actual Foundation parameter closure: root author receipt

26 October2026. Root authored and fully read both new files before execution,
each proof correction before its replay, and the complete final pair before
freeze. This is author validation, not an independent review.

`FoundationHAClosure.sentence_univCl` proves the exact identity

```lean
sentence (Semiformula.univCl φ)ᴺ =
  SetTheory.PA.Formula.closeN φ.fvSup (formula φᴺ)
```

The left side uses Foundation's actual classical closure implementation:
`fvSup`, `fixitr`, universal closure and `toEmpty`, followed by the existing
GG translation and checked syntax interpretation. No replacement closure
convention or supplied syntax-agreement premise occurs. The proof reuses
the existing GG embedding/rewriting laws and proves only the missing
all-quantifier and canonical-environment identities.

The canonical target interpretation of `fixitr 0 m` is the identity at
every source free index: indices below m become bound slot x; all remaining
indices become free slot m+(x−m)=x. Thus this syntax identity even covers
closure counts too small to bind every source variable. No unsupported
free-variable bound is used. The final `proves_univCl` turns an actual HA
proof of the translated open body into an actual HA proof of the literal
closed source image by the already checked HA universal-introduction rule.
It does not prove an arbitrary body's HA provability.

Focused checks cover count0, count3 below a sparse variable7, count12 above
all parameters, nested universal/existential binders with interpreted order,
and a concrete HA proof for the closed source `&7=&7`.

Frozen main source SHA256:
`593d4672ff5a2bfead2f8771a1b94273319f441e84732df57229cb11447e8b31`.
Checks source:
`c1ce4c4ca55750971392ad2dc7bb308ad0f93e51e8d9c50da64189b93f4d467f`.
Final objects:
`233f1a4a4b4bb29791e58dbc838cb668a64161940c5f2b12412a90b33464b2c6`
and `2dc273bf3644a046e80b9848bdbfb96f9638badc68a60bd5f07645bcb0a770f4`.

The final main and checks passed capped direct compilation with `-M6000
-j1 -DElab.async=false`; the main log is empty. All six final axiom reports
use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The
classical metatheoretic dependency occurs in the existing source-closure/
embedding identity; it adds no classical rule to the actual `HA.Proves`
derivation. Both the precise syntax statement and HA proof constructor
are retained, rather than interpreting this audit as a choice-free result.

The private overlay `/tmp/foundation-ha-closure-root-fjkgfcn6/lib` reuses
the88 authenticated prerequisites of the accepted Foundation arithmetic
packet, including76 Foundation modules. All491 source/cache/trace/object/
prior observations were checked before and after each invocation. Compiler
and package identities were rechecked at freeze. No Foundation, package
or broad custom closure was freshly built; only the two new leaves were
compiled. The driver enforces a512MiB disk reserve.

The first main run exposed a notation-specific rewrite match and residual
`0+n` normalization; its two proof-only corrections left all theorem
statements intact. The first checks run needed an explicit import for the
existing double-negation-introduction helper. Those failed drafts/logs are
preserved, and their failed declarations are not accepted. No successful
main was rerun without a change. The final six reports contain no `sorryAx`.

All14 author bundle files are durably pinned in
`foundation-ha-closure-author-replay/`. Aggregate replay SHA256:
`88cf1f0983335cd29fafcc99fbaea13a6c39033e4d822d9885f81e23aae1bfbe`.
The remaining arbitrary induction-body and order-axiom proofs still need
their own derivations; this closure result does not establish the final
HA equation/consistency equivalence.
