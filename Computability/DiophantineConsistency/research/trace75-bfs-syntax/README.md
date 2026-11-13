# Trace75 literal syntax

The existing canonical `TenPositiveTrace75Syntax.lean` defines the
`Expr (Fin 10)` for trace75 and proves that it evaluates to `value75` in any
commutative ring. This folder's copy is byte-for-byte the canonical source
with a single appended `#print axioms` command. The runner checks this
relation and the canonical source hash before compiling the copy.

The author check `attempt01`, tool session 34557, exited 0 and is reaped.
The reported axiom set for `evalRing_expression` is `[propext]`. The output
`/tmp/trace75-syntax-ql2wu2mb/DiophantineConsistency/TenPositiveTrace75Syntax.olean`
has SHA-256 `8349c9a4d22b2bdd2b3cb475570430b1df30a8e7f4e5e8ede9f40fb13a361d68`.
The source SHA-256 is `46aacc7b43fc5e42095a36265e6ba34853b7aeae70f053b289553ed4dcb18068`,
runner SHA-256 is `d0bc3a6b30e82d5860d8bdfc35abb0025dfa7704e2a739504201283047c8948b`,
and the terminal record SHA-256 is `a337790dd0dc729ffba6cee5c20e6c926fd24a9b9c1acf101b47e4ae48a81b0b`.
The selected direct fresh-provider objects were pinned; their transitive
project, package, dynamic and source ancestry remain inherited. No
independent Lean replay or external JSON/PDF binding is claimed.

`Trace75BFSSyntax.literal_zero_iff` further proves, for arbitrary natural
ports and model-natural coordinates in any `IΣ₁` model, that `InternalZero`
of that literal expression is equivalent to actual trace75 `value75=0` in
the model's difference ring. This is an arbitrary-valuation syntax binding;
it does not assert a positive zero, a halt equivalence, or iPRA derivability.

The model-binding author check `model-attempt02`, tool session 78246, exited
0 and is reaped. Its object
`/tmp/trace75-modelsyntax-i60jel9j/Trace75BFSSyntax.olean` has SHA-256
`15c89721715979a0071a7e5fa1bfca8d4188fd38b22480f4008532a09b5e3e9c`; the
axiom report is `[propext, Classical.choice, Quot.sound]`. Source SHA-256 is
`f71d277d0e04a9e516f91df0ebdcd233306f5c82200607faec93e444148ef3c4`, runner
SHA-256 is `aa368b858432b6b68b1fdad86b1220b3f4f2c289224f08ab3cdd6c0e3adc3ee3`,
and terminal record SHA-256 is
`89b3d9896560c50a6c82a4babf2380b7a6dac90ea3200aa60be11fbeadfdaa15`.
The failed first model attempt remains in `observations/`.

This binding used the inventoried merged namespace overlay in
`overlay-inventory.json` (SHA-256
`43f46b4876d7d269212f473746dd5079760d6c20188c575049ed1bf03dc6bcc5`):
the earlier fresh trace75 namespace plus the new syntax object. The overlay
links and selected direct objects were checked before and after the run;
other target bytes and transitive ancestry remain inherited. This earlier
provider does not by itself resolve the known mismatch with the BFS reverse
provider. A later source-coherent endpoint must be rebuilt or reconciled on a
compatible union.
