# Independent source review of the self-contained CD52 producer

The held producer `49099c1c05e6a18a6c500a46f190545abfa441330ddeee7880a39ac7af9f077d` is clear for an independent reproduction run. This review read the complete 246-line source and all three templates. It did not import or execute either producer and did not invoke a proof compiler.

The producer reads the exact attributed `DomRho8.4fdc.lean` as inert UTF-8 text. The derivation text is an ancestry input whose raw hash is checked; its contents are not interpreted to generate the proof. Both inputs and all templates have literal SHA-256 guards. The former delivered Python renderer is no longer an input or an import. The maintained script imports only Python standard-library modules.

The transformation selects the explicit d1–d52 bodies, changes the four discarded numeric fillers to their already-reviewed reflexive terms, replaces the five truth arguments by the arbitrary seed, and changes the numerical type/order notation. Per-block occurrence checks constrain these rewrites. The templates supply the same generic assumptions, six semantic helpers, seed discharge, public theorems and unchanged Nat adapter reviewed in the preceding mathematical receipt.

Its independent free-constructor audit checks all 58 private bodies in dependency order. Every MP checks literal major/minor agreement, each restricted row checks its order guard using only a hypothesis, reflexivity or left/right growth, and the local `happ` proof is checked before use. The specialized `under_antecedent` invocation is allowed only after that helper has itself been checked. No `imp τ τ = τ` equation, zero bound, transitivity, injectivity or substitution axiom is used. The d52 result is separately compared to the full unrestricted row.

This is deliberately a fixed-input syntax reader: its tokenization omits unrelated punctuation and is not a general Lean parser or a proof kernel. Literal input/template hashes and the final exact core hash prevent acceptance of a different generated source under this reviewed configuration. The expected source is `5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f`; the unchanged adapter is `8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378`. Changing those pins requires a new review. Normal Python is required explicitly, so `-O` cannot silently disable the assertions.

The CLI preserves the maintained behavior: no arguments checks the maintained source location, `--out DIR` writes the two Lean files and metrics under that output root, and `--out DIR --check` compares exact existing bytes without regenerating files. Root owns the actual reproduction and kernel receipts. No new theorem, compilation or whole-endpoint acceptance is asserted by this source review.

The rejected import-based predecessor and its reason are preserved under `history/producer-import-draft`. It would have called `importlib.exec_module` on the delivered renderer; it remained unexecuted. The new source-only receipt supersedes that design review without turning the predecessor into an execution failure.

No blocking finding remains. This review supplements, rather than replaces, the prior independent generic proof/API receipt `081a96980e1a2dca8eb7217e30b783a2a930c365ac536eed754d7bd4cb78b38e`.
