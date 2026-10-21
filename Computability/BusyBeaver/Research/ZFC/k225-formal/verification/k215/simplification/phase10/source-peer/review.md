# Independent source review of the generic 52-step successor

No blocking mathematical or source/API issue was found in the held candidate `5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f`. This is a source review and an independent finite syntax audit, not Lean elaboration or kernel acceptance. Neither the supplied producer nor a proof compiler was invoked by this reviewer.

The complete candidate and baseline generic core were read. The public `Language`, `rho8` and `Restricted` declarations (including every field), and the headers of public `rho8_all`, `composition` and `lift_right`, are unchanged modulo whitespace/comments. Imports remain exactly `Init`. The existing numerical `DomRho8` adapter is byte-identical (`8fdbec0d...6d378`); its `DomImp`, truth-free recovery, composition/lifting and numerical helper APIs are retained. The private K and Peirce formulas remain available as d12 and d18. There is no new bottom, zero, transitivity, injectivity, formula decoder or collapse equation.

## All 52 core steps and relation guards

The independent `check_source.py` reads the candidate's explicit formula types and proof expressions without importing the delivered generator or the author's audit. It treats implication as a free binary constructor and `τ` as an unconstrained atom. Each lemma invocation substitutes its explicit arguments into the already checked earlier statement; each MP requires exact antecedent/minor equality and exact result/declared-conclusion equality. Each restricted row must independently discharge its actual bound using only the current hypothesis, reflexivity or left/right growth. The own audit passes all 58 private bodies: the 52 core lemmas plus six semantic-tail helpers, containing 66 MP applications, 19 restricted-row applications and five uses of the seed theorem. It also compares the six public declarations above and the unchanged adapter.

The four modified fillers are exactly the proposed reflexive replacements: d3/d10 use `v1 → v2`; d7 uses `(v1 → v2) → v3`; d16 uses `v0`. In each case both occurrences in the major/minor instances agree and the restricted-row guard is reflexivity at that same formula. None survives in the conclusion. The five truth detachments d4/d9/d13/d18/d22 use the arbitrary seed `τ` as the antecedent of their major formula and detach `T τ`. No step equates `τ → τ` with `τ`, or normalizes either operand. All other bounds are the unchanged explicit subterm-growth or supplied inequalities.

This audit is deliberately narrower than a Lean parser: it accepts only the explicit prefix implication/proof grammar used by these bodies. Kernel checking remains necessary for elaboration, structure coercions, implicit arguments, universe/binder details and the actual accepted assumptions. The first own parser attempt split a signature at its inner proof-premise type instead of the final conclusion; its source/log are preserved. A second attempt correctly stopped at the source pin when the author removed the stale pending-kernel comment. Final execution binds the announced successor and changes no candidate bytes.

## Composition and lifting without circularity

`under_antecedent` is two detachments. d47 turns a proved `x → y` into `x → (z → y)`; d46 turns that into `(z → x) → (z → y)`. It uses neither composition nor a deduction theorem.

For the longer composition argument, write `J = (a → b) → b` and `E = a → c`. d35 gives `a → J`; lifting this under `E → a`, followed by Peirce d18, gives `(E → a) → J`. Unrestricted d52 and contraction d22 then yield `(J → E) → E`, the stated `application_contract`. `insert_middle` is just d47 applied to d16. These combine to prove `application_transport`: `(J → c) → (a → c)`.

`repeated_antecedent` removes the outer repeated `a` in `a → b → c → (a → d)`. Its sole additional restricted row uses the reflexive guard `a ≼ a`; d23, d38 and d22 perform the remaining contractions. Finally the explicitly typed `happ` is `J → ((a → b) → ((b → c) → (a → c)))`. Application transport yields its version prefixed by `a`, and repeated-antecedent elimination removes that prefix. Every substitution and MP match in this tail is also included in the independent syntax audit.

All public results discharge the temporary seed with the existing `withSeed` construction: the reflexive restricted instance proves `T (rho8 L a a a a)`. Thus public recovery still needs only `Restricted L T`. `rho8_all` uses d52 with argument order `c,u,a,b`; composition uses the new semantic tail; lifting uses the two-detachment helper. There is no circular use of a public theorem being defined.

## Actual source saving and remaining boundary

The held candidate is **14,739 bytes / 330 lines**, against **19,378 bytes / 381 lines** for the maintained core: a saving of **4,639 bytes and 51 lines** with the public API retained. Including the unchanged 2,680-byte / 73-line adapter, the pair is **17,419 bytes / 403 lines**, down from **22,058 bytes / 454 lines**. This is source-size evidence, not a claim about object size, compile time, a smaller machine, a changed calculus or a new ZFC-consistency endpoint.

The maintained producer synchronization is outside this receipt. Before adoption, it needs exact regeneration of these held bytes and the bounded kernel/API/axiom checks arranged by Root. A later combined checkpoint must retain the current transitive-source invalidation policy. The receipt remains source-only even if another agent subsequently compiles this exact candidate.
