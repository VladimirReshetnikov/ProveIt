# Foundation universal closure: independent review

The controller-certificate agent independently read all 67 main lines and
38 check lines of the root-authored `FoundationHAClosure` packet, the complete
author receipt, the syntax interpreter, the existing GG translation, and the
specific source closure/rewriting and HA universal-introduction dependencies.
No mathematical or source-binding issue was found. The reviewer did not author
these leaves or the imported Foundation/HA syntax and deduction modules.
Earlier independent reviews of several HA prerequisites are not represented
as fresh compilation of those prerequisites here.

The exact source closure is preserved: `univCl` applies `fixitr` at `fvSup`,
universal closure, then `toEmpty`. The proof first transports the existing GG
translation through the actual embedding and rewriting identities. Its new
`formula_fixitr` establishes equality of the two canonical target variable
environments: source free index `x < m` becomes bound target index `x`, while
`x ≥ m` becomes free target index `m + (x - m) = x`. There are no original
bound variables in this lemma. Thus arbitrary `m`, including zero and counts
below the source free-variable bound, is legitimate. Nested binders are handled
by the previously proved capture-avoiding `formulaAux_rew`, not by an assumed
substitution identity.

The all-closure inductions use the actual successor convention on both syntax
representations. Consequently `sentence_univCl` has exactly the claimed
`closeN φ.fvSup (formula φᴺ)` result. `proves_univCl` takes an actual proof of
the open translated body and applies the existing HA reclosure constructor.
That constructor preserves a finite list of arithmetic axioms because they
are sentences; its universal rule shifts the context explicitly. It supplies
no arbitrary body proof, excluded-middle rule, or unrestricted DNE. The
focused sparse-index, partial-closure, nested-binder and closed-reflexivity
checks are consistent with those contracts.

Frozen source SHA256s:

- Main: `593d4672ff5a2bfead2f8771a1b94273319f441e84732df57229cb11447e8b31`.
- Checks: `c1ce4c4ca55750971392ad2dc7bb308ad0f93e51e8d9c50da64189b93f4d467f`.

Both leaves were independently compiled into the initially absent target
paths of `/tmp/foundation-ha-closure-controller-peer-os1z53ls/lib`, using
Lean 4.32.0, `-M6000 -j1 -DElab.async=false`, and an isolated `LEAN_PATH`.
Both passed, with an empty main log. The fresh objects are byte-identical to
the author's: `233f1a4a4b4bb29791e58dbc838cb668a64161940c5f2b12412a90b33464b2c6`
and `2dc273bf3644a046e80b9848bdbfb96f9638badc68a60bd5f07645bcb0a770f4`.
The two runs took 1.71 and 1.80 seconds; peak resident memory was 1,755,684 KiB.

All six reports were inspected. `doubleNegation_allClosure` uses no axioms;
the two interpretation lemmas use only `propext` and `Quot.sound`; the full
source-closure identity, HA reclosure binding, and reflexivity example also
report `Classical.choice`. That is an existing metatheoretic dependency of
the source closure/embedding construction, not a new rule of `HA.Derives`.
No `sorryAx` or nonstandard axiom appears.

The accepted author's aggregate metadata
`foundation-ha-closure-dependency-replay.json` was pinned at
`88cf1f0983335cd29fafcc99fbaea13a6c39033e4d822d9885f81e23aae1bfbe`.
The complete 88-module cached inventory, its 491 source/cache/trace/object/
prior observations, compiler/package identities, frozen sources/author
objects, and 14 durable author-bundle files were checked before execution
and after each invocation. Only these two leaves were rebuilt; the parent
arithmetic packet and Foundation/package closure were reused. The inherited
external-package boundary is not upgraded to a new transitive attestation.
The author's two failed development invocations remain separate and are not
counted as accepted proofs. No frozen source or shared object was modified.

Commands, full logs and timing text, all inherited pins, object comparisons,
source snapshots and the peer driver hash are retained in
`foundation-ha-closure-peer-replay.json`, SHA256
`31d9713beb716e544ff3041cd9e69b6ce38f7d4752a929edb9559b9efcb28546`.
This closes the exact parameter-closure transport only. It does not prove
the remaining arithmetic axiom/induction images or the final HA consistency
equivalence.
