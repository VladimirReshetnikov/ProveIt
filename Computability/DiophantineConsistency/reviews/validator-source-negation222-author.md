# Actual C222 source negation: author checkpoint

Author: `/root/circuit_reduction`. The new main/check pair is frozen and
freshly compiled. Independent review and acceptance remain separate.
No existing proof source, vendor file, shared documentation, Git state,
or accepted dependency object was changed.

Final sources, under `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA`:

- `ValidatorSourceNegation222.lean`, 168 lines, SHA256
  `766f589378be9c2bfe583f248b8e2a448945d74114400f46c7d8ed210bbd16b4`;
- `ValidatorSourceNegation222Checks.lean`, 71 lines, SHA256
  `7fd75fe179da81627761d1ad4845bd0bf8c81768e3fd6db1691ae450e1f2afcc`.

## Exact theorem

`encode_neg` applies to every internal typed source code
`IsSemiformula ℒₛₑₜ n p`, with arbitrary internal `F`, `B`, and `s`. It proves
both actual C222 implications between
`encode F B s (Bootstrapping.neg ℒₛₑₜ p)` and
`wim (encode F B s p) 1`. The two projection theorems expose the implications;
`encode_neg_witnesses` exposes numeric internal checker-history witnesses.
There is no freshness, distinct-label, stack-length or standardness premise.
The typed-source premise is retained; malformed zero is explicitly excluded
by a focused check.

The definitions and finite logical helpers are over arbitrary IΣ1 arithmetic
models. The uniform source induction explicitly additionally assumes IΣ2.
Its displayed Π₂ motive universally quantifies `n,F,B,s`; actual CProv is Σ₁,
and the encoder, source negation, and typed-source predicate have the required
actual graph definability. `InductionOnHierarchy.order_induction_sigma 𝚷 2`
and the actual eight-way source-code case theorem handle internally sized
syntax, rather than an induction over externally finite Lean formulas.

The finite code helpers use actual `cProv_classical`, implication composition,
contraposition, double-negation introduction/elimination and ALL monotonicity.
Implication congruence reverses the antecedent direction correctly. The two
connective cases use these small derivations instead of the old expanded
four-variable tautologies. Both quantifier cases invoke the induction
hypothesis at the literal state `(n+1,F,s∷B,s+2)`. They compare the same binder
label on both sides, so neither alpha-renaming nor vacuity is needed.

The single import is the accepted actual `ValidatorFormulaEncoder222`.
The fully read `R2Neg` was a proof guide only; no R2/CProv254 proof is imported.
The equality case uses the same actual Eind atom and its numeric negation;
it does not identify Eind with primitive `weq`. This packet supplies no source
axiom images, tagged seed interpretation, complete source-proof translation,
closed ZF-to-C222 reduction or final HA equivalence. Classical C222 proof
rules are not additional axioms of the separate HA derivation calculus.

Focused checks cover equality with colliding labels, membership with fallback
labels, a negated equality, truth/falsity, double source negation, alternating
nested quantifiers and their literal encoder-state updates, and malformed
zero. Two purely syntactic checks explicitly omit the unnecessary IΣ2
section hypothesis.

## Cache, execution and provenance

The approved plan/pins remain frozen at
`research/validator-source-negation222-plan.md` / `.json`, SHA256
`18fe20b1b5087f6ac250a98b5bd56b9df2a7fd477f5e5867e5964e7d0c442993` /
`418971e7da7efeec1e02402bf692b14e975bfa1826ccce3675bc722692ded5f9`.
The execution inventory is `reviews/validator-source-negation222-cache.json`,
SHA256 `fb33ff9c1bf83ca829d82958beadb725e3db1a347878caac2ab1a98e55fc4fae`.

All 152 cached current-source modules, 117 Foundation modules, 503 artifacts,
and 40 explicit external boundaries were reauthenticated before execution.
The header parser includes `public meta import Aesop`; this corrects the
earlier Context inventory's boundary omission without modifying that frozen
packet. The added Aesop primary is pinned to the accepted Enum proof-word
provider. The selected encoder/syntax prerequisite objects are the accepted
root-fresh objects. No pending Context object is imported. This is reuse of
authenticated dependencies, not a fresh Foundation/dependency replay.

Only the new pair was compiled in
`/tmp/validator-source-negation222-author-ysq05w0b/lib`. Commands used Lean4.32,
`-M6000 -j1 -DElab.async=false`, one Lean thread, no `LEAN_SRC_PATH`, regular
non-symlink outputs, and the 512 MiB disk reserve guard. Sources and drivers
were completely read before execution. Final main/check runs passed in
5.918 / 3.103 seconds, with an empty main log and no warnings. All 16 axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`.

Final object hashes:

- main `6155f06b7f9809a19ca7aec04c4f813fd69f58a41dc88e1a9a547f35eac6f119`;
- checks `aa98d0b79ce994484b5e4250522a269e17fa753016cc65040148d8ca89257c29`.

The final replay has 2,111 pre/post pin observations plus the retained 709
read-only planning observations. Summary
`reviews/validator-source-negation222-replay.json` has SHA256
`cfb206112f8eb04f4a104a7313b8ef51cb566bb82509518f731d78accd81351e`.
The 27-file manifest `reviews/validator-source-negation222-author-replay/FILES.json`
has SHA256 `70c7319c28aab8df8b6ebb065a7d3ad017a599266bd4d5dc658e64b3fba57920`.

The main passed on its first attempt and remained unchanged. Initial checks
left three concrete relation-symbol recognizer goals unsolved; explicit
unfolding of `Language.IsRel`, `Language.isRel`, and the actual set-language
instance solved them. Two unused-IΣ2 warnings were removed with `omit`.
The failed check draft, diagnostics (including failed-declaration sorryAx
reports), all driver/source snapshots, timing/pin records and prior main
object are retained. None of those failed declarations is accepted in the
final clean object or final axiom reports.
