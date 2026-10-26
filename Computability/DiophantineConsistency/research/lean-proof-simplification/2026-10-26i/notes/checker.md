# Two additional proof simplifications: checker and computability layer

Snapshot: `e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11`.
Both mechanisms were checked against the incoming 2026-10-26 report and the earlier relocated `research/lean-proof-simplification-20261026` packet by the independent novelty audit. Neither is in those packets. Novelty here means new relative to that audited proposal set, not a claim that product invariants or `fun_prop` are new mathematics.

## 1. One exact decoder graph, rather than two independent success inductions

**Source target.** `Lean/DiophantineConsistency/AnnotatedProofCode.lean`, lines 78-132 (`decoded_depth_le`, `quote_of_decode`); lines 139-147 (`decode_quote_iff`). The two success proofs split on fuel, input code, first unpaired component, left recursive decode and right recursive decode in almost exactly the same order. Each theorem knows only one projection of the useful invariant.

**Stronger invariant.** Prove the following once, by induction on fuel, for every natural code, including malformed codes:

```
decode fuel code = some t → t.quote = code ∧ t.depth ≤ fuel
```

Both original results are its projections. Retain the existing independent completeness induction `decode_quote`. Together they give the exact graph:

```
decode fuel code = some t ↔ t.quote = code ∧ t.depth ≤ fuel
```

The old `decode_quote_iff` was restricted to input `t.quote`; this new lemma is quantified over arbitrary `code`. It does not infer that every natural code has a parse, and does not replace malformed-input coverage with quotation-only reasoning.

**The less-obvious local reduction.** In the fork case, expose the nested `Option.bind` term with `change`, then use `Option.bind_eq_some_iff` twice. Successful parsing already proves that both children succeeded. Destructing two success witnesses is enough; explicit impossible `none` branches disappear. The induction hypotheses now supply both child quote equalities and both depth inequalities. `Nat.pair_unpair` reconstructs the original input, and the two inequalities imply the maximum-depth inequality.

**Checked source reduction.** The API-preserving `decoder-graph.patch` changes only theorem code, keeps every existing declaration, and adds `decoded_spec` plus `decode_eq_some_iff`. Full module: **461 → 439 lines**, net **22 fewer lines**. Changed declaration blocks: **66 → 44 physical lines**; nonblank lines **63 → 39**. These totals include the stronger theorem and compatibility projections; they do not hide new helper overhead in another file. Byte-for-byte executable definitions are unchanged.

**Validation boundary.** `DecoderGraph.lean` contains the complete original `Tree` submodule with this patch applied, under its original namespace, and compiles with Lean 4.32.0. Thus the actual definitions and every original Tree theorem were checked together. The enclosing module imports the large proof-checker development; that full import closure and downstream project were not rebuilt. `AnnotatedProofCode.proposed.lean` is a complete reviewable replacement file, while the patch is the concise intended deliverable. Printed axioms are only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.

**Why it is additional.** The older packets suggest list lookup lemmas, history folds, scanner simulations, and finite table assembly. Those are about list-state iteration. This proposal compresses the inverse theorem and exact fuel domain of the recursive tree decoder. It leaves scanner architecture and list lookup code alone.

## 2. Register primitive recursiveness as a compositional function property

**Source target.** `Lean/DiophantineConsistency/Computability.lean`, lines 92-166. `pr_rho2`, `pr_rho3`, `pr_rho4`, `pr_rho5`, `pr_growG`, `pr_clos`, and `pr_axStack` manually repeat the syntactic structure of the very formula expressions being proved primitive recursive. For example, the axiom stack has a nine-line nested `.comp`/`.pair` proof, including a final definitional equality cast.

**Mechanism.** Mathlib's existing `fun_prop` tactic supports user-registered function properties. Register `Primrec`, the identity/constant/composition/product rules, and a compact library of arithmetic constructor rules. Then the theorem statement and the function definition determine the composition proof:

```
theorem clos_rule ... : Primrec (fun v => clos P (a v) (b v) (c v) (d v)) := by
  unfold clos
  fun_prop (disch := assumption)
```

The prototype treats the pairing `P` parametrically with `hP : Primrec₂ P`, exactly the proposition already supplied by upstream `pr_P`. Consequently it does not assume square pairing is the original Cantor pairing. Constructor definitions retain the upstream bodies with `P` made explicit. This is proof-producing automation, not an evaluator or a replacement compiler.

**A practical interface detail.** Do not simply tag `Primrec.nat_add` or an upstream `Primrec₂` lemma as if it were a `Primrec` rule. Their declared head is `Primrec₂`; the direct-registration experiment did not solve `Primrec` goals. The tested module uses compositional adapters with conclusion `Primrec (fun v => ...)`. In the axiom-stack client, the local pairing hypothesis is put into uncurried `Primrec` form by:

```
change Primrec (fun p : Nat × Nat => P p.1 p.2) at hP
```

After that, `unfold axStack; fun_prop (disch := assumption)` handles the entire expression. For application inside the repository, similarly expose the existing base primitives under an uncurried/compositional adapter and retain their old declarations for existing clients.

**What has actually been checked.** `PrimrecFunProp.lean` compiles proofs for rho1, rho2, rho3, rho4, rho5, rho6, rho8, growG, req, clos, axStack, and a nested product-input client. The four printed axiom lists are standard Lean logical axioms only; no `sorryAx`. This module does not import or replace the repository's complete `Computability.lean`; it proves generic versions of these composition facts against the pinned Mathlib.

**Cost accounting.** The proof bodies for the tested generic clos and rho2 clients are two lines each; axStack uses three lines including the local pairing conversion. Upstream corresponding bodies occupy five, five, and nine lines. These are local client reductions, not a net whole-module saving. The prototype also has 6 constructor adapters (wim, wel, wal, weq, wn, wex), two general arithmetic rules, and property registrations. Therefore no net repository line reduction or compilation-speed improvement is claimed for this proposal. Its main benefit is eliminating repeated manual construction of expression-shaped proofs, which scales across additional clients; retain explicit recursion/termination proofs and measure the complete migrated module before advertising a net size result.

**Why it is additional.** The preceding reports discuss recursor congruence for `Realizes`, PR scanner programs with varying seeds, and explicit program optimizers. This proposal acts on extensional `Primrec` propositions already present in `Computability.lean`; it leaves the actual program syntax, realization certificates, node counts, and machine source unchanged.

## Replay

Use the repository's pinned `lean-toolchain` and `lake-manifest.json` and run:

```
lake env lean /absolute/path/to/DecoderGraph.lean
lake env lean /absolute/path/to/PrimrecFunProp.lean
```

Lean: 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`. Validation logs, measured decoder metrics, SHA-256 hashes and the explicit partial-build boundary are in `validation.json`.

## Primary source links

- https://github.com/VladimirReshetnikov/ProveIt/blob/e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedProofCode.lean#L78-L155
- https://github.com/VladimirReshetnikov/ProveIt/blob/e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11/Computability/DiophantineConsistency/Lean/DiophantineConsistency/Computability.lean#L92-L166
- https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Tactic/FunProp.lean (documented registration contract)
- https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Computability/Primrec/Basic.lean (existing primitive-recursive closure rules)
