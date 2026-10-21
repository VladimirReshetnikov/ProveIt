# Guarded proof hierarchy for dominated rho8

The [35,185-byte Lean proof](source/DomRho8.lean) passes an isolated kernel check and five typed API clients. It replaces the current629-node expanded proof with **61 small bootstrap lemmas,81 reusable guarded lemmas, and a short deduction theorem**. The source is72.55% smaller than the128,177-byte predecessor and contains no valuation term DAG. This measures proof-source size; it makes no global minimality or total repository-size claim.

The exact arbitrary-natural-code theorem and `DomImp`, `le_l`, `le_r`, `sub` API are unchanged. There is no ZFC premise, decoding or implication-injectivity assumption. The isolated check is complete; canonical adoption and the affected endpoint closure are separate steps.

## Why the hierarchy is smaller

Source149 established identity, K, Peirce and the transport lemma

```text
(a → b) → (((a → c) → a) → b)
```

in original nodes0–60. Its remaining producer expanded CD230 proof templates at each use to discharge numerical bounds. We instead retain each template as a universally quantified theorem, stating any residual dominance bound as an explicit hypothesis.

Only ten of the original107 templates need a bound, each with one hypothesis. Removing unused templates leaves81, eight guarded. Instantiation discharges bounds using only reflexivity, `0 ≤ x`, and the facts that an implication code dominates its two arguments. Composition and S have no remaining bounds. The Lean kernel checks every such use; the Python guard propagation is untrusted.

After proving K and S, the private deduction theorem is an ordinary induction on finite derivations. Under assumptions `(c→u)→a` and `a→c`, a further assumption `c→u` yields `c`; discharge it, apply Peirce, and discharge the two original assumptions and unused `b`. This proves the exact unrestricted rho8 row. Deduction is not used circularly to bootstrap S.

The bootstrap now binds native Nat parameters directly. Its largest conclusion has27 syntax nodes, so shared valuation-term declarations add complexity without helping this small prefix. Consequent renaming in `mp_substitution` is reconstructed exactly, and variables absent from the conclusion are instantiated by truth0. The only normalization is the proved `wim 0 0 = 0` identity.

## Checks and provenance

- [Final isolated check](actual/run4/result.json):9.5866seconds, exit0, zero warnings. The [log](actual/run4/compiler.log) has four reports, each exactly `[propext, Quot.sound]`.
- The [five typed clients](source/API.lean) are appended to the exact proof in the [checked snapshot](actual/run4/PlainWithAudit.lean). They check the original API and expanded numerical target.
- [Independent source/API review](peers/source-api/review.json) reads the complete614-line proof and compares every61/81 conclusion with its pinned input. It does not rerun the compiler or claim a fresh endpoint closure.
- [Narrow bootstrap-producer review](peers/plain-bootstrap-source-peer.json) checks the substitution, consequent renaming and truth0 filler handling. The [production generator review](peers/generator-review.json) independently checks the complete renderer, CLI and saved seven-mode controls.
- [Renderer reproduction](reproduction/run2/result.json) checks five modes and two invalid-mode controls. Its default generated source plus the five clients is byte-identical to the kernel snapshot.
- [Summary](summary.json) records exact pins, counts and the explicitly bounded scope.

The immutable inputs remain [Source149's full certificate](../../../../../lean217/dominated_rho8_full_certificate.json) and its [pinned CD230 templates](../../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/149-dom-theory-ev-CD230.v). Their SHA256 values are respectively `3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452` and `c788460c8dd0f4dda4440cae4595d73723223b385825d18df2bf94b52764d087`. Original template and certificate attribution is retained; guarded reuse, the direct bootstrap renderer and proof organization are repository follow-up work.

## Reproduction

The [production generator](code/generate_domrho8_lean.py) defaults to this hierarchy for the exact original Source149 input. From this directory, an explicit portable invocation is:

```sh
python3 code/generate_domrho8_lean.py \
  ../../../../../lean217/dominated_rho8_full_certificate.json /tmp/DomRho8.guarded.lean \
  --templates ../../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/149-dom-theory-ev-CD230.v
```

The generator expects a repository-relative template location when `--templates` is omitted. An explicit `--plan` retains the629-node route; `--no-plan` retains the674-node greedy route; unmatched certificate inputs retain generic rendering. `--templates` is rejected with either plan option or a different certificate. No solver is required.

The historical checker and reproduction drivers retain their original absolute paths. They are evidence of the recorded invocations; use the production generator above for portable generation and the maintained serial Lean build driver for proof compilation.

## Preserved failures and limits

Run1 failed because a `rho8` wrapper needed explicit unfolding. Run2 checked composition and S but failed one list-membership constructor in the final deduction proof; its `sorryAx` final report is excluded. [Run3](actual/run3/result.json) then passed the full theorem with the larger valuation bootstrap. The first production replay failed before creating a proof source because its default repository-root path was one directory too shallow; the failed generator, stderr and correction history remain. None of these failures is overwritten or counted as a successful check.

No ATP or solver run, new machine statement, table change, runtime replay, Rocq result or full endpoint rebuild is claimed by this packet. Root's phase2 sources stayed frozen throughout this experiment.
