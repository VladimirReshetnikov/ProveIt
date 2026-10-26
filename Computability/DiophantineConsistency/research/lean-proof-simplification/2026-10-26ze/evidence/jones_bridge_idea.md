# A third structural idea: expose the existing Jones evaluation bridge

Pinned commit: `efa64ca941cdae37bb6f7fc5093ae8bb69296ca3`.

## The residual duplication

`JonesSyntax.lean` proves five private theorems evaluating the derived Jones components of an arbitrary `RingVars (Expr σ)` record:

- `eval_rad`, for the two radicands;
- `eval_wt`, for their separating weights;
- `eval_dvsr`, for the squared divisor;
- `eval_dvnd`, for the squared dividend;
- `eval_marg`, for the inequality margin.

`ExecutableJones.lean` already imports `JonesSyntax`, uses its `evalExprVars` function, then repeats all five proofs. These repeated proofs expand the same nested arithmetic definitions of `U, Y, M, P, K, A, B', W, C, J, Q, D, E, F, Gp, H, I`. They do not inspect how the record was constructed from a seed expression or its coefficients.

That independence is the decisive fact. The established bridge applies equally to the record produced by the executable compiler. The later module need not rebuild it.

## Exact change

Remove `private` from the five existing declarations in `JonesSyntax.lean`, leaving every statement and proof body otherwise untouched. Delete the five later private duplicates. In the existing proof of `ExecutableJones.eval_withInput`, qualify the five rewrite lemmas:

```lean
    JonesSyntax.eval_rad, JonesSyntax.eval_wt, JonesSyntax.eval_dvsr,
    JonesSyntax.eval_dvnd, JonesSyntax.eval_marg, eval_syntaxVars]
```

For example, the old later theorem has the statement

```lean
(v.rad k).eval a = Jones1982.Nine.rad (JonesSyntax.evalExprVars a v) k
```

and is immediately proved by

```lean
JonesSyntax.eval_rad a v k
```

The divisor, dividend, and margin statements differ textually only because the earlier statements write `(fun e : Expr σ => e.eval a) v.dvsr` and analogous expressions. Beta reduction makes them definitionally identical to `v.dvsr.eval a`.

No new abstract interpretation structure is needed. No import is added. No expression constructor, enumeration order, coefficient routine, seed data, or compiler definition changes. Five theorem names become newly public; all existing public statements are retained.

## Maintenance improvement and novelty

The measured candidate removes **49 physical Lean lines**: `JonesSyntax.lean` remains at 179 lines and `ExecutableJones.lean` shrinks from 300 to 251. These are long and fragile rewrite lists over the actual Jones arithmetic components; deleting the second copies reduces the maintenance cost when a derived component changes.

The audit found no proposal of these five semantic bridges in packets a–v. The closest earlier ideas are common scalar ratio tails, generic degree/renaming interfaces, and thematic module boundaries. None supplies these five source-specific evaluation theorems. The novelty claim is therefore the exact hidden interface and its duplicate client, not a general claim that making lemmas public is new.

I also examined `eval_vectorSum`. The available library equivalence and product-sum lemmas can shorten its existing successor calculation slightly, but the improvement is only a few lines and does not justify another proposal here.

## Validation and its limits

`jones.patch` passes `git apply --check` against the pinned snapshot. The five earlier proof bodies are unchanged except for visibility. An extracted-source Lean harness compiles all five promoted proofs and all five aliases with the exact old duplicate statement types. The harness uses the literal original definitions of `RingVars`, the original integer `Jones1982.Nine.Vars` and its components, and `JonesSyntax.evalExprVars`, together with a freshly built pinned `Representation` module. It contains no invented substitute definitions or assumed axioms.

The two upstream data sources, `Diophantine/Paper1982/NineRatio.lean` and `NinePoly.lean`, were fetched at the same pinned commit. Full fetched copies and SHA-256 provenance are included. The compiled alias axiom sets agree with the reused theorems: `[propext, Classical.choice, Quot.sound]` for radicands/weights, and `[propext]` for divisor/dividend/margin.

The harness is **not a complete module rebuild** of `JonesSyntax` or `ExecutableJones`; the larger Hilbert-tenth dependency chain was not replayed. The report must preserve that distinction. Integration should rebuild those two modules and the direct executable-equation client. The exact source edit is proof-only, but full downstream validation remains an integration gate.

## Files

- `structural/jones.patch`
- `structural/candidate/DiophantineConsistency/JonesSyntax.lean`
- `structural/candidate/DiophantineConsistency/ExecutableJones.lean`
- `structural/JonesBridgeHarness.lean`
- `structural/jones-validation.log`
- `structural/jones-metrics.json`
- `structural/jones-provenance.json`
- `structural/jones-dependencies/NineRatio.lean`
- `structural/jones-dependencies/NinePoly.lean`
