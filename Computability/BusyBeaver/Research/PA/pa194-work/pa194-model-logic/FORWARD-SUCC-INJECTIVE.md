# Forward PAeq successor injectivity

This package proves the actual forward translation of the fixed PAeq successor-injectivity sentence. It opens both successor-value witnesses, applies the separately repository-replayed order-isomorphism cancellation theorem to the two successor outputs, and uses their predecessors as witnesses for the translated equality. Source equality and the closed strict-Separation axiom are discharged by the existing full-source suppliers.

`PA194ForwardSuccInjective.root_succInjective_provable` proves that the full relational source theory derives the exact root-dispatcher image of `succInjective.univCl`, in every candidate PRA + IΣ₁ model and under the root packet code bound. This is a model-level fixed-axiom supplier, including nonstandard arithmetic models. It does not supply arbitrary induction instances, the function-term existential rule, a full guarded compiler, physical synchronization, or a native iPRA implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-forward-succ-injective.sh "$PWD" /dev/shm/pa194-forward-succ-injective-repo-NEW
```

The checker rebuilds fourteen source modules and a ten-report audit, using the repository-replayed canonical unified source syntax, cancellation theorem, translated-equality helpers, and other explicitly listed prebuilt paths. It does not rebuild the full dependency closure. An earlier replay failed because a pre-unification `PA194AtomicPAeq` object was selected alongside the canonical order-isomorphism definitions; this checker gives the unified repository objects precedence and the v2 replay passed.
