# Guarded specialization of translated arithmetic universals

`guarded_tr_all_specialize` specializes an unguarded typed source proof of a translated arithmetic universal to any model-valued free variable and supplies the corresponding domain guard. `guarded_tr_all_specialize_guarded` does the same starting from a guarded source proof, preserving and extending its guard bound. It can therefore be applied repeatedly to nested translated universals.

Both results require the displayed source proof as a hypothesis and apply in candidate-PRA models with an arithmetic IΣ₁ reduct. They do not supply the proof or establish native iPRA or a machine equivalence.

The checker rebuilds this module in a fresh output and verifies the source and direct dependency hashes; transitive dependencies are prebuilt. Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-guarded-universal-elim.sh "$PWD" /dev/shm/pa194-guarded-universal-elim-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
