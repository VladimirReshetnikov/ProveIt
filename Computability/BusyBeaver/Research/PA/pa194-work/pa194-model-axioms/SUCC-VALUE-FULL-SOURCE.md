# Full-source successor-value transport

`PA194SuccValueFullSource.fullSource_succValue` proves the guarded sequent `¬∃v valBody(s)[v], ∃w valBody(succ s)[w]` for every internally valid arity-zero PAeq term `s`, including nonstandard codes, in every candidate PRA model whose arithmetic reduct satisfies classical IΣ₁. It assumes no naming field and does not assume a value of `s` exists.

The staged sources identify `succTotalCode` exactly with the previously proved standard source sentence asserting domain-successor existence, derive the guarded successor-value implication in any theory where that sentence is provable, and discharge its premise using the existing full-source `domainSuccessorUniversalProof`. The implication depends on the separately source-replayed Σ₁ value-domain factorization and fixed first-order schema.

From the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-succ-value-full-source.sh "$PWD" /dev/shm/pa194-succ-value-full-source-repo
```

The checker recompiles the three modules, requires five clean axiom reports, and rejects `sorryAx`. It retains the separately replayed successor-value implication and the other prebuilt object overlays enumerated in the script, including Foundation. The checker selects the repository-built implication baseline. This is a model-uniform Lean proof, not native iPRA. It does not by itself construct a name from a successor value, discharge `NameFacts.eSucc`, or prove physical-machine synchronization.
