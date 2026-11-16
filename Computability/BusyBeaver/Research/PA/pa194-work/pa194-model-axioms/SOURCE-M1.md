# Guarded multiplication totality source field

The typed source proof derives guarded, domain-valued output existence for the exact `mulResult` relation. It uses source equality, empty, adjunction and intersection, the typed addition-totality sentence, and the universally closed Separation instance for the negated multiplication-prefix-existence property. The quoted sentence is identified exactly with `tHyp sM1`. The model wrapper discharges those fixed source assumptions, supplying the Separation sentence from generic typed Separation membership and the addition sentence from the checked `a1` source proof. The resulting `PA194MulTotalGuardedSource.m1` is a full-source proof in each candidate PRA model carrying classical IΣ₁, including nonstandard models.

This supplies the single `SourceFacts.m1` field. Other source facts, proof-compiler obligations, native iPRA transfer and physical machine synchronization remain separate.

From the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-m1.sh "$PWD" /dev/shm/pa194-source-m1-repo
```

This incremental checker rebuilds these three sources in one output, rejects `sorryAx`, and checks six axiom reports. The `LEAN_PATH` retains the independently source-replayed multiplication Separation, induction, output, prefix and graph chains, repository-replayed `a1` and recurrence/graph objects, older addition-output/induction objects, and Foundation objects. It is not a fresh rebuild of the entire dependency closure; a separate standalone check of the corresponding addition-output source development passed, but did not establish byte identity with the older objects used here.

A separate [17-module repository-source replay](SOURCE-M1-CHAIN.md) rebuilt the multiplication helper chain and these three final modules in dependency order, passing all declared axiom audits without `sorryAx`. Earlier graph, addition and Foundation dependencies remained prebuilt.
