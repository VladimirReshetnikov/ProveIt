# Conditional transport from PA refutation to scheduler halting

`PA194RemainingFixedSupplier.tr_closed_quote` identifies the compiler's
translation of a closed standard formula with the quoted standard translation
used by the guarded interpretation. `remaining_fixed_supplier` supplies the
four remaining fixed axioms from `SourceFacts` and the two explicit source
recursion proofs `tHyp sA3` and `tHyp sM3`, after discharging the guards.

`PA194FullSourceRefutationReduction.refutation_of_source_facts` combines those
axioms with term naming, source domain inhabitation and the ordinal induction
supplier. `PA194PARefutationScheduler.scheduler_halts_of_pa_refutation` then
takes an internally coded Foundation PA refutation to a halting clock for the
modeled command scheduler. In every candidate PRA model whose arithmetic
reduct satisfies IΣ₁, the remaining source premises are `SourceFacts` and
those two recursion clauses. This is one conditional direction for the
scheduler. It does not yet connect that clock to a halt of the literal dense
machine, or prove a consistency implication in iPRA.

From the repository root, with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-refutation-to-scheduler.sh \
  "$PWD" /dev/shm/pa194-refutation-to-scheduler-repo
```

The incremental replay rebuilds four prerequisite arithmetic-syntax modules,
the upstream induction supplier and ordinal induction link, and the three
new modules in a single output. It checks the axiom reports for `sorryAx` and
pins the directly imported staged objects. Further transitive project and
Foundation objects remain prebuilt; this is not a complete source-closure
rebuild.
