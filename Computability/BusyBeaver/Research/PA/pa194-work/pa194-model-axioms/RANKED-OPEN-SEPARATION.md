# Open separation at seeded axiom nodes

`simRuleSeparation_seededAxiom` proves the numerical compiler's axiom-leaf implication for `sepRoot φ`, assuming only `IsSemiformula SourceL 1 φ` and `SeedAdmission bound reserve e (axm s (sepRoot φ))`. The property may have arbitrary model-valued free variables, including nonstandard codes and parameters. The source model satisfies PRA and IΣ₁. `simRuleSeparation_rankedAxiom` is the corresponding ranked-admission result. The proof derives the free-stack freshness conditions from ranked admission, proves the code of the outer universal constructor exceeds two, and obtains both reserve inequalities from the actual axiom node. Four printed axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`.

This is an open-formula leaf. Foundation theories contain sentences, and this result does not produce universal closure of parameters or its shifted property code. It does not define a theory, construct a compiler, identify PA, prove native iPRA derivability, or establish any consistency implication.

The independent suffix replay exited 0 in `/tmp/pa194-ranked-open-separation-replay-v3.log`. It compiles the three repository source modules `PA194ModelSeparation`, `PA194ModelLowVacuity`, `PA194ModelSeparationAxiom`, and this new source in one output. Source hashes and two selected prebuilt object hashes are checked before and after; the baseline and workspace/package foundations remain prebuilt and their full transitive provenance is not authenticated by those checks. No whole-workspace clean build is claimed. Exact command from the repository root with a fresh output path:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-ranked-open-separation.sh "$PWD" /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-full-one-level-audit /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-ranked-open-separation-replay-v3
```
