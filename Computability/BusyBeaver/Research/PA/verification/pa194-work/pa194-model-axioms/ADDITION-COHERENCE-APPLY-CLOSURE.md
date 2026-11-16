# Single-output addition-coherence helper/application replay

The four modules rebuild typed coherence syntax, specialization/shift, the conditional frame, and the stronger global-statement application in one output directory. The application assumes the global coherence proof and does not assume output domains; the global statement and SourceFacts.a2 are not proved here. The application source uses only the Rules and ordinal-induction Schema imports, reducing the dependency closure compared with the earlier scratch version.

The check is pinned to its direct source/object inputs. The addition and ordinal imports include older staged objects and will need repository source closure verification. Stack is enlarged and core files disabled to diagnose earlier Lean exit-139 crashes.

From the repository root, with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-addition-coherence-apply-closure.sh "$PWD" /dev/shm/pa194-add-coherence-apply-closure-repo
```
