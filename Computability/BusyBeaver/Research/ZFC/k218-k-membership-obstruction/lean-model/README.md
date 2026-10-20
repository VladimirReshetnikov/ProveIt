# Checked native K + RAB + QS nonderivability

[KRABModel.lean](KRABModel.lean) proves that native falsum and code 16 are not
derivable from the exact retained numerical rows, literal gated seed bundle,
K, membership-fourth rho8, MP, theorem-only GEN, and quantified stability.
The valuation and constructor laws cover every natural code.

The [first Lean check](verification.json) passed in 2.430 seconds with 21 axiom
reports, zero warnings and default proof limits. The only reported axioms are
standard Lean `propext`, `Classical.choice`, and `Quot.sound`; no axiom or proof
omission was added. The full [scope and dependency note](checked-result.md)
distinguishes this theorem from an internal PA consistency proof or a new
machine construction. Code 16/all-identities extensions are outside its scope.

The [independent source peer](source-peer.json) read the complete formalization.
The separate [binding and actual-input receipt](binding-and-actual-review.json)
checks the exact six KCode222 transcriptions and accepted Code254 source/object
pair. Only Code254 is imported; KCode222's theorem facade is not. The inherited
cache is an explicit dependency boundary rather than a fresh transitive build.

The algebra and ordinary proof are due to `opening_encoder`; `drop_contract`
authored and executed the Lean formalization; `review_upstream_reflection`
performed its independent source/API review. The original [ordinary proof](../proof.md)
remains unchanged. Root also read the complete new source and actual result.

All actual source/log/result files are retained under [history/attempt1](history/attempt1/).
There was one successful Lean attempt and no failed Lean attempt. Compiled
objects are omitted from Git; their exact hashes remain in the actual record.
The [publication map](publication.json) pins every retained text artifact.

To rerun with the same existing accepted cache and compiler paths available:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-k-membership-obstruction/lean-model/run_lean.py fresh-attempt
```

The named attempt directory must not exist. The runner pins the selected
Code254 source/object and compiler, captures the new log, and enforces
`-j1 -M4096` plus a 120-second process limit. It does not download dependencies,
query versions, rebuild the inherited namespace, or execute any Rocq/Coq code.
The retained [parent record](inputs/accepted-Code254-parent.json) documents
those environment-specific prerequisites; a fresh checkout alone does not
supply the external cached objects.
