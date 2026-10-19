# Reproducing the combined 243-state machine

Use Python 3.12 with assertions enabled. All work runs on a fresh external copy
and uses the standard library. From the repository root, recover the source 71
package to restore the inherited runtime checker and its original paths:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_167.py --repo "$PWD" --output /tmp/rotation244-recovered
```

Then run the portable helper:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/candidate-combined243/provenance/reproduce_combined243.py --reference /tmp/rotation244-recovered/zfc244-loop-rotation-20261018/reference/baseline245 --output /tmp/combined243-quick
```

It copies the exact five machine/source artifacts, three adapters and 291
reference inputs. It checks blank initialization, all 8,390 affine cases and
all 8,390 finite literal fixtures. Its [actual packaging check](evidence/portable-quick/verification.json)
passes, reproducing 407,967 startup transitions and 6,473,394 literal transitions.
The original input files and their copied counterparts remain unchanged.

Add `--expanded` and choose a different fresh output directory to run the
complete expanded symbolic replay as well. Each quick stage has a 120-second
process-group limit; expanded replay has 600 seconds. A timeout preserves logs
and reports an unfinished check. The complete [original expanded run](evidence/expanded-verification.json)
passed 8,390 cases and 2,314,868 rules in 509.285 seconds. The packaging check
did not repeat that expensive stage.

Recovery reads the committed archive; the runtime helper uses the reviewed
substantive checkers directly. It performs no dependency installation or proof
compilation. These Python checks and the separately checked
[relative Lean theorem](../combined243_simulation.md) have distinct scopes;
the full 243-state Lean consistency endpoint and internal PA proof remain open.
