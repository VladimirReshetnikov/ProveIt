# Joint calibrated binder and CB1 scheduler check

Status: no physical allocation in the inherited protected-row model. This is a synthesis-model result, not a lower bound or a rejected concrete machine.

The source is formed by taking the entire left root subtree of the calibrated CB1 scheduler and the entire right root subtree of the calibrated binder variant. The changed regions are disjoint. Thus this combines two previously justified transformations without changing either local constructor word.

| Binder | DAG nodes | Primitive leaves | Maximum depth | Maximum zero run |
|---|---:|---:|---:|---:|
| 4P+2 (G_Q) | 202 | 4,753 | 47 | 6 |
| 4P (G_I) | 203 | 4,751 | 47 | 6 |

Each source was allocated against both `q13_cb215.native.tm` and `q13_normal215.native.tm`. All four mixed-integer allocation models were infeasible. The solver used the inherited protected-row classification and contextual helper protections. Each run had a 20-second solver limit but returned an infeasibility result in about 6–10 milliseconds. The source change removes state13's decoder role; the retained runtime constraints on that state's rows prevent it from supplying an extra compatible allocation domain here.

Place this directory under `source-search/`, beside the shared source utilities and `frozen_engine_rows219.json`. Run `python3 replay_joint.py` for a standard-library source reconstruction and count check. Run `python3 replay_joint.py --allocate` for the four allocation reruns (NumPy and SciPy required); new receipts go into a fresh temporary directory and do not replace frozen receipts.

`allocate_joint.py` changes only baseline selection and provenance checks from the existing protected allocator, with paths adapted for portability. The frozen receipts retain the original run's absolute input-path labels and original code hash; their content hashes identify the exact baseline inputs. No table was produced, so no primitive-runtime or blank-startup verification is claimed for the mixed sources.
