# Recovering and checking batch199

Use standard-library Python from the repository root. This restores all 403
members from the three arrival commits without executing any supplied code:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake199.py /tmp/k215-batch199
```

The packet roots are:

* `/tmp/k215-batch199/K215_Composed_Selector/K215_Composed_Selector_2026-10-20`
* `/tmp/k215-batch199/K216_Rho6_Permutation_2026-10-21/K216_Rho6_Permutation_2026-10-21`
* `/tmp/k215-batch199/K215_Construction_and_Research_2026-10-21/K215_Construction_and_Research_2026-10-21`

Placement `ed175ba03d` retired the ZIPs. The
[placement map](data/intake199-placement.json) identifies all 207 new files,
156 current aliases,13 batch aliases,7 historical aliases and 20 archive-only
members, including the complete main articles and their inputs. Absent
historical helper names are documented in the source dossiers, not fabricated.

## Inspect saved results without running candidates

Source 162's published evidence already contains all logs, fresh runtime,
startup, reconstructed artifacts and original unchanged actual record.
Prepare its 26 selected inputs from the pristine packet and three pinned
repository parent files, then run root's own read-only auditor:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source162/prepare_saved.py --packet /tmp/k215-batch199/K215_Composed_Selector/K215_Composed_Selector_2026-10-20 --output /tmp/k215-batch199-saved
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source162/review_saved.py --run /tmp/k215-batch199-saved --source164 /tmp/k215-batch199/K215_Construction_and_Research_2026-10-21/K215_Construction_and_Research_2026-10-21 --comparison SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake199-source164/comparison162.json --output /tmp/k215-batch199-saved-review.json
```

Expected statuses: `EXACT_SOURCE162_SAVED_VIEW_PREPARED` and
`PASS_ROOT_INDEPENDENT_SOURCE162_ACTUAL_AND164_TRANSFER`. The second checks
every stored blank event and whole-frame support against native/dense tables,
every case guard/row/duration, all source effects and edges, and the exact164
transfer. It imports no supplied checker and reruns no candidate. These
portable invocations were replayed successfully after publication.

The Source 163/164 saved output/capture readers also work after relocation:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source163/audit_fresh.py --actual SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake199-source163/fresh1 --output /tmp/k215-batch199-saved163.json
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source164/review_saved.py --run SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake199-source164 --packet /tmp/k215-batch199/K215_Construction_and_Research_2026-10-21/K215_Construction_and_Research_2026-10-21 --output /tmp/k215-batch199-saved164.json
```

They expect `FOUR_FRESH_OUTPUTS_AND_CAPTURE_CHAIN_REVIEW_PASS` and
`PASS_INDEPENDENT_SAVED_SEMANTIC_AUDIT`. Their authors also executed those
finite leaves; they are own saved-output checks, not second-agent executions.
Root replayed them unchanged. Source 164's earlier path-bound auditor and
the corrected dossier wording remain preserved under history.

## Fresh selected executions

The portable Source 162 runner needs the packet plus three exact parent
files already published in the repository. Keep it beside
`fresh-inputs.json`, and choose a nonexistent output directory:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source162/run_fresh.py --packet /tmp/k215-batch199/K215_Composed_Selector/K215_Composed_Selector_2026-10-20 --parent-table Computability/BusyBeaver/Research/ZFC/candidate-k216/k216.native.tm --parent-source Computability/BusyBeaver/Research/ZFC/candidate-k216/sites216.json --reference-source Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/sites216.json --out /tmp/k215-batch199-fresh162
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source163/run_selected.py --package /tmp/k215-batch199/K216_Rho6_Permutation_2026-10-21/K216_Rho6_Permutation_2026-10-21 --output /tmp/k215-batch199-fresh163
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake199-source164/run.py --packet /tmp/k215-batch199/K215_Construction_and_Research_2026-10-21/K215_Construction_and_Research_2026-10-21 --output /tmp/k215-batch199-fresh164
```

Source 162 runs seven reviewed leaves, with caps30/30/30/10/10/360/30 seconds.
Its complete runtime proves 6,176 cases/1,698,790 symbolic rules/all 430 rows/
minimum 6, and the exact blank trace takes 95,726 steps. All26 inputs stay
unchanged; fresh case/startup gzip bytes match the supplied files. The
source-identical430-row bijection transfers this proof to 164. Detailed
[runner scope](data/intake199-source162/review/fresh-reproduction.md).

Source 163 runs four finite leaves with 120-second caps, capturing every packet
file before/after and checking only declared output changes. It does not
repeat the old 216 full runtime. [Detailed scope](intake199-source163-reproduction.md).

Source 164 runs seven finite leaves with 60-second caps and 29 selected input
captures: reconstruction, two projection audits, context matrix, raw lift,
residual interface and reached-frame scanner witness. It does not repeat162's
runtime or blank start. [Detailed scope](intake199-source164-reproduction.md).

All interpreters keep assertions enabled; failures retain logs and stop the
runner. No submitted wrapper, manifest validation, ancestor suite, broad
search, C++ build or proof assistant belongs to these selections. The
separately retained rho6-on215 allocator invocation is a bounded research
measurement with a historical solver environment; its reproduction note
does not advertise that command as portable or as an accepted machine proof.
