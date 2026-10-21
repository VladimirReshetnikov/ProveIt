# Selected fresh K216 replay for root

Use a disposable copy of the extracted K216 package. `{COPY}` below is that copy, `{PARENT}` is the already-accepted extracted K217 package with `machine/sites217.json` and `machine/k217.native.tm`, and `{OUT}` is a new output directory outside both. No submitted wrapper, ancestor verification, or manifest suite is needed. The complete five-command plan and gates are also in `fresh-jobs.json`.

```text
python3 -B {COPY}/code/reconstruct216.py --parent {PARENT} --out {OUT}/rebuilt
python3 -B {COPY}/code/source_equivalence.py --baseline {PARENT}/machine/sites217.json --candidate {COPY}/source/sites216.json --out {OUT}/source
python3 -B {COPY}/code/audit216.py --out {OUT}/blank-marker.json
python3 -B {COPY}/code/check_joint_fold.py --old {COPY}/machine/prefold217.native.tm --new {COPY}/machine/k216.native.tm --keep 164 --drop 183 --radius 4 --fuel 20 --output {OUT}/fold-window.json
python3 -B {COPY}/code/validate_native.py {COPY}/machine/k216.native.tm {COPY}/source/sites216.json {OUT}/runtime
```

Keep exact stdout, stderr, invocation, return status, source/input hashes, and elapsed time for each job. A suggested per-job outer bound is1,200 seconds; the delivered full runtime is331.54 seconds. This is a checker-construction bound, not a bound on machine runtime or register values. Observe progress through nonblocking tool sessions. All assertions must be enabled; do not use `-O` or nonzero `PYTHONOPTIMIZE`.

Require byte-exact reconstructed native/dense/prefold and spaced/compact sources. Require source status `ALL_NATURAL_SOURCE_BISIMULATION_PASS` with6,175 edges and byte-exact deterministic recipe/correspondence against delivered evidence. Require the marker/startup status and fold status with27,527 contexts/48 nontrivial, histogram1→1:27,479 and1→3:48, and rejected corrupt-initial-halt control.

The native driver can exit0 on a recorded failure. Require runtime status `UNIVERSAL_MATHEMATICAL_PASS`,6,176 ordered cases with no failures, all affine duration coefficients nonnegative and positive constant, exact table/source/checker/helper bindings,1,709,992 symbolic rules, minimum constant13, and all432 rows covered by case plus proved-block traces. Require startup status `CALIBRATED_DIRTY_ROOT_SEED`,313,133 steps and exact whole tape/head/state/register/spare match. An independent metadata parser should inspect these gates; do not infer them merely from process return0.

Actual fresh evidence has not been produced by the author of this plan. Root owns execution and publication of any PASS.
